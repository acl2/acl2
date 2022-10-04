; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

(include-book "svtv-fsm-ideal")
(include-book "svtv-stobj-export")
(include-book "cycle-probe")
(include-book "centaur/fgl/def-fgl-thm" :dir :system)
(include-book "centaur/misc/starlogic" :dir :system)
(include-book "centaur/meta/variable-free" :dir :system)
(local (include-book "../svex/alist-thms"))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (include-book "centaur/bitops/floor-mod" :dir :system))
(local (in-theory (disable mod floor ceiling)))

(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable acl2::alist-keys-member-hons-assoc-equal)))


(defcong svex-envlists-similar svex-envlists-similar (svtv-name-lhs-map-eval-list map envs) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))


(encapsulate nil
  (local (defthm svex-alist-eval-equiv!-redef
           (Equal (svex-alist-eval-equiv! x y)
                  (and (svex-alist-eval-equiv x y)
                       (equal (svex-alist-keys x) (svex-alist-keys y))))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv!-when-svex-alist-eval-equiv)))))

  (defthm cycle-fsm-of-svtv-data-obj
    (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                  (svtv-data-obj->cycle-fsm-validp x)
                  (svtv-data-obj->flatten-validp x))
             (b* (((svtv-data-obj x))
                  ((base-fsm x.phase-fsm))
                  ((base-fsm x.cycle-fsm)))
               (base-fsm-eval-equiv x.cycle-fsm
                                    (base-fsm-to-cycle x.cycle-phases x.phase-fsm nil))))
    :hints (("goal" :in-theory (e/d (base-fsm-eval-equiv
                                     base-fsm-to-cycle)))
            (and stable-under-simplificationp
                 `(:expand ((:with svex-alist-eval-equiv-in-terms-of-envs-equivalent
                             ,(car (last clause)))))))))


(defthm svex-alist-keys-values-of-base-fsm-to-cycle
  (implies (svtv-cyclephaselist-has-outputs-captured phases)
           (equal (svex-alist-keys (base-fsm->values (base-fsm-to-cycle phases fsm simp)))
                  (svex-alist-keys (base-fsm->values fsm))))
  :hints(("Goal" :in-theory (enable base-fsm-to-cycle))))


(defthm values-of-base-fsm-to-cycle-under-svex-alist-same-keys
  (implies (svtv-cyclephaselist-has-outputs-captured phases)
           (svex-alist-same-keys (base-fsm->values (base-fsm-to-cycle phases fsm simp))
                                 (base-fsm->values fsm)))
  :hints(("Goal" :in-theory (enable svex-alist-same-keys))))


(define svtv-cycle-step-fsm-input-subst ((ins svex-alist-p)
                                         (phase svtv-cyclephase-p))
  :returns (in-subst svex-alist-p)
  (b* (((svtv-cyclephase phase)))
    (if phase.inputs-free
        (append (svex-env-to-subst phase.constants) (svex-alist-fix ins))
      (svex-env-to-subst phase.constants)))
  ///
  (defret svex-alist-eval-of-<fn>
    (equal (svex-alist-eval in-subst env)
           (svtv-cycle-step-fsm-inputs (svex-alist-eval ins env) phase))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-fsm-inputs)))))


(define svtv-cycle-fsm-input-substs ((ins svex-alist-p)
                                     (phases svtv-cyclephaselist-p))
  :returns (in-substs svex-alistlist-p)
  (if (atom phases)
      nil
    (cons (svtv-cycle-step-fsm-input-subst ins (car phases))
          (svtv-cycle-fsm-input-substs ins (cdr phases))))
  ///
  (defret svex-alistlist-eval-of-<fn>
    (equal (svex-alistlist-eval in-substs env)
           (svtv-cycle-fsm-inputs (svex-alist-eval ins env) phases))
    :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs)))))


(defthm svtv-cycle-output-phase-iff-has-outputs-captured
  (iff (svtv-cycle-output-phase phases)
       (svtv-cyclephaselist-has-outputs-captured phases))
  :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                    svtv-cyclephaselist-has-outputs-captured))))


(defsection svex-alist-invert

  ;; For reconstructing pipeline inputs from FSM inputs, it's useful to be able
  ;; to invert an svex alist whose expressions only contain variables and
  ;; constants -- i.e. map the variables in the values to the corresponding
  ;; keys.  This isn't exact wrt variables used more than once.
  
  (define svex-alist-quote/var-p ((x svex-alist-p))
    (if (atom x)
        t
      (and (or (not (mbt (and (consp (car x))
                              (svar-p (caar x)))))
               (not (svex-case (cdar x) :call)))
           (svex-alist-quote/var-p (Cdr x))))
    ///
    (local (in-theory (enable svex-alist-fix))))

  (define svex-alist-var-rlookup ((v svar-p) (x svex-alist-p))
    :returns (key (iff (svar-p key) key))
    (if (atom x)
        nil
      (if (and (mbt (and (consp (car x))
                         (svar-p (caar x))))
               (svex-case (cdar x) :var)
               (equal (svar-fix v) (svex-var->name (cdar x))))
          (caar x)
        (svex-alist-var-rlookup v (cdr x))))
    ///
    ;; (local (in-theory (disable acl2::consp-under-iff-when-true-listp
    ;;                            acl2::consp-of-car-when-alistp
    ;;                            ryl::consp-when-member-equal-of-mod-uops-map-p
    ;;                            ryl::consp-when-member-equal-of-mod-owner-map-p
    ;;                            svar-p-when-member-equal-of-svarlist-p
    ;;                            svarlist-p-when-subsetp-equal)))
    (local (in-theory (disable (:d svex-alist-var-rlookup))))
    (defret lookup-of-<fn>
      (implies (and key
                    (no-duplicatesp-equal (svex-alist-keys x)))
               (equal (svex-lookup key x) (svex-var v)))
      :hints(("Goal" :in-theory (enable svex-lookup-of-cons)
              :induct <call>
              :expand ((svex-alist-keys x)
                       <call>))))

    (local (defthm sfix-of-singleton
             (Equal (sfix (list x))
                    (list x))
             :hints(("Goal" :in-theory (enable sfix empty setp)))))
  
    (defret <fn>-under-iff-when-quote/var-p
      (implies (svex-alist-quote/var-p x)
               (iff (svex-alist-var-rlookup v x)
                    (member-equal (svar-fix v) (svex-alist-vars x))))
      :hints(("Goal" 
              :induct <call>
              :expand ((svex-alist-vars x)
                       (svex-alist-quote/var-p x)
                       (svex-vars (cdar x))
                       <call>))))
    
    (local (in-theory (enable svex-alist-fix))))



  (define svex-alist-invert ((x svex-alist-p))
    :returns (new-x svex-alist-p)
    (if (atom x)
        nil
      (if (and (mbt (and (consp (car x))
                         (svar-p (caar x))))
               (svex-case (cdar x) :var))
          (cons (cons (svex-var->name (cdar x)) (svex-var (caar x)))
                (svex-alist-invert (cdr x)))
        (svex-alist-invert (cdr x))))
    ///
    (local (Defthm svex-eval-when-var
             (implies (svex-case x :var)
                      (equal (svex-eval x env) (svex-env-lookup (svex-var->name x) env)))
             :hints(("Goal" :in-theory (enable svex-eval)))))

    (local (Defthm svex-eval-when-quote
             (implies (svex-case x :quote)
                      (equal (svex-eval x env) (svex-quote->val x)))
             :hints(("Goal" :in-theory (enable svex-eval)))))

    (defret svex-lookup-of-<fn>
      (equal (svex-lookup v new-x)
             (let ((key (svex-alist-var-rlookup v x)))
               (and key (svex-var key))))
      :hints(("Goal" :in-theory (enable svex-alist-var-rlookup
                                        svex-lookup-of-cons))))
  
    (defret lookup-in-eval-of-svex-alist-invert
      (implies (and (svex-alist-quote/var-p x)
                    (no-duplicatesp-equal (svex-alist-keys x)))
               (equal (svex-env-lookup var (svex-alist-eval new-x (svex-alist-eval x env)))
                      (if (member-equal (svar-fix var) (svex-alist-vars x))
                          (svex-env-lookup var env)
                        (4vec-x))))
      :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons-split
                                        svex-alist-eval
                                        svex-alist-keys
                                        svex-alist-vars
                                        svex-lookup-of-cons
                                        svex-alist-quote/var-p))))



    (defret eval-of-svex-alist-invert
      (implies (and (svex-alist-quote/var-p x)
                    (no-duplicatesp-equal (svex-alist-keys x)))
               (svex-envs-equivalent (svex-alist-eval new-x (svex-alist-eval x env))
                                     (svex-env-extract (svex-alist-vars x) env)))
      :hints(("Goal" :in-theory (enable svex-envs-equivalent))))
  
    (local (defthm svex-lookup-of-atom
             (implies (atom x)
                      (equal (svex-lookup v x) nil))
             :hints(("Goal" :in-theory (enable svex-lookup)))))
  
    ;; (local (defthm svex-kind-of-lookup-when-svex-alist-quote/var-p
    ;;          (implies (svex-alist-quote/var-p x)
    ;;                   (not (equal (svex-kind (svex-lookup v x)) :call)))
    ;;          :hints(("Goal" :in-theory (enable svex-alist-quote/var-p
    ;;                                            svex-lookup-of-cons)
    ;;                  :induct t))))

    (local (defthm name-of-svex-lookup-member-svex-alist-vars
             (implies (svex-case (svex-lookup v x) :var)
                      (member-equal (svex-var->name (svex-lookup v x))
                                    (svex-alist-vars x)))
             :hints(("Goal" :in-theory (enable svex-alist-vars
                                               svex-lookup-of-cons)))))

    (local (defthm svex-kind-of-lookup-when-svex-alist-quote/var-p
             (implies (and (svex-alist-quote/var-p x)
                           (not (svex-case (svex-lookup v x) :var)))
                      (equal (svex-kind (svex-lookup v x)) :quote))
             :hints(("Goal" :in-theory (enable svex-alist-quote/var-p
                                               svex-lookup-of-cons)
                     :induct t))))
  
    (defret eval-of-svex-alist-invert-invert
      (implies (and (svex-alist-quote/var-p x)
                    (no-duplicatesp-equal (svex-alist-keys x)))
               (equal (svex-alist-eval x (svex-alist-eval new-x (svex-alist-eval x env)))
                      (svex-alist-eval x env))))

    (local (in-theory (enable svex-alist-fix)))))

(local (in-theory (disable hons-dups-p)))

(defsection svex-alistlist-invert

  ;; For reconstructing pipeline inputs from FSM inputs, it's useful to be able
  ;; to invert an svex alist whose expressions only contain variables and
  ;; constants -- i.e. map the variables in the values to the corresponding
  ;; keys.  This isn't exact wrt variables used more than once.
  
  (define svex-alistlist-quote/var-p ((x svex-alistlist-p))
    (if (atom x)
        t
      (and (svex-alist-quote/var-p (car x))
           (svex-alistlist-quote/var-p (cdr x)))))


  (define svex-alistlist-no-duplicate-keys-p ((x svex-alistlist-p))
    (if (atom x)
        t
      (and (not (acl2::hons-dups-p (svex-alist-keys (car x))))
           (svex-alistlist-no-duplicate-keys-p (cdr x))))
    ///
    (local (in-theory (enable svex-alistlist-p))))
  

  (define svex-alistlist-invert ((x svex-alistlist-p))
    :returns (new-x svex-alistlist-p)
    (if (atom x)
        nil
      (cons (svex-alist-invert (car x))
            (svex-alistlist-invert (cdr x))))))


(define svex-alist-all-xes ((x svex-alist-p))
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (svar-p (caar x)))))
             (svex-equiv (cdar x) (svex-x)))
         (svex-alist-all-xes (cdr x))))
  ///
  (local (defthm svex-lookup-when-svex-alist-all-xes
           (implies (and (svex-alist-all-xes x)
                         (svex-lookup k x))
                    (equal (svex-lookup k x) (svex-x)))
           :hints(("Goal" :in-theory (enable svex-lookup-redef)))))
  (defthmd svex-alist-all-xes-implies-bottom
    (implies (svex-alist-all-xes x)
             (svex-env-<<= (svex-alist-eval x env) any))
    :hints(("Goal" :in-theory (enable svex-env-<<=))))

  (defthmd svex-alist-all-xes-implies-eval-similar-nil
    (implies (svex-alist-all-xes x)
             (svex-envs-similar (svex-alist-eval x env) nil))
    :hints(("Goal" :in-theory (enable svex-envs-similar))))

  (local (in-theory (enable svex-alist-fix))))






(define svarlist-change-override ((x svarlist-p)
                                  (type svar-overridetype-p))
  :returns (new-x svarlist-p)
  (if (atom x)
      nil
    (cons (svar-change-override (car x) type)
          (svarlist-change-override (cdr x) type)))
  ///
  (defret svarlist-override-p-of-<fn>
    (iff (svarlist-override-p new-x other-type)
         (or (atom x)
             (svar-overridetype-equiv other-type type)))
    :hints(("Goal" :in-theory (enable svarlist-override-p)))))



(encapsulate nil
  (local (defthm set-equiv-of-cons
           (iff (set-equiv (cons a b) c)
                (and (member-equal a c)
                     (set-equiv (remove-equal a b) (remove-equal a c))))
           :hints(("Goal" :use ((:instance acl2::set-unequal-witness-correct
                                 (x (cons a b)) (y c))
                                (:instance acl2::set-unequal-witness-correct
                                 (x (remove-equal a b)) (y (remove-equal a c)))
                                (:instance ACL2::SET-EQUIV-IMPLIES-IFF-MEMBER-2
                                 (x (acl2::set-unequal-witness (cons a b) c))
                                 (y (remove-equal a b))
                                 (y-equiv (remove-equal a c)))
                                (:instance ACL2::SET-EQUIV-IMPLIES-IFF-MEMBER-2
                                 (x (acl2::set-unequal-witness (remove-equal a b) (remove-equal a c)))
                                 (y (cons a b))
                                 (y-equiv c))
                                (:instance ACL2::SET-EQUIV-IMPLIES-IFF-MEMBER-2
                                 (x a)
                                 (y (cons a b))
                                 (y-equiv c)))
                   :in-theory (disable acl2::set-equiv-implies-iff-member-2
                                       acl2::subsetp-member
                                       remove-equal
                                       acl2::remove-when-not-member)))))
  (defthmd svar-override-triplelist-override-vars-of-triples-when-svarlist-override-p
    (implies (svarlist-override-p vars nil)
             (set-equiv (svar-override-triplelist-override-vars
                         (svarlist-to-override-triples vars))
                        (append (svarlist-change-override vars :val)
                                (svarlist-change-override vars :test))))
    :hints(("Goal" :in-theory (enable svarlist-change-override svar-change-override
                                      svarlist-to-override-triples
                                      svarlist-override-p
                                      svar-override-p
                                      svar-override-triplelist-override-vars)))))



(defthm svarlist-override-p-of-override-test-vars
  (implies (svarlist-override-p in-vars nil)
           (svarlist-override-p (svar-override-triplelist->testvars
                                 (svarlist-to-override-triples in-vars))
                                :test))
  :hints(("Goal" :in-theory (enable svarlist-override-p svar-override-p
                                    svar-override-triplelist->testvars
                                    svarlist-to-override-triples
                                    svar-override-triplelist->testvars))))


(defthm svarlist-override-p-of-override-val-vars
  (implies (svarlist-override-p in-vars nil)
           (svarlist-override-p (svar-override-triplelist->valvars
                                 (svarlist-to-override-triples in-vars))
                                :val))
  :hints(("Goal" :in-theory (enable svarlist-override-p svar-override-p
                                    svar-override-triplelist->valvars
                                    svarlist-to-override-triples
                                    svar-override-triplelist->valvars))))



;; propagating svex-envlist-removekeys through svtv-cycle-run-fsm-inputs

(define svtv-cyclephaselist-keys ((x svtv-cyclephaselist-p))
  (if (atom x)
      nil
    (append (alist-keys (svtv-cyclephase->constants (car x)))
            (svtv-cyclephaselist-keys (cdr x)))))


(defthm svex-env-removekeys-of-append-keys
  (equal (svex-env-removekeys (append keys1 keys2) x)
         (svex-env-removekeys keys1 (svex-env-removekeys keys2 x)))
  :hints(("Goal" :in-theory (enable svex-env-removekeys))))

(defthm svex-envlist-removekeys-of-append-keys
  (equal (svex-envlist-removekeys (append keys1 keys2) x)
         (svex-envlist-removekeys keys1 (svex-envlist-removekeys keys2 x)))
  :hints(("Goal" :in-theory (enable svex-envlist-removekeys))))

(encapsulate nil
  (local (defthm member-when-override-mismatch
           (implies (and (svarlist-override-p x x-type)
                         (svar-override-p k k-type)
                         (not (svar-overridetype-equiv x-type k-type)))
                    (not (member-equal k (svarlist-fix x))))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svar-override-p
                                             svarlist-fix)))))

  (local (in-theory (disable member-equal)))

  ;; (defthm svex-env-remove-override-vars-when-non-override
  ;;   (implies (and (svarlist-override-p remkeys :val)
  ;;                 (svarlist-override-p (alist-keys (svex-env-fix x)) nil))
  ;;            (equal (svex-env-removekeys remkeys x)
  ;;                   (svex-env-fix x)))
  ;;   :hints(("Goal" :in-theory (enable svex-env-removekeys
  ;;                                     svex-env-fix
  ;;                                     alist-keys
  ;;                                     svarlist-override-p))))

  ;; (defthm svex-env-remove-override-tests-when-non-override
  ;;   (implies (and (svarlist-override-p remkeys :test)
  ;;                 (svarlist-override-p (alist-keys (svex-env-fix x)) nil))
  ;;            (equal (svex-env-removekeys remkeys x)
  ;;                   (svex-env-fix x)))
  ;;   :hints(("Goal" :in-theory (enable svex-env-removekeys
  ;;                                     svex-env-fix
  ;;                                     alist-keys
  ;;                                     svarlist-override-p))))

  (local (defthm svex-env-remove-override-vars-when-override-mismatch-lemma
           (implies (and (svarlist-override-p remkeys rem-type)
                         (svarlist-override-p (alist-keys (svex-env-fix x)) key-type)
                         (not (svar-overridetype-equiv rem-type key-type)))
                    (equal (svex-env-removekeys remkeys x)
                           (svex-env-fix x)))
           :hints(("Goal" :in-theory (e/d (svex-env-removekeys
                                           svex-env-fix
                                           svarlist-override-p)
                                          (iff))))))

  (defthm svex-env-remove-override-vars-when-override-mismatch
    (implies (and (svarlist-override-p remkeys rem-type)
                  (equal keys (alist-keys (svex-env-fix x)))
                  ;; (syntaxp (or (cw "keys: ~x0~%" keys) t))
                  (svarlist-override-p keys key-type)
                  (not (svar-overridetype-equiv rem-type key-type)))
             (equal (svex-env-removekeys remkeys x)
                    (svex-env-fix x))))

  (defthm svex-env-remove-override-vars-when-override-mismatch-svarlist-change-override
    (implies (and (svarlist-override-p remkeys rem-type)
                  (equal keys (alist-keys (svex-env-fix x)))
                  (bind-free (case-match keys
                               (('svarlist-change-override & key-type)
                                `((key-type . ,key-type)))
                               (& nil))
                             (key-type))
                  (svarlist-override-p keys key-type)
                  (not (svar-overridetype-equiv rem-type key-type)))
             (equal (svex-env-removekeys remkeys x)
                    (svex-env-fix x)))))

(defthm svex-envlist-remove-override-vars-of-svtv-cycle-fsm-inputs
  (implies (and (svarlist-override-p (svtv-cyclephaselist-keys x) nil)
                (svarlist-override-p keys :val))
           (equal (svex-envlist-removekeys keys (svtv-cycle-fsm-inputs cycle-inputs x))
                  (svtv-cycle-fsm-inputs (svex-env-removekeys keys cycle-inputs) x)))
  :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                    svtv-cycle-step-fsm-inputs
                                    svtv-cyclephaselist-keys
                                    svex-envlist-removekeys))))

(defthm svex-envlist-remove-override-tests-of-svtv-cycle-fsm-inputs
  (implies (and (svarlist-override-p (svtv-cyclephaselist-keys x) nil)
                (svarlist-override-p keys :test))
           (equal (svex-envlist-removekeys keys (svtv-cycle-fsm-inputs cycle-inputs x))
                  (svtv-cycle-fsm-inputs (svex-env-removekeys keys cycle-inputs) x)))
  :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                    svtv-cycle-step-fsm-inputs
                                    svtv-cyclephaselist-keys
                                    svex-envlist-removekeys))))

(defthm svex-envlist-remove-override-vars-of-svtv-cycle-run-fsm-inputs
  (implies (and (svarlist-override-p (svtv-cyclephaselist-keys x) nil)
                (svarlist-override-p keys :val))
           (equal (svex-envlist-removekeys keys (svtv-cycle-run-fsm-inputs cycle-inputs x))
                  (svtv-cycle-run-fsm-inputs (svex-envlist-removekeys keys cycle-inputs) x)))
  :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs
                                    svex-envlist-removekeys))))

(defthm svex-envlist-remove-override-tests-of-svtv-cycle-run-fsm-inputs
  (implies (and (svarlist-override-p (svtv-cyclephaselist-keys x) nil)
                (svarlist-override-p keys :test))
           (equal (svex-envlist-removekeys keys (svtv-cycle-run-fsm-inputs cycle-inputs x))
                  (svtv-cycle-run-fsm-inputs (svex-envlist-removekeys keys cycle-inputs) x)))
  :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs
                                    svex-envlist-removekeys))))
                



;; propagating svex-envlist-removekeys through svtv-fsm-to-base-fsm-inputs


(defthm alist-keys-of-svtv-name-lhs-map-eval-x
  (Equal (alist-keys (svtv-name-lhs-map-eval-x x env))
         (alist-keys (svtv-name-lhs-map-fix x)))
  :hints(("Goal" :in-theory (enable alist-keys svtv-name-lhs-map-fix svtv-name-lhs-map-eval-x))))

;; (defthm svarlist-override-p-keys-of-svtv-name-lhs-map-keys-change-override
;;   (svarlist-override-p (alist-keys (svtv-name-lhs-map-keys-change-override x :override-val val :override-test test))
;;                        val test)
;;   :hints(("Goal" :in-theory (enable svarlist-override-p alist-keys svtv-name-lhs-map-keys-change-override))))


(defthm alist-keys-of-svtv-name-lhs-map-keys-change-override
  (equal (alist-keys (svtv-name-lhs-map-keys-change-override x type))
         (svarlist-change-override (alist-keys (svtv-name-lhs-map-fix x)) type))
  :hints(("Goal" :in-theory (enable alist-keys svtv-name-lhs-map-keys-change-override svarlist-change-override svtv-name-lhs-map-fix svar-change-override))))

(defthm svex-env-removekeys-when-subset
  (implies (double-rewrite (subsetp-equal (alist-keys (svex-env-fix x))
                                          (svarlist-fix keys)))
           (equal (svex-env-removekeys keys x) nil))
  :hints(("Goal" :in-theory (enable svex-env-removekeys alist-keys svex-env-fix))))

(encapsulate nil
  (local (defund svarlist-change-override-map-member (key x type)
           (let ((n (acl2::index-of key (svarlist-change-override x type))))
             (and n
                  (nth n x)))))

  (local (defthm member-of-svarlist-change-override-necc
           (implies (and (equal key (svar-change-override w type))
                         (member-equal w x))
                    (member-equal key (svarlist-change-override x type)))
           :hints(("Goal" :in-theory (enable svarlist-change-override-map-member
                                             acl2::index-of
                                             svarlist-change-override)))))

  (local (defthm member-of-svarlist-change-override-witness
           (implies (acl2::rewriting-negative-literal
                     `(member-equal ,key (svarlist-change-override ,x ,type)))
                    (iff (member-equal key (svarlist-change-override x type))
                         (let ((w (svarlist-change-override-map-member key x type)))
                           (and (member-equal w x)
                                (equal key (svar-change-override w type))))))
           :hints(("Goal" :in-theory (enable svarlist-change-override-map-member
                                             acl2::index-of
                                             svarlist-change-override)))))
  
  (defcong set-equiv set-equiv (svarlist-change-override x type) 1
    :hints (("goal" :in-theory (enable acl2::set-unequal-witness-rw))))

  ;; (local (defthm svarlist-subsetp
  ;;          (implies (subsetp-equal x y)
  ;;                   (subsetp-equal (svarlist-fix x) (svarlist-fix y)))))
  
  (defthm svarlist-change-override-of-subset
    (implies (subsetp-equal x y)
             (subsetp-equal (svarlist-change-override x type)
                            (svarlist-change-override y type)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))))


(defthm alist-keys-of-fast-alist-clean-under-set-equiv
  (set-equiv (alist-keys (fast-alist-clean x))
             (alist-keys x))
  :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw
                                    acl2::alist-keys-member-hons-assoc-equal))))


(local
 (encapsulate nil
   (local (defthm subsetp-lhs-vars-lookup-of-svtv-name-lhs-map-vars
            (implies (svar-p key)
                     (subsetp (lhs-vars (cdr (hons-assoc-equal key map)))
                              (svtv-name-lhs-map-vars map)))
            :hints(("Goal" :in-theory (enable hons-assoc-equal
                                              svtv-name-lhs-map-vars)))))

   (defthm subsetp-svtv-name-lhs-map-vars-of-fal-extract
         (subsetp (svtv-name-lhs-map-vars (fal-extract keys map))
                  (svtv-name-lhs-map-vars map))
         :hints(("Goal" :in-theory (enable fal-extract)
                 :induct (fal-extract keys map)
                 :expand ((:Free (a b) (svtv-name-lhs-map-vars (cons a b)))))))

   (defthm subsetp-svtv-name-lhs-map-vars-of-fal-extract-fix
         (subsetp (svtv-name-lhs-map-vars (fal-extract keys (svtv-name-lhs-map-fix map)))
                  (svtv-name-lhs-map-vars map))
         :hints(("Goal" :in-theory (enable fal-extract)
                 :induct (fal-extract keys map)
                 :expand ((:Free (a b) (svtv-name-lhs-map-vars (cons a b)))))))))


;; Need to change this to take only the override-val/override-test keys of the namemap!
(defthm svex-env-remove-override-vals-of-svtv-fsm-phase-inputs
  (implies (and (subsetp-equal (svarlist-change-override
                                (svtv-name-lhs-map-vars
                                 (acl2::fal-extract (alist-keys (svex-env-fix override-vals))
                                                    (svtv-name-lhs-map-fix namemap))) :val)
                               (svarlist-fix keys))
                (svarlist-override-p keys :val)
                (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil))
           (equal (svex-env-removekeys keys (svtv-fsm-phase-inputs inputs override-vals override-tests namemap))
                  (svtv-fsm-phase-inputs inputs nil override-tests namemap)))
  :hints(("Goal" :in-theory (enable svtv-fsm-phase-inputs
                                    svtv-fsm-env-inversemap
                                    (fast-alist-clean))
          :expand ((:free (x) (fal-extract nil x))))))


(defthm svex-env-remove-override-tests-of-svtv-fsm-phase-inputs
  (implies (and (subsetp-equal (svarlist-change-override
                                (svtv-name-lhs-map-vars
                                 (acl2::fal-extract (alist-keys (svex-env-fix override-tests))
                                                    (svtv-name-lhs-map-fix namemap))) :test)
                               (svarlist-fix keys))
                (svarlist-override-p keys :test)
                (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil))
           (equal (svex-env-removekeys keys (svtv-fsm-phase-inputs inputs override-vals override-tests namemap))
                  (svtv-fsm-phase-inputs inputs override-vals nil namemap)))
  :hints(("Goal" :in-theory (enable svtv-fsm-phase-inputs
                                    svtv-fsm-env-inversemap
                                    (fast-alist-clean))
          :expand ((:free (x) (fal-extract nil x))))))

(define svex-alistlist-all-keys ((x svex-alistlist-p))
  (if (atom x)
      nil
    (append (svex-alist-keys (car x))
            (svex-alistlist-all-keys (cdr x)))))

(define svex-envlist-all-keys ((x svex-envlist-p))
  (if (atom x)
      nil
    (append (alist-keys (svex-env-fix (car x)))
            (svex-envlist-all-keys (cdr x))))
  ///
  (defthm svex-envlist-all-keys-of-svex-alistlist-eval
    (Equal (svex-envlist-all-keys (svex-alistlist-eval x env))
           (svex-alistlist-all-keys x))
    :hints(("Goal" :in-theory (enable svex-alistlist-all-keys
                                      svex-alistlist-eval)))))

(local (defthm fal-extract-of-append
         (equal (fal-extract (append x y) z)
                (append (fal-extract x z)
                        (fal-extract y z)))
         :hints(("Goal" :in-theory (enable fal-extract)))))


(defthm svtv-name-lhs-map-vars-of-append-under-set-equiv
  (set-equiv (svtv-name-lhs-map-vars (append x y))
             (append (svtv-name-lhs-map-vars x)
                     (svtv-name-lhs-map-vars y)))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-vars))))

(defthm svex-envlist-remove-override-vals-of-svtv-fsm-to-base-fsm-inputs
  (implies (and (subsetp-equal (svarlist-change-override
                                (svtv-name-lhs-map-vars
                                 (acl2::fal-extract (svex-envlist-all-keys override-vals)
                                                    (svtv-name-lhs-map-fix namemap)))
                                :val)
                               (svarlist-fix keys))
                (svarlist-override-p keys :val)
                (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil))
           (equal (svex-envlist-removekeys keys (svtv-fsm-to-base-fsm-inputs inputs override-vals override-tests namemap))
                  (svtv-fsm-to-base-fsm-inputs inputs nil override-tests namemap)))
  :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs
                                    svex-envlist-all-keys
                                    svex-envlist-removekeys))))

(defthm svex-envlist-remove-override-tests-of-svtv-fsm-to-base-fsm-inputs
  (implies (and (subsetp-equal (svarlist-change-override
                                (svtv-name-lhs-map-vars
                                 (acl2::fal-extract (svex-envlist-all-keys override-tests)
                                                    (svtv-name-lhs-map-fix namemap)))
                                :test)
                               (svarlist-fix keys))
                (svarlist-override-p keys :test)
                (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil))
           (equal (svex-envlist-removekeys keys (svtv-fsm-to-base-fsm-inputs inputs override-vals override-tests namemap))
                  (svtv-fsm-to-base-fsm-inputs inputs override-vals nil namemap)))
  :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs
                                    svex-envlist-all-keys
                                    svex-envlist-removekeys))))


(define svtv-cyclephaselist-no-i/o-phase ((phases svtv-cyclephaselist-p))
  (if (atom phases)
      t
    (and (b* (((svtv-cyclephase ph1) (car phases)))
           (and (not ph1.inputs-free)
                (not ph1.outputs-captured)))
         (svtv-cyclephaselist-no-i/o-phase (cdr phases)))))

(define svtv-cyclephaselist-unique-i/o-phase ((phases svtv-cyclephaselist-p))
  (if (atom phases)
      nil
    (b* (((svtv-cyclephase ph1) (car phases)))
      (or (and (not ph1.inputs-free)
               (not ph1.outputs-captured)
               (svtv-cyclephaselist-unique-i/o-phase (cdr phases)))
          (and ph1.inputs-free
               ph1.outputs-captured
               (svtv-cyclephaselist-no-i/o-phase (cdr phases)))))))





;; Propagating svar-override-triplelist-envlists-ok-<<= through svtv-cycle-run-fsm-inputs

(local (defun svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs-when-no-i/o-ind (phases ref-envs)
         (if (atom phases)
             ref-envs
           (svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs-when-no-i/o-ind
            (Cdr phases) (cdr ref-envs)))))


(local (defthm svex-env-lookup-of-override-test-var-when-no-override-keys
         (implies (and (svar-override-p key :test)
                       (svarlist-override-p (alist-keys (svex-env-fix env)) nil))
                  (equal (svex-env-lookup key env) (4vec-x)))
         :hints(("Goal" :in-theory (enable svex-env-lookup
                                           svarlist-override-p
                                           svex-env-fix
                                           alist-keys
                                           svar-override-p)))))

(defthm svar-override-triplelist-env-ok-<<=-when-no-override-keys
  (implies (and (svarlist-override-p (alist-keys (svex-env-fix override-env)) nil)
                (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
                (svarlist-override-p (svar-override-triplelist->valvars triples) :val))
           (svar-override-triplelist-env-ok-<<= triples override-env ref-env))
  :hints(("Goal" :in-theory (enable svar-override-triplelist-env-ok-<<=
                                    svar-override-triplelist->valvars
                                    svar-override-triplelist->testvars
                                    svarlist-override-p))))

(local (defthm svex-env-boundp-of-override-test-var-when-no-override-keys
         (implies (and (svar-override-p key :test)
                       (svarlist-override-p (alist-keys (svex-env-fix env)) nil))
                  (not (svex-env-boundp key env)))
         :hints(("Goal" :in-theory (enable svex-env-boundp
                                           svarlist-override-p
                                           svex-env-fix
                                           alist-keys
                                           svar-override-p)))))

(local (defthm svex-env-boundp-of-override-val-var-when-no-override-keys
         (implies (and (svar-override-p key :val)
                       (svarlist-override-p (alist-keys (svex-env-fix env)) nil))
                  (not (svex-env-boundp key env)))
         :hints(("Goal" :in-theory (enable svex-env-boundp
                                           svarlist-override-p
                                           svex-env-fix
                                           alist-keys
                                           svar-override-p)))))

(defthm svar-override-triplelist-env-ok-<<=-of-append-when-no-override-keys
  (implies (and (svarlist-override-p (alist-keys (svex-env-fix env1)) nil)
                (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
                (svarlist-override-p (svar-override-triplelist->valvars triples) :val))
           (equal (svar-override-triplelist-env-ok-<<= triples (append env1 override-env) ref-env)
                  (svar-override-triplelist-env-ok-<<= triples override-env ref-env)))
  :hints(("Goal" :in-theory (enable svar-override-triplelist-env-ok-<<=
                                    svar-override-triplelist->valvars
                                    svar-override-triplelist->testvars
                                    svarlist-override-p))))

(defthm svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs-when-no-i/o
  (implies (and (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
                (svarlist-override-p (svar-override-triplelist->valvars triples) :val)
                (svtv-cyclephaselist-no-i/o-phase phases))
           (equal (svar-override-triplelist-envlists-ok-<<=
                   triples (svtv-cycle-fsm-inputs ins phases) ref-envs)
                  t))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-no-i/o-phase
                                    svtv-cycle-fsm-inputs
                                    svtv-cyclephaselist-keys
                                    svar-override-triplelist-envlists-ok-<<=
                                    svtv-cycle-step-fsm-inputs)
          :induct (svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs-when-no-i/o-ind
                   phases ref-envs))))


(local (defthm svtv-cyclephaselist-has-outputs-captured-when-unique-i/o
         (implies (svtv-cyclephaselist-unique-i/o-phase phases)
                  (svtv-cyclephaselist-has-outputs-captured phases))
         :hints(("Goal" :in-theory (enable svtv-cyclephaselist-has-outputs-captured
                                           svtv-cyclephaselist-unique-i/o-phase)))))

(defthm svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs
  (implies (and (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
                (svarlist-override-p (svar-override-triplelist->valvars triples) :val)
                (svtv-cyclephaselist-unique-i/o-phase phases))
           (equal (svar-override-triplelist-envlists-ok-<<=
                   triples (svtv-cycle-fsm-inputs ins phases) ref-envs)
                  (svar-override-triplelist-env-ok-<<=
                   triples ins (nth (svtv-cycle-output-phase phases) ref-envs))))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-keys
                                    svtv-cyclephaselist-unique-i/o-phase
                                    svtv-cycle-fsm-inputs
                                    svtv-cycle-output-phase
                                    svar-override-triplelist-envlists-ok-<<=
                                    svtv-cycle-step-fsm-inputs)
          :induct (svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs-when-no-i/o-ind
                   phases ref-envs))))



(defthm svtv-cycle-output-phase-type-when-has-outputs-captured
  (implies (svtv-cyclephaselist-has-outputs-captured x)
           (natp (svtv-cycle-output-phase x)))
  :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                    svtv-cyclephaselist-has-outputs-captured)))
  :rule-classes :type-prescription)

(defthm svex-env-p-nth-of-svex-envlist
  (implies (svex-envlist-p x)
           (svex-env-p (nth n x))))

(defthm nthcdr-of-svex-envlist-fix
  (equal (nthcdr n (svex-envlist-fix x))
         (svex-envlist-fix (nthcdr n x)))
  :hints(("Goal" :in-theory (enable svex-envlist-fix))))


(defthm svtv-cyclephaselist-has-outputs-captured-when-atom
  (implies (atom x)
           (not (svtv-cyclephaselist-has-outputs-captured x)))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-has-outputs-captured))))

(define svex-envlist-phase-outputs-extract-cycle-outputs ((phases svtv-cyclephaselist-p)
                                                          (phase-outs svex-envlist-p))
  :guard (svtv-cycle-output-phase phases)
  :returns (cycle-outs svex-envlist-p)
  :measure (len phase-outs)
  (if (atom phase-outs)
      nil
    (cons (svex-env-fix (nth (svtv-cycle-output-phase phases) phase-outs))
          (svex-envlist-phase-outputs-extract-cycle-outputs
           phases
           (nthcdr (if (mbt (consp phases))
                       (len phases)
                     1)
                   phase-outs))))
  ///

  (local (defun nth-of-extract-ind (n phases phase-outs)
           (if (zp n)
               (list phases phase-outs)
             (nth-of-extract-ind (1- n) phases (nthcdr (len phases) phase-outs)))))

  (local (defthm natp-of-times-decr-lemma
           (implies (and (posp n)
                         (natp len)
                         (natp m))
                    (natp (+ (- len)
                             m
                             (* n len))))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))
           :rule-classes :type-prescription))

  (local (defthm plus-x-y-minus-x-z
           (equal (+ x y (* -1 x) z)
                  (+ y z))))
  
  (defret nth-of-<fn>
    (implies (svtv-cyclephaselist-has-outputs-captured phases)
             (Equal (nth n cycle-outs)
                    (svex-env-fix (nth (+ (svtv-cycle-output-phase phases)
                                          (* (nfix n) (len phases)))
                                       phase-outs))))
    :hints (("goal" :induct (nth-of-extract-ind n phases phase-outs)
             :expand (<call>))))

  (defret len-of-<fn>
    (implies (and (equal 0 (mod (len phase-outs) (len phases)))
                  (consp phases))
             (equal (len cycle-outs)
                    (floor (len phase-outs) (len phases))))
    :hints(("Goal" :in-theory (enable acl2::mod-redef acl2::floor-redef)))))


(local (defun svar-override-triplelist-envlists-ok-<<=-of-append-ind (x ref-envs)
         (if (atom x)
             ref-envs
           (svar-override-triplelist-envlists-ok-<<=-of-append-ind (cdr x) (cdr ref-envs)))))

(defthm svar-override-triplelist-envlists-ok-<<=-of-append
  (equal (svar-override-triplelist-envlists-ok-<<= triples (append x y) ref-envs)
         (and (svar-override-triplelist-envlists-ok-<<= triples x (take (len x) ref-envs))
              (svar-override-triplelist-envlists-ok-<<= triples y (nthcdr (len x) ref-envs))))
  :hints(("Goal" :in-theory (enable svar-override-triplelist-envlists-ok-<<=)
          :induct (svar-override-triplelist-envlists-ok-<<=-of-append-ind x ref-envs))))


(local (defun svar-override-triple-envlists-ok-of-svtv-cycle-run-fsm-inputs-ind (phases ins ref-envs)
         (if (atom ins)
             (list phases ref-envs)
           (svar-override-triple-envlists-ok-of-svtv-cycle-run-fsm-inputs-ind phases (cdr ins)
                                                                              (nthcdr (if (consp phases) (len phases) 1)
                                                                                      ref-envs)))))

(defthm svtv-cyclephaselist-unique-i/o-phase-when-atom
  (implies (atom x)
           (not (svtv-cyclephaselist-unique-i/o-phase x)))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-unique-i/o-phase))))

(defthm svtv-cyclephaselist-unique-i/o-phase-implies-natp-output-phase
  (implies (svtv-cyclephaselist-unique-i/o-phase x)
           (natp (svtv-cycle-output-phase x)))
  :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                    svtv-cyclephaselist-unique-i/o-phase)))
  :rule-classes :type-prescription)

(defthm svtv-cycle-output-phase-bound
  (implies (svtv-cycle-output-phase phases)
           (< (svtv-cycle-output-phase phases) (len phases)))
  :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                    svtv-cyclephaselist-has-outputs-captured)))
  :rule-classes :linear)

(defthm svar-override-triple-envlists-ok-of-svtv-cycle-run-fsm-inputs
  (implies (and (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
                (svarlist-override-p (svar-override-triplelist->valvars triples) :val)
                (svtv-cyclephaselist-unique-i/o-phase phases))
           (equal (svar-override-triplelist-envlists-ok-<<=
                   triples (svtv-cycle-run-fsm-inputs ins phases) ref-envs)
                  (svar-override-triplelist-envlists-ok-<<=
                   triples ins (svex-envlist-phase-outputs-extract-cycle-outputs
                                phases ref-envs))))
  :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs
                                    svex-envlist-phase-outputs-extract-cycle-outputs
                                    svar-override-triplelist-envlists-ok-<<=)
          :induct (svar-override-triple-envlists-ok-of-svtv-cycle-run-fsm-inputs-ind
                   phases ins ref-envs))))


(defthm svtv-probealist-extract-of-probealist-cycle-adjust
  (implies (svtv-cyclephaselist-has-outputs-captured phases)
           (equal (svtv-probealist-extract (svtv-probealist-cycle-adjust probes phases) phase-outputs)
                  (svtv-probealist-extract probes (svex-envlist-phase-outputs-extract-cycle-outputs phases phase-outputs))))
  :hints(("Goal" :in-theory (enable svtv-probealist-extract
                                    svtv-probealist-cycle-adjust
                                    svtv-probealist-cycle-adjust-aux)
          :induct (len probes))))



;; Propagating svar-override-triplelist-envlists-ok-<<= through svtv-fsm-to-base-fsm-inputs

;; For svar-override-triplelist-env-ok of svtv-fsm-phase-inputs, instead of
;; iterating through the triples we'd like to find a succinct way to open it up
;; and say exactly what the requirements are in terms of the few override
;; signals that are actually set.

;; - Triples are generated by svarlist-to-override-triples of override-free variables

;; - Extract of override-test names from namemap has LHSes that are among the
;; override variables (therefore when translated to override-test variables,
;; they are among the tests of the triples) -- maybe this isn't needed

;; - Settings of override-test variables are constant -- the user env from the
;; pipeline contains only constant settings of the override test pipe variables


(define 4vec-override-values-ok-<<= ((test 4vec-p)
                                     (val 4vec-p)
                                     (ref 4vec-p))
  (4vec-<<= (4vec-bit?! test val 0)
            (4vec-bit?! test ref 0)))


(defthm svar-override-triplelist-env-ok-<<=-implies-override-values-ok-of-member
  (implies (and (svar-override-triplelist-env-ok-<<= x override-env ref-env)
                (member-equal trip (svar-override-triplelist-fix x)))
           (b* (((svar-override-triple trip)))
             (4vec-override-values-ok-<<= (svex-env-lookup trip.testvar override-env)
                                          (svex-env-lookup trip.valvar override-env)
                                          (svex-env-lookup trip.refvar ref-env))))
  :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=
                                    svar-override-triplelist-env-ok-<<=
                                    svar-override-triplelist-fix))))

(defthm triple-when-member-of-svarlist-to-override-triples
  (implies (svarlist-override-p vars nil)
           (iff (member-equal trip (svarlist-to-override-triples vars))
                (and (svar-override-triple-p trip)
                     (b* (((svar-override-triple trip)))
                       (and (member-equal trip.refvar (svarlist-fix vars))
                            (equal trip.valvar (svar-change-override trip.refvar :val))
                            (equal trip.testvar (svar-change-override trip.refvar :test)))))))
  :hints(("Goal" :in-theory (e/d (svarlist-to-override-triples
                                    svar-change-override
                                    svarlist-fix
                                    svarlist-override-p
                                    svar-override-p)
                                 (member-equal))
          :induct (len vars))))

(define svex-env-filter-override ((x svex-env-p)
                                  (type svar-overridetype-p))
  :returns (new-x svex-env-p)
  (if (atom x)
      nil
    (if (and (mbt (and (consp (car x))
                       (svar-p (caar x))))
             (svar-override-p (caar x) type))
        (cons (mbe :logic (cons (caar x) (4vec-fix (cdar x)))
                   :exec (car x))
              (svex-env-filter-override (cdr x) type))
      (svex-env-filter-override (cdr x) type)))
  ///
  (defret boundp-of-<fn>
    (equal (svex-env-boundp k new-x)
           (and (svar-override-p k type)
                (svex-env-boundp k x)))
    :hints(("Goal" :in-theory (enable svex-env-boundp))))

  (defret lookup-of-<fn>
    (equal (svex-env-lookup k new-x)
           (if (svar-override-p k type)
               (svex-env-lookup k x)
             (4vec-x)))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (defthm svex-env-filter-override-of-append
    (equal (svex-env-filter-override (append x y) type)
           (append (svex-env-filter-override x type)
                   (svex-env-filter-override y type))))

  (local (defthm svar-override-p-diff
           (implies (and (svar-override-p x type1)
                         (not (svar-overridetype-equiv type1 type2)))
                    (not (svar-override-p x type2)))
           :hints(("Goal" :in-theory (enable svar-override-p)))))


  (local
   (defret svex-env-filter-override-when-keys-override-p-lemma
     (implies (svarlist-override-p (alist-keys (svex-env-fix x)) key-type)
              (equal new-x
                     (and (svar-overridetype-equiv type key-type)
                          (svex-env-fix x))))
     :hints(("Goal" :in-theory (e/d (svex-env-fix
                                     svarlist-override-p)
                                    (svar-overridetype-equiv))))))

  (defret svex-env-filter-override-when-keys-override-p
    (implies (and (equal keys (alist-keys (svex-env-fix x)))
                  (svarlist-override-p keys key-type))
             (equal new-x
                    (and (svar-overridetype-equiv type key-type)
                         (svex-env-fix x)))))

  (defret svex-env-filter-override-when-keys-change-override-p
    (implies (and (equal keys (alist-keys (svex-env-fix x)))
                  (bind-free (case-match keys
                               (('svarlist-change-override & key-type)
                                `((key-type . ,key-type)))
                               (& nil))
                             (key-type))
                  (svarlist-override-p keys key-type))
             (equal new-x
                    (and (svar-overridetype-equiv type key-type)
                         (svex-env-fix x)))))

  (defret svarlist-override-p-alist-keys-of-<fn>
    (svarlist-override-p (alist-keys new-x) type)
    :hints(("Goal" :in-theory (enable svarlist-override-p))))
  
  (local (in-theory (enable svex-env-fix))))

(define svex-env-keys-change-override ((x svex-env-p)
                                       (type svar-overridetype-p))
  :returns (new-x svex-env-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (cons (cons (svar-change-override (caar x) type)
                    (4vec-fix (cdar x)))
              (svex-env-keys-change-override (cdr x) type))
      (svex-env-keys-change-override (cdr x) type)))
  ///
  
  (local
   (defret svex-env-lookup-of-<fn>-lemma
     (implies (and (svarlist-override-p (alist-keys (svex-env-fix x)) key-type)
                   (svar-override-p v type))
              (equal (svex-env-lookup v new-x)
                     (svex-env-lookup (svar-change-override v key-type) x)))
     :hints(("Goal" :in-theory (enable svarlist-override-p
                                       alist-keys
                                       svex-env-fix
                                       svex-env-lookup
                                       equal-of-svar-change-override)))))

  (local
   (defret svex-env-boundp-of-<fn>-lemma
     (implies (and (svarlist-override-p (alist-keys (svex-env-fix x)) key-type)
                   (svar-override-p v type))
              (equal (svex-env-boundp v new-x)
                     (svex-env-boundp (svar-change-override v key-type) x)))
     :hints(("Goal" :in-theory (enable svarlist-override-p
                                       alist-keys
                                       svex-env-fix
                                       svex-env-boundp
                                       equal-of-svar-change-override)))))


  (defret svex-env-lookup-of-<fn>
    (implies (and (equal keys (alist-keys (svex-env-fix x)))
                  (svarlist-override-p keys key-type)
                  (svar-override-p v type))
             (equal (svex-env-lookup v new-x)
                    (svex-env-lookup (svar-change-override v key-type) x))))

  (defret svex-env-boundp-of-<fn>
    (implies (and (equal keys (alist-keys (svex-env-fix x)))
                  (svarlist-override-p keys key-type)
                  (svar-override-p v type))
             (equal (svex-env-boundp v new-x)
                    (svex-env-boundp (svar-change-override v key-type) x))))

  (defret svex-env-lookup-of-<fn>-bind-special
    (implies (and (equal keys (alist-keys (svex-env-fix x)))
                  (bind-free (case-match keys
                               (('svarlist-change-override & key-type)
                                `((key-type . ,key-type)))
                               (('alist-keys ('svex-env-filter-override & key-type))
                                `((key-type . ,key-type)))
                               (& nil))
                             (key-type))
                  (svarlist-override-p keys key-type)
                  (svar-override-p v type))
             (equal (svex-env-lookup v new-x)
                    (svex-env-lookup (svar-change-override v key-type) x))))

  (defret svex-env-boundp-of-<fn>-bind-special
    (implies (and (equal keys (alist-keys (svex-env-fix x)))
                  (bind-free (case-match keys
                               (('svarlist-change-override & key-type)
                                `((key-type . ,key-type)))
                               (('alist-keys ('svex-env-filter-override & key-type))
                                `((key-type . ,key-type)))
                               (& nil))
                             (key-type))
                  (svarlist-override-p keys key-type)
                  (svar-override-p v type))
             (equal (svex-env-boundp v new-x)
                    (svex-env-boundp (svar-change-override v key-type) x))))
      

  (local (in-theory (enable svex-env-fix))))


(defthmd svarlist-to-override-triples-in-terms-of-svar-change-override
  (implies (svarlist-override-p vars nil)
           (equal (svarlist-to-override-triples vars)
                  (if (Atom vars)
                      nil
                    (cons (make-svar-override-triple
                           :refvar (car vars)
                           :valvar (svar-change-override (car vars) :val)
                           :testvar (svar-change-override (car vars) :test))
                          (svarlist-to-override-triples (cdr vars))))))
  :hints(("Goal" :in-theory (enable svarlist-override-p
                                    svarlist-to-override-triples
                                    svar-change-override
                                    svar-override-p)))
  :rule-classes ((:definition :controller-alist ((svarlist-to-override-triples t))
                  :install-body nil)))



(define svar-override-keys-check-override-envs ((keys svarlist-p)
                                            (test-env svex-env-p)
                                            (val-env svex-env-p)
                                            (ref-env svex-env-p))
  :returns (ok)
  (if (atom keys)
      t
    (and (4vec-override-values-ok-<<= (svex-env-lookup (svar-change-override (car keys) :test) test-env)
                                      (svex-env-lookup (svar-change-override (car keys) :val) val-env)
                                      (svex-env-lookup (car keys) ref-env))
         (svar-override-keys-check-override-envs (cdr keys) test-env val-env ref-env)))
  ///
  (defthm svar-override-triplelist-env-ok-<<=-in-terms-of-check-override-envs
    (implies (svarlist-override-p vars nil)
             (equal (svar-override-triplelist-env-ok-<<= (svarlist-to-override-triples vars) override-env ref-env)
                    (svar-override-keys-check-override-envs
                     vars
                     (svex-env-filter-override override-env :test) ;; test
                     (svex-env-filter-override override-env :val)
                     ref-env)))
    :hints(("Goal" :in-theory (enable svarlist-override-p
                                      svar-override-keys-check-override-envs
                                      svar-override-triplelist-env-ok-<<=
                                      svarlist-to-override-triples
                                      svar-override-p
                                      svar-change-override
                                      4vec-override-values-ok-<<=))))

  (defthm svar-override-keys-check-override-envs-implies-when-member
    (implies (and (svar-override-keys-check-override-envs keys test-env val-env ref-env)
                  (member-equal (svar-fix var) (svarlist-fix keys)))
             (4vec-override-values-ok-<<= (svex-env-lookup (svar-change-override var :test) test-env)
                                          (svex-env-lookup (svar-change-override var :val) val-env)
                                          (svex-env-lookup var ref-env))))

  (defund svar-override-keys-check-override-envs-witness (keys test-env val-env ref-env)
    (if (atom keys)
        nil
      (if (4vec-override-values-ok-<<= (svex-env-lookup (svar-change-override (car keys) :test) test-env)
                                       (svex-env-lookup (svar-change-override (car keys) :val) val-env)
                                       (svex-env-lookup (car keys) ref-env))
          (svar-override-keys-check-override-envs-witness (cdr keys) test-env val-env ref-env)
        (svar-fix (car keys)))))

  (local (in-theory (enable svar-override-keys-check-override-envs-witness)))

  (defthmd svar-override-keys-check-override-envs-when-witness
    (implies (b* ((var (svar-override-keys-check-override-envs-witness keys test-env val-env ref-env)))
               (or (not (member-equal (svar-fix var) (svarlist-fix keys)))
                   (4vec-override-values-ok-<<= (svex-env-lookup (svar-change-override var :test) test-env)
                                                (svex-env-lookup (svar-change-override var :val) val-env)
                                                (svex-env-lookup var ref-env))))
             (svar-override-keys-check-override-envs keys test-env val-env ref-env)))

  (defthmd svar-override-keys-check-override-envs-by-witness
    (implies (acl2::rewriting-positive-literal `(svar-override-keys-check-override-envs ,keys ,test-env ,val-env ,ref-env))
             (equal (svar-override-keys-check-override-envs keys test-env val-env ref-env)
                    (b* ((var (svar-override-keys-check-override-envs-witness keys test-env val-env ref-env)))
               (or (not (member-equal (svar-fix var) (svarlist-fix keys)))
                   (4vec-override-values-ok-<<= (svex-env-lookup (svar-change-override var :test) test-env)
                                                (svex-env-lookup (svar-change-override var :val) val-env)
                                                (svex-env-lookup var ref-env)))))))

  (defcong set-equiv equal (svar-override-keys-check-override-envs keys test-env val-env ref-env) 1
    :hints (("goal" :cases ((svar-override-keys-check-override-envs keys test-env val-env ref-env)
                            (svar-override-keys-check-override-envs keys-equiv test-env val-env ref-env))
             :in-theory (enable svar-override-keys-check-override-envs-when-witness
                                svar-override-keys-check-override-envs-by-witness))))

  (defcong svex-envs-similar equal (svar-override-keys-check-override-envs keys test-env val-env ref-env) 2)
  (defcong svex-envs-similar equal (svar-override-keys-check-override-envs keys test-env val-env ref-env) 3)
  (defcong svex-envs-similar equal (svar-override-keys-check-override-envs keys test-env val-env ref-env) 4)

  (local (defthmd 4vec-override-values-ok-<<=-of-lookup-test-casesplit
           (implies (case-split (not (svex-env-boundp key test-env)))
                    (4vec-override-values-ok-<<= (svex-env-lookup key test-env) val ref))
           :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=
                                             svex-env-boundp
                                             svex-env-lookup)))))

  (local (defthmd 4vec-override-values-ok-<<=-of-lookup-val-casesplit
           (implies (case-split (not (svex-env-boundp key val-env)))
                    (4vec-override-values-ok-<<= test (svex-env-lookup key val-env) ref))
           :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=
                                             svex-env-boundp
                                             svex-env-lookup)))))


  (local (defthm svar-override-p-when-member
           (implies (and (member-equal (svar-fix v) (svarlist-fix keys))
                         (svarlist-override-p keys type))
                    (svar-override-p v type))
           :hints(("Goal" :in-theory (enable svarlist-override-p)))))
                       
  
  (local (defthm member-svar-change-override-when-member-non-override-testvars
           (implies (and (member-equal (svar-change-override v :test) testvars)
                         (member-equal (svar-fix v) (svarlist-fix keys))
                         (svarlist-override-p keys nil))
                    (member-equal (svar-fix v) (svarlist-change-override testvars nil)))
           :hints(("Goal" :in-theory (enable svarlist-change-override svarlist-override-p)))))

  (local (defthm member-svar-change-override-when-member-non-override-valvars
           (implies (and (member-equal (svar-change-override v :val) valvars)
                         (member-equal (svar-fix v) (svarlist-fix keys))
                         (svarlist-override-p keys nil))
                    (member-equal (svar-fix v) (svarlist-change-override valvars nil)))
           :hints(("Goal" :in-theory (enable svarlist-change-override svarlist-override-p)))))
  
  
  (defthmd svar-override-keys-check-override-envs-intersect-test-env
    (implies (svarlist-override-p keys nil)
             (equal (svar-override-keys-check-override-envs (intersection-equal (svarlist-fix keys)
                                                                            (svarlist-change-override
                                                                             (alist-keys (svex-env-fix test-env)) nil))
                                                        test-env val-env ref-env)
                    (svar-override-keys-check-override-envs keys test-env val-env ref-env)))
    :hints (("Goal" :cases ((svar-override-keys-check-override-envs (intersection-equal (svarlist-fix keys)
                                                                            (svarlist-change-override
                                                                             (alist-keys (svex-env-fix test-env)) nil))
                                                        test-env val-env ref-env)
                            (svar-override-keys-check-override-envs keys test-env val-env ref-env))
             :in-theory (enable svar-override-keys-check-override-envs-by-witness
                                svar-override-keys-check-override-envs-when-witness)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:computed-hint-replacement
                   ('(:in-theory (e/d (svex-env-boundp-iff-member-alist-keys)
                                      (4vec-override-values-ok-<<=-of-lookup-test-casesplit))))
                   :in-theory (e/d (4vec-override-values-ok-<<=-of-lookup-test-casesplit)
                                   (svar-override-keys-check-override-envs-when-witness)))))
    :otf-flg t)


  (defthmd svar-override-keys-check-override-envs-intersect-val-env
    (implies (svarlist-override-p keys nil)
             (equal (svar-override-keys-check-override-envs (intersection-equal (svarlist-fix keys)
                                                                                (svarlist-change-override
                                                                                 (alist-keys (svex-env-fix val-env))
                                                                                 nil))
                                                        test-env val-env ref-env)
                    (svar-override-keys-check-override-envs keys test-env val-env ref-env)))
    :hints (("Goal" :cases ((svar-override-keys-check-override-envs (intersection-equal (svarlist-fix keys)
                                                                                        (svarlist-change-override
                                                                                         (alist-keys (svex-env-fix val-env))
                                                                                         nil))
                                                                    test-env val-env ref-env)
                            (svar-override-keys-check-override-envs keys test-env val-env ref-env))
             :in-theory (enable svar-override-keys-check-override-envs-by-witness
                                svar-override-keys-check-override-envs-when-witness)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:computed-hint-replacement
                   ('(:in-theory (e/d (svex-env-boundp-iff-member-alist-keys)
                                      (4vec-override-values-ok-<<=-of-lookup-val-casesplit))))
                   :in-theory (e/d (4vec-override-values-ok-<<=-of-lookup-val-casesplit)
                                   (svar-override-keys-check-override-envs-when-witness)))))
    :otf-flg t))


(define svex-envlist-filter-override ((x svex-envlist-p)
                                       (type svar-overridetype-p))
  :returns (new-x svex-envlist-p)
  (if (atom x)
      nil
    (cons (svex-env-filter-override (car x) type)
          (svex-envlist-filter-override (cdr x) type)))
  ///

  (defthm svex-envlist-filter-override-of-append
    (equal (svex-envlist-filter-override (append x y) type)
           (append (svex-envlist-filter-override x type)
                   (svex-envlist-filter-override y type))))
                         
  
  (local
   (defret svex-envlist-filter-override-when-keys-override-p-lemma
     (implies (svarlist-override-p (svex-envlist-all-keys x) key-type)
              (equal new-x
                     (if (svar-overridetype-equiv key-type type)
                         (svex-envlist-fix x)
                       (repeat (len x) nil))))
     :hints(("Goal" :in-theory (enable svex-envlist-all-keys
                                       svarlist-override-p
                                       repeat)))))

  (defret svex-envlist-filter-override-when-keys-override-p
    (implies (and (equal keys (svex-envlist-all-keys x))
                  (svarlist-override-p keys key-type))
             (equal new-x
                    (if (svar-overridetype-equiv key-type type)
                        (svex-envlist-fix x)
                      (repeat (len x) nil)))))

  (defret svex-envlist-filter-override-when-keys-change-override-p
    (implies (and (equal keys (svex-envlist-all-keys x))
                  (bind-free (case-match keys
                               (('svarlist-change-override & key-type)
                                `((key-type . ,key-type)))
                               (& nil))
                             (key-type))
                  (svarlist-override-p keys key-type))
             (equal new-x
                    (if (svar-overridetype-equiv key-type type)
                        (svex-envlist-fix x)
                      (repeat (len x) nil))))))

(define svex-envlist-keys-change-override ((x svex-envlist-p)
                                           (type svar-overridetype-p))
  :returns (new-x svex-envlist-p)
  (if (atom x)
      nil
    (cons (svex-env-keys-change-override (car x) type)
          (svex-envlist-keys-change-override (cdr x) type)))
  ///

  (defthm svex-envlist-keys-change-override-of-append
    (equal (svex-envlist-keys-change-override (append x y) type)
           (append (svex-envlist-keys-change-override x type)
                   (svex-envlist-keys-change-override y type))))


  (defret len-of-svex-envlist-keys-change-override
    (equal (len new-x) (len x))))





(define svar-override-keys-check-override-envlists ((keys svarlist-p)
                                                    (test-envs svex-envlist-p)
                                                    (val-envs svex-envlist-p)
                                                    (ref-envs svex-envlist-p))
  :returns (ok)
  (if (atom test-envs)
      t
    (and (svar-override-keys-check-override-envs keys (car test-envs) (car val-envs) (car ref-envs))
         (svar-override-keys-check-override-envlists keys (cdr test-envs) (cdr val-envs) (cdr ref-envs))))
  ///
  (defthm svar-override-triplelist-env-ok-<<=-in-terms-of-check-override-envlists
    (implies (svarlist-override-p vars nil)
             (equal (svar-override-triplelist-envlists-ok-<<= (svarlist-to-override-triples vars) override-envs ref-envs)
                    (svar-override-keys-check-override-envlists
                     vars
                     (svex-envlist-filter-override override-envs :test) ;; test
                     (svex-envlist-filter-override override-envs :val)
                     ref-envs)))
    :hints(("Goal" :in-theory (enable svar-override-keys-check-override-envlists
                                      svar-override-triplelist-envlists-ok-<<=
                                      svex-envlist-filter-override))))

  (defcong set-equiv equal (svar-override-keys-check-override-envlists keys test-envs val-envs ref-envs) 1
    :hints (("goal" :cases ((svar-override-keys-check-override-envlists keys test-envs val-envs ref-envs)
                            (svar-override-keys-check-override-envlists keys-equiv test-envs val-envs ref-envs)))))

  (defcong svex-envlists-similar equal (svar-override-keys-check-override-envlists keys test-envs val-envs ref-envs) 2)
  (defcong svex-envlists-similar equal (svar-override-keys-check-override-envlists keys test-envs val-envs ref-envs) 3)
  (defcong svex-envlists-similar equal (svar-override-keys-check-override-envlists keys test-envs val-envs ref-envs) 4))


(defthm svex-env-filter-override-vals-of-svtv-fsm-phase-inputs
  (equal (svex-env-filter-override (svtv-fsm-phase-inputs ins vals tests map) :val)
         (svtv-fsm-phase-inputs nil vals nil map))
  :hints(("Goal" :in-theory (enable svtv-fsm-phase-inputs
                                    svtv-fsm-env-inversemap)
          :expand ((:free (x) (fal-extract nil x))))))

(defthm svex-env-filter-override-tests-of-svtv-fsm-phase-inputs
  (equal (svex-env-filter-override (svtv-fsm-phase-inputs ins vals tests map) :test)
         (svtv-fsm-phase-inputs nil nil tests map))
  :hints(("Goal" :in-theory (enable svtv-fsm-phase-inputs
                                    svtv-fsm-env-inversemap)
          :expand ((:free (x) (fal-extract nil x))))))


(defthm svex-envlist-filter-override-vals-of-svtv-fsm-to-base-fsm-inputs
  (equal (svex-envlist-filter-override (svtv-fsm-to-base-fsm-inputs ins vals tests map) :val)
         (svtv-fsm-to-base-fsm-inputs (repeat (len ins) nil) vals nil map))
  :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs
                                    svex-envlist-filter-override))))

(defthm svex-envlist-filter-override-tests-of-svtv-fsm-to-base-fsm-inputs
  (equal (svex-envlist-filter-override (svtv-fsm-to-base-fsm-inputs ins vals tests map) :test)
         (svtv-fsm-to-base-fsm-inputs (repeat (len ins) nil) nil tests map))
  :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs
                                    svex-envlist-filter-override))))

(define svtv-cyclephaselist-remove-constants ((x svtv-cyclephaselist-p))
  :returns (new-x svtv-cyclephaselist-p)
  (if (atom x)
      nil
    (cons (change-svtv-cyclephase (car x) :constants nil)
          (svtv-cyclephaselist-remove-constants (cdr x))))
  ///
  (defret svtv-cyclephaselist-no-i/o-phase-of-<fn>
    (equal (svtv-cyclephaselist-no-i/o-phase new-x)
           (svtv-cyclephaselist-no-i/o-phase x))
    :hints(("Goal" :in-theory (enable svtv-cyclephaselist-no-i/o-phase))))

  (defret svtv-cyclephaselist-unique-i/o-phase-of-<fn>
    (equal (svtv-cyclephaselist-unique-i/o-phase new-x)
           (svtv-cyclephaselist-unique-i/o-phase x))
    :hints(("Goal" :in-theory (enable svtv-cyclephaselist-unique-i/o-phase))))

  (defret svtv-cyclephaselist-has-outputs-captured-of-<fn>
    (equal (svtv-cyclephaselist-has-outputs-captured new-x)
           (svtv-cyclephaselist-has-outputs-captured x))
    :hints(("Goal" :in-theory (enable svtv-cyclephaselist-has-outputs-captured))))

  (defret svtv-cycle-output-phase-of-<fn>
    (equal (svtv-cycle-output-phase new-x)
           (svtv-cycle-output-phase x))
    :hints(("Goal" :in-theory (enable svtv-cycle-output-phase)))))
  


;; (defthm svex-envlist-filter-override-tests-of-svtv-cycle-fsm-inputs-no-i/o
;;   (implies (and (svarlist-override-p (svtv-cyclephaselist-keys x) nil)
;;                 (svtv-cyclephaselist-no-i/o-phase x))
;;            (equal (svex-envlist-filter-override (svtv-cycle-fsm-inputs cycle-inputs x) :test)
;;                   (repeat (len x) nil)))
;;   :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
;;                                     svtv-cyclephaselist-keys
;;                                     svtv-cycle-step-fsm-inputs
;;                                     svtv-cyclephaselist-no-i/o-phase
;;                                     svex-envlist-filter-override
;;                                     repeat))))

;; (defthm svex-envlist-filter-override-tests-of-svtv-cycle-fsm-inputs
;;   (implies (and (svarlist-override-p (svtv-cyclephaselist-keys x) nil)
;;                 (svtv-cyclephaselist-unique-i/o-phase x))
;;            (equal (svex-envlist-filter-override (svtv-cycle-fsm-inputs cycle-inputs x) :test)
;;                   (update-nth (svtv-cycle-output-phase x)
;;                               (svex-env-filter-override cycle-inputs :test)
;;                               (repeat (len x) nil))))
;;   :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
;;                                     svtv-cyclephaselist-keys
;;                                     svtv-cycle-step-fsm-inputs
;;                                     svtv-cyclephaselist-unique-i/o-phase
;;                                     svtv-cycle-output-phase
;;                                     svex-envlist-filter-override
;;                                     repeat))))


(defthm svex-envlist-filter-override-tests-of-svtv-cycle-fsm-inputs
  (implies (svarlist-override-p (svtv-cyclephaselist-keys x) nil)
           (equal (svex-envlist-filter-override (svtv-cycle-fsm-inputs cycle-inputs x) :test)
                  (svtv-cycle-fsm-inputs (svex-env-filter-override cycle-inputs :test)
                                         (svtv-cyclephaselist-remove-constants x))))
  :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                    svtv-cyclephaselist-remove-constants
                                    svtv-cyclephaselist-keys
                                    svtv-cycle-step-fsm-inputs
                                    svex-envlist-filter-override))))

(defthm svex-envlist-filter-override-tests-of-svtv-cycle-run-fsm-inputs
  (implies (svarlist-override-p (svtv-cyclephaselist-keys x) nil)
           (equal (svex-envlist-filter-override (svtv-cycle-run-fsm-inputs cycle-inputs x) :test)
                  (svtv-cycle-run-fsm-inputs (svex-envlist-filter-override cycle-inputs :test)
                                             (svtv-cyclephaselist-remove-constants x))))
  :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs
                                    svex-envlist-filter-override))))


(defthm svex-envlist-filter-override-vals-of-svtv-cycle-fsm-inputs
  (implies (svarlist-override-p (svtv-cyclephaselist-keys x) nil)
           (equal (svex-envlist-filter-override (svtv-cycle-fsm-inputs cycle-inputs x) :val)
                  (svtv-cycle-fsm-inputs (svex-env-filter-override cycle-inputs :val)
                                         (svtv-cyclephaselist-remove-constants x))))
  :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                    svtv-cyclephaselist-remove-constants
                                    svtv-cyclephaselist-keys
                                    svtv-cycle-step-fsm-inputs
                                    svex-envlist-filter-override))))

(defthm svex-envlist-filter-override-vals-of-svtv-cycle-run-fsm-inputs
  (implies (svarlist-override-p (svtv-cyclephaselist-keys x) nil)
           (equal (svex-envlist-filter-override (svtv-cycle-run-fsm-inputs cycle-inputs x) :val)
                  (svtv-cycle-run-fsm-inputs (svex-envlist-filter-override cycle-inputs :val)
                                             (svtv-cyclephaselist-remove-constants x))))
  :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs
                                    svex-envlist-filter-override))))

(defthm len-of-svtv-cycle-run-fsm-inputs
  (equal (len (svtv-cycle-run-fsm-inputs ins phases))
         (* (len ins) (len phases)))
  :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs))))




(defcong svex-envlists-similar equal (svex-envlist-<<= x y) 1
  :hints (("goal" :cases ((svex-envlist-<<= x y))
           :in-theory (enable svex-envlist-<<=))))

(defcong svex-envlists-similar equal (svex-envlist-<<= x y) 2
  :hints (("goal" :cases ((svex-envlist-<<= x y))
           :in-theory (enable svex-envlist-<<=))))

(defthmd svex-envlists-similar-rec
  (equal (svex-envlists-similar x y)
         (if (or (atom x) (atom y))
             (and (atom x) (atom y))
           (and (svex-envs-similar (car x) (car y))
                (svex-envlists-similar (cdr x) (cdr y)))))
  :hints (("goal" :cases ((svex-envlists-similar x y))
           :do-not-induct t)
          (and stable-under-simplificationp
               (b* ((lit (assoc 'svex-envlists-similar clause)))
                 `(:expand (,lit)))))
  :rule-classes ((:definition :install-body nil
                  :controller-alist ((svex-envlists-similar t t)))))


(local (include-book "std/basic/inductions" :dir :system))

(defcong set-equiv svex-envlists-similar (svex-envlist-removekeys keys x) 1
  :hints(("Goal" :in-theory (enable svex-envlist-removekeys)
          :induct (len x)
          :expand ((:with svex-envlists-similar-rec (svex-envlists-similar keys keys-equiv))))))




;; Monotonicity of input stuff


(defthm svtv-cycle-fsm-inputs-monotonic
  (implies (svex-env-<<= x y)
           (svex-envlist-<<= (svtv-cycle-fsm-inputs x phases) (svtv-cycle-fsm-inputs y phases)))
  :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                    svtv-cycle-step-fsm-inputs
                                    svex-envlist-<<=))))

(defthm svex-envlist-<<=-of-append
  (implies (and (equal (len x1) (len x2))
                (svex-envlist-<<= x1 x2)
                (svex-envlist-<<= y1 y2))
           (svex-envlist-<<= (append x1 y1) (append x2 y2)))
  :hints(("Goal" :in-theory (enable svex-envlist-<<=))))


(defthm svex-envlist-<<=-of-append-nil
  (implies (and (svex-envlist-<<= x1 nil)
                (svex-envlist-<<= y1 nil))
           (svex-envlist-<<= (append x1 y1) nil))
  :hints(("Goal" :in-theory (enable svex-envlist-<<=))))


(defthm svtv-cycle-run-fsm-inputs-monotonic
  (implies (and (svex-envlist-<<= x y)
                (<= (len x) (len y)))
           (svex-envlist-<<= (svtv-cycle-run-fsm-inputs x phases) (svtv-cycle-run-fsm-inputs y phases)))
  :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs
                                    svex-envlist-<<=))))

(defthm lhs-eval-x-monotonic
  (implies (svex-env-<<= x y)
           (4vec-<<= (lhs-eval-x lhs x) (lhs-eval-x lhs y)))
  :hints(("Goal" :in-theory (enable lhs-eval-x lhatom-eval-x))))


(defthm svtv-name-lhs-map-eval-x-monotonic
  (implies (svex-env-<<= x y)
           (svex-env-<<= (svtv-name-lhs-map-eval-x map x)
                         (svtv-name-lhs-map-eval-x map y)))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-x))))


(defthm svtv-fsm-phase-inputs-monotonic
  (implies (and (svex-env-<<= ins1 ins2)
                (equal (alist-keys (svex-env-fix ins1))
                       (alist-keys (svex-env-fix ins2)))
                (svex-env-<<= vals1 vals2)
                (equal (alist-keys (svex-env-fix vals1))
                       (alist-keys (svex-env-fix vals2)))
                (svex-env-<<= tests1 tests2)
                (equal (alist-keys (svex-env-fix tests1))
                       (alist-keys (svex-env-fix tests2))))
           (svex-env-<<= (svtv-fsm-phase-inputs ins1 vals1 tests1 map)
                         (svtv-fsm-phase-inputs ins2 vals2 tests2 map)))
  :hints(("Goal" :in-theory (enable svtv-fsm-phase-inputs))
         (and stable-under-simplificationp
              `(:expand (,(car (last clause)))
                :in-theory (e/d (svex-env-<<=-necc)
                                (svex-env-lookupp-of-svtv-name-lhs-map-eval-x))))))

(define svex-alist-keys-list ((x svex-alistlist-p))
  :returns (keys svarlist-list-p)
  (if (atom x)
      nil
    (cons (svex-alist-keys (car x))
          (svex-alist-keys-list (cdr x)))))


(define svex-env-keys-list ((x svex-envlist-p))
  :returns (keys svarlist-list-p)
  (if (atom x)
      nil
    (cons (alist-keys (svex-env-fix (car x)))
          (svex-env-keys-list (cdr x))))
  ///
  (defthm svex-env-keys-list-of-svex-alistlist-eval
    (equal (svex-env-keys-list (svex-alistlist-eval x env))
           (svex-alist-keys-list x))
    :hints(("Goal" :in-theory (enable svex-alist-keys-list
                                      svex-alistlist-eval)))))
      


(defthm svtv-fsm-to-base-fsm-inputs-monotonic
  (implies (and (svex-envlist-<<= ins1 ins2)
                (equal (svex-env-keys-list ins1)
                       (svex-env-keys-list ins2))
                (svex-envlist-<<= vals1 vals2)
                (equal (svex-env-keys-list vals1)
                       (svex-env-keys-list vals2))
                (svex-envlist-<<= tests1 tests2)
                (equal (svex-env-keys-list tests1)
                       (svex-env-keys-list tests2)))
           (svex-envlist-<<= (svtv-fsm-to-base-fsm-inputs ins1 vals1 tests1 map)
                         (svtv-fsm-to-base-fsm-inputs ins2 vals2 tests2 map)))
  :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs
                                    svex-envlist-<<=
                                    svex-env-keys-list))))


(defthmd alist-keys-of-svex-env-open-cons
  (equal (alist-keys (svex-env-fix (cons pair rest)))
         (if (and (consp pair)
                  (svar-p (car pair)))
             (cons (car pair)
                   (alist-keys (svex-env-fix rest)))
           (alist-keys (svex-env-fix rest))))
  :hints(("Goal" :in-theory (enable alist-keys svex-env-fix))))



(encapsulate nil
  (local (defthm svex-alistlist-evals-equal-when-envs-agree
           (implies (svex-envs-agree (svex-alistlist-vars x) env1 env2)
                    (equal (equal (svex-alistlist-eval x env1)
                                  (svex-alistlist-eval x env2))
                           t))
           :hints(("Goal" :in-theory (enable svex-alistlist-eval-when-envs-agree)))))
  
  (local (defthm svex-env-extract-intersection
           (implies (svarlist-p vars)
                    (svex-envs-agree vars env (svex-env-extract (intersection-equal (alist-keys (svex-env-fix env)) vars) env)))
           :hints(("Goal" :in-theory (enable svex-envs-agree-by-witness
                                             svex-env-lookup
                                             acl2::alist-keys-member-hons-assoc-equal)))))
  
  (defthmd svex-alistlist-eval-of-env-remove-keys
    (implies (and (equal env-keys (alist-keys (svex-env-fix env)))
                  (syntaxp (quotep env-keys))
                  (equal alistlist-vars (svex-alistlist-vars alists))
                  (syntaxp (quotep alistlist-vars))
                  (equal intersec (acl2::hons-intersection env-keys alistlist-vars))
                  (syntaxp (and (quotep intersec)
                                (not (equal (len (unquote intersec)) (len (unquote env-keys)))))))
             (equal (svex-alistlist-eval alists env)
                    (svex-alistlist-eval alists (svex-env-extract intersec env))))
    :hints(("Goal" :in-theory (enable svex-alistlist-eval-when-envs-agree)))))


(encapsulate nil
  (local (Defthm svex-env-<<=-nil-implies-<<=-any
           (implies (svex-env-<<= x nil)
                    (svex-env-<<= x any))
           :hints(("Goal" :in-theory (enable svex-env-<<=-transitive-1)))))
  
  (defthm svex-envlist-<<=-transitive-1
    (implies (and (svex-envlist-<<= x y)
                  (svex-envlist-<<= y z))
             (svex-envlist-<<= x z))
    :hints(("Goal" :in-theory (enable svex-envlist-<<=
                                      svex-env-<<=-transitive-1))))

  (defthm svex-envlist-<<=-transitive-2
    (implies (and (svex-envlist-<<= y z)
                  (svex-envlist-<<= x y))
             (svex-envlist-<<= x z))))


(defthm svex-envlist-<<=-of-cycle/svtv-fsm-monotonic-rw
  (implies (and (svex-envlist-<<=
                 (svtv-cycle-run-fsm-inputs
                  (svtv-fsm-to-base-fsm-inputs
                   (svex-alistlist-eval pipe-ins env1)
                   nil nil namemap)
                  cycle-phases)
                 ins)
                (svex-alistlist-check-monotonic pipe-ins)
                (svex-env-<<= env env1))
           (svex-envlist-<<=
            (svtv-cycle-run-fsm-inputs
             (svtv-fsm-to-base-fsm-inputs
              (svex-alistlist-eval pipe-ins env)
              nil nil namemap)
             cycle-phases)
            ins))
  :hints(("Goal" :in-theory (enable svex-envlist-<<=-transitive-2))))



(defthm svex-envlist-<<=-of-nthcdr
  (implies (svex-envlist-<<= x y)
           (svex-envlist-<<= (nthcdr n x) (nthcdr n y)))
  :hints(("Goal" :in-theory (enable svex-envlist-<<= nthcdr))))


(encapsulate nil
  (local (defun ind (phases x y)
           (if (atom x)
               (list phases y)
             (ind phases
                  (nthcdr (max (len phases) 1) x)
                  (nthcdr (max (len phases) 1) y)))))

  (local (defthm svex-env-<<=-nth-nil
           (implies (and (svex-envlist-<<= x y)
                         (<= (len y) (nfix n)))
                    (svex-env-<<= (nth n x) nil))
           :hints (("goal" :use ((:instance svex-envlist-<<=-implies-nth))
                    :in-theory (disable svex-envlist-<<=-implies-nth)))))

  (local (defthm len-equal-0
           (equal (equal (len x) 0) (not (consp x)))))
  
  (defthm svex-envlist-phase-outputs-extract-cycle-outputs-monotonic
    (implies (svex-envlist-<<= x y)
             (svex-envlist-<<= (svex-envlist-phase-outputs-extract-cycle-outputs phases x)
                               (svex-envlist-phase-outputs-extract-cycle-outputs phases y)))
    :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs)
            :induct (ind phases x y)
            :expand ((svex-envlist-phase-outputs-extract-cycle-outputs phases x)
                     (svex-envlist-phase-outputs-extract-cycle-outputs phases y)
                     (:free (a b c) (svex-envlist-<<= (cons a b) c))
                     (:free (y) (svex-envlist-<<= nil y)))))))




(defthm lhs-eval-monotonic
  (implies (svex-env-<<= x y)
           (4vec-<<= (lhs-eval lhs x) (lhs-eval lhs y)))
  :hints(("Goal" :in-theory (enable lhs-eval lhatom-eval lhrange-eval))))

(defthm lhs-eval-zero-monotonic
  (implies (svex-env-<<= x y)
           (4vec-<<= (lhs-eval-zero lhs x) (lhs-eval-zero lhs y)))
  :hints(("Goal" :in-theory (enable lhs-eval-zero lhatom-eval-zero))))


(defthm svtv-name-lhs-map-eval-monotonic
  (implies (svex-env-<<= x y)
           (svex-env-<<= (svtv-name-lhs-map-eval map x)
                         (svtv-name-lhs-map-eval map y)))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval))))


(defthm svtv-name-lhs-map-eval-list-monotonic
  (implies (and (svex-envlist-<<= x y)
                (equal (len x) (len y)))
           (svex-envlist-<<= (svtv-name-lhs-map-eval-list map x)
                              (svtv-name-lhs-map-eval-list map y)))
  :hints(("Goal" :in-theory (enable svex-envlist-<<=
                                    svtv-name-lhs-map-eval-list))))



(encapsulate nil
  (local (in-theory (disable svar-override-keys-check-override-envs-by-witness)))
  
  (local (defun ind (phases ref-envs)
           (if (atom phases)
               ref-envs
             (ind (cdr phases) (cdr ref-envs)))))

  (local (defthm 4vec-override-values-ok-<<=-of-x
           (equal (4vec-override-values-ok-<<= (4vec-x) val ref)
                  t)
           :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=)))))
  
  (defthm svar-override-keys-check-override-envlists-of-svtv-cycle-fsm-inputs-no-i/o
    (implies (and (svtv-cyclephaselist-no-i/o-phase phases)
                  (svarlist-override-p (svtv-cyclephaselist-keys phases) nil))
             (equal (svar-override-keys-check-override-envlists
                     vars
                     (svtv-cycle-fsm-inputs test-env phases)
                     (svtv-cycle-fsm-inputs val-env phases)
                     ref-envs)
                    t))
    :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                      svtv-cycle-step-fsm-inputs
                                      svtv-cyclephaselist-keys
                                      svar-override-keys-check-override-envlists
                                      svtv-cyclephaselist-no-i/o-phase
                                      svar-override-keys-check-override-envs-by-witness)
            :induct (ind phases ref-envs))))

  (defthm svar-override-keys-check-override-envlists-of-svtv-cycle-fsm-inputs-no-i/o-no-vals
    (implies (and (svtv-cyclephaselist-no-i/o-phase phases)
                  (svarlist-override-p (svtv-cyclephaselist-keys phases) nil))
             (equal (svar-override-keys-check-override-envlists
                     vars
                     (svtv-cycle-fsm-inputs test-env phases)
                     (repeat (len phases) nil)
                     ref-envs)
                    t))
    :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                      svtv-cycle-step-fsm-inputs
                                      svtv-cyclephaselist-keys
                                      svar-override-keys-check-override-envlists
                                      svtv-cyclephaselist-no-i/o-phase
                                      svar-override-keys-check-override-envs-by-witness)
            :induct (ind phases ref-envs))))


  (defthm svar-override-keys-check-override-envs-of-append-non-override-tests
    (implies (svarlist-override-p (alist-keys (svex-env-fix consts)) nil)
             (equal (svar-override-keys-check-override-envs
                     vars
                     (append consts test-env)
                     val-env
                     ref-env)
                    (svar-override-keys-check-override-envs
                     vars test-env val-env ref-env)))
    :hints(("Goal" :in-theory (enable svar-override-keys-check-override-envs)
            :induct (svar-override-keys-check-override-envs
                     vars test-env val-env ref-env))))

  (defthm svar-override-keys-check-override-envs-of-append-non-override-vals
    (implies (svarlist-override-p (alist-keys (svex-env-fix consts)) nil)
             (equal (svar-override-keys-check-override-envs
                     vars
                     test-env
                     (append consts val-env)
                     ref-env)
                    (svar-override-keys-check-override-envs
                     vars test-env val-env ref-env)))
    :hints(("Goal" :in-theory (enable svar-override-keys-check-override-envs)
            :induct (svar-override-keys-check-override-envs
                     vars test-env val-env ref-env))))

  (defthm svar-override-keys-check-override-envlists-of-svtv-cycle-fsm-inputs
    (implies (and (svtv-cyclephaselist-unique-i/o-phase phases)
                  (svarlist-override-p (svtv-cyclephaselist-keys phases) nil))
             (equal (svar-override-keys-check-override-envlists
                     vars
                     (svtv-cycle-fsm-inputs test-env phases)
                     (svtv-cycle-fsm-inputs val-env phases)
                     ref-envs)
                    (svar-override-keys-check-override-envs
                     vars test-env val-env
                     (nth (svtv-cycle-output-phase phases) ref-envs))))
    :hints (("goal" :induct (ind phases ref-envs)
             :in-theory (enable svtv-cycle-fsm-inputs
                                svtv-cycle-output-phase
                                svtv-cycle-step-fsm-inputs
                                svtv-cyclephaselist-keys
                                svar-override-keys-check-override-envlists
                                svtv-cyclephaselist-unique-i/o-phase
                                svar-override-keys-check-override-envs-by-witness))))

  ;; (defthm svar-override-keys-check-override-envlists-of-svtv-cycle-fsm-inputs-no-vals
  ;;   (implies (and (svtv-cyclephaselist-unique-i/o-phase phases)
  ;;                 (svarlist-override-p (svtv-cyclephaselist-keys phases) nil))
  ;;            (equal (svar-override-keys-check-override-envlists
  ;;                    vars
  ;;                    (svtv-cycle-fsm-inputs test-env phases)
  ;;                    nil
  ;;                    ref-envs)
  ;;                   (svar-override-keys-check-override-envs
  ;;                    vars test-env nil
  ;;                    (nth (svtv-cycle-output-phase phases) ref-envs))))
  ;;   :hints (("goal" :induct (ind phases ref-envs)
  ;;            :in-theory (enable svtv-cycle-fsm-inputs
  ;;                               svtv-cycle-output-phase
  ;;                                     svtv-cycle-step-fsm-inputs
  ;;                                     svtv-cyclephaselist-keys
  ;;                                     svar-override-keys-check-override-envlists
  ;;                                     svtv-cyclephaselist-unique-i/o-phase))))

  (defthm svar-override-keys-check-override-envlists-of-svtv-cycle-fsm-inputs-nil-vals
    (implies (and (svtv-cyclephaselist-unique-i/o-phase phases)
                  (svarlist-override-p (svtv-cyclephaselist-keys phases) nil))
             (equal (svar-override-keys-check-override-envlists
                     vars
                     (svtv-cycle-fsm-inputs test-env phases)
                     (repeat (len phases) nil)
                     ref-envs)
                    (svar-override-keys-check-override-envs
                     vars test-env nil
                     (nth (svtv-cycle-output-phase phases) ref-envs))))
    :hints (("goal" :induct (ind phases ref-envs)
             :in-theory (enable svtv-cycle-fsm-inputs
                                svtv-cycle-output-phase
                                repeat
                                svtv-cycle-step-fsm-inputs
                                svtv-cyclephaselist-keys
                                svar-override-keys-check-override-envlists
                                svtv-cyclephaselist-unique-i/o-phase
                                svar-override-keys-check-override-envs-by-witness)))))



(encapsulate nil
  (local (defun ind (phases test-envs val-envs ref-envs)
           (if (atom test-envs)
               (list val-envs ref-envs)
             (ind phases (cdr test-envs) (cdr val-envs)
                  (nthcdr (max 1 (len phases)) ref-envs)))))

  (local (defthm svar-override-keys-check-override-envlists-of-append
           (equal (svar-override-keys-check-override-envlists
                   vars (append test-envs1 test-envs2)
                   val-envs ref-envs)
                  (and (svar-override-keys-check-override-envlists
                        vars test-envs1
                        (take (len test-envs1) val-envs)
                        (take (len test-envs1) ref-envs))
                       (svar-override-keys-check-override-envlists
                        vars test-envs2
                        (nthcdr (len test-envs1) val-envs)
                        (nthcdr (len test-envs1) ref-envs))))
           :hints(("Goal" :in-theory (e/d (svar-override-keys-check-override-envlists
                                           take)
                                          (svar-override-keys-check-override-envs-by-witness))
                   :induct (svar-override-keys-check-override-envlists
                            vars test-envs1 val-envs ref-envs)))))

  (local (defthm take-of-append
           (implies (equal (nfix n) (len x))
                    (equal (take n (append x y))
                           (true-list-fix x)))
           :hints(("Goal" :induct (take n x)))))

  (local (defthm nthcdr-of-append
           (implies (equal (nfix n) (len x))
                    (equal (nthcdr n (append x y))
                           y))
           :hints(("Goal" :induct (nthcdr n x)))))
  
  (defthm svar-override-keys-check-override-envlists-of-svtv-cycle-run-fsm-inputs
    (implies (and (svtv-cyclephaselist-unique-i/o-phase phases)
                  (svarlist-override-p (svtv-cyclephaselist-keys phases) nil))
             (equal (svar-override-keys-check-override-envlists
                     vars
                     (svtv-cycle-run-fsm-inputs test-envs phases)
                     (svtv-cycle-run-fsm-inputs val-envs phases)
                     ref-envs)
                    (svar-override-keys-check-override-envlists
                     vars test-envs val-envs
                     (svex-envlist-phase-outputs-extract-cycle-outputs phases ref-envs))))
    :hints(("Goal" :in-theory (e/d ; svex-envlist-phase-outputs-extract-cycle-outputs
                               (svar-override-keys-check-override-envlists
                                svtv-cycle-run-fsm-inputs)
                               (svar-override-keys-check-override-envs-by-witness))
            :expand ((svex-envlist-phase-outputs-extract-cycle-outputs phases ref-envs)
                     (svex-envlist-phase-outputs-extract-cycle-outputs phases nil))
            :induct (ind phases test-envs val-envs ref-envs)))))


(defthm consp-of-svtv-cyclephaselist-remove-constants
  (equal (consp (svtv-cyclephaselist-remove-constants phases))
         (consp phases))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-remove-constants))))

(defthm len-of-svtv-cyclephaselist-remove-constants
  (equal (len (svtv-cyclephaselist-remove-constants phases))
         (len phases))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-remove-constants))))

(defthm svex-envlist-phase-outputs-extract-cycle-outputs-of-remove-constants
  (equal (svex-envlist-phase-outputs-extract-cycle-outputs
          (svtv-cyclephaselist-remove-constants phases) x)
         (svex-envlist-phase-outputs-extract-cycle-outputs phases x))
  :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs)
          :induct (svex-envlist-phase-outputs-extract-cycle-outputs phases x)
          :expand ((:free (phases) (svex-envlist-phase-outputs-extract-cycle-outputs phases x))) )))





(defthm consp-of-svtv-name-lhs-map-eval-list
  (equal (consp (svtv-name-lhs-map-eval-list namemap envs))
         (consp envs))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-list))))


(encapsulate
  nil
  (local
   (defthm svtv-name-lhs-map-eval-list-under-iff
     (iff (svtv-name-lhs-map-eval-list namemap envs)
          (consp envs))
     :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-list)))))

  (local (defthm consp-of-svex-envlist-phase-outputs-extract-cycle-outputs
           (equal (consp (svex-envlist-phase-outputs-extract-cycle-outputs phases envs))
                  (consp envs))
           :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs)))))

  
  (local (defthm mod-0-when-less
           (implies (and (natp x) (natp y)
                         (< x y))
                    (equal (equal 0 (mod x y))
                           (equal x 0)))
           :hints (("goal" :in-theory (e/d (acl2::mod-redef) (mod))))))
          

  (local (defthm nthcdr-of-svtv-name-lhs-map-eval-list
           (equal (nthcdr n (svtv-name-lhs-map-eval-list namemap envs))
                  (svtv-name-lhs-map-eval-list namemap (nthcdr n envs)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-list)))))

  
  (defthm svex-envlist-phase-outputs-extract-cycle-outputs-of-svtv-name-lhs-map-eval-list
    (implies (and (equal 0 (mod (len envs) (len phases)))
                  (svtv-cyclephaselist-has-outputs-captured phases))
             (equal (svex-envlist-phase-outputs-extract-cycle-outputs phases (svtv-name-lhs-map-eval-list namemap envs))
                    (svtv-name-lhs-map-eval-list namemap (svex-envlist-phase-outputs-extract-cycle-outputs phases envs))))
    :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs
                                      svtv-name-lhs-map-eval-list
                                      acl2::mod-redef)
            :induct (svex-envlist-phase-outputs-extract-cycle-outputs phases envs)
            :expand ((svex-envlist-phase-outputs-extract-cycle-outputs phases
                                                                       (svtv-name-lhs-map-eval-list namemap envs)))))))




(define svex-env-lookuplist ((keys svarlist-p)
                             (env svex-env-p))
  :returns (vals 4veclist-p)
  (if (atom keys)
      nil
    (cons (svex-env-lookup (car keys) env)
          (svex-env-lookuplist (cdr keys) env))))


(define 4veclist-override-values-ok-<<= ((tests 4veclist-p)
                                         (vals 4veclist-p)
                                         (refs 4veclist-p))
  :guard (and (eql (len tests) (len vals))
              (eql (len tests) (len refs)))
  (if (atom tests)
      t
    (and (4vec-override-values-ok-<<= (car tests) (car vals) (car refs))
         (4veclist-override-values-ok-<<= (cdr tests) (cdr vals) (cdr refs))))
  ///
  (defthmd svar-override-keys-check-override-envs-in-terms-of-4veclist-override-values-ok-<<=
    (equal (svar-override-keys-check-override-envs keys test-env val-env ref-env)
           (4veclist-override-values-ok-<<= (svex-env-lookuplist (svarlist-change-override keys :test) test-env)
                                            (svex-env-lookuplist (svarlist-change-override keys :val) val-env)
                                            (svex-env-lookuplist keys ref-env)))
    :hints(("Goal" :in-theory (enable svar-override-keys-check-override-envs
                                      svex-env-lookuplist
                                      svarlist-change-override)))))


(fty::deflist svtv-name-lhs-map-list :elt-type svtv-name-lhs-map :true-listp t)

(define svtv-name-lhs-map-inverse-list ((x svtv-name-lhs-map-list-p))
  :returns (invlist svtv-name-lhs-map-list-p)
  (if (atom x)
      nil
    (cons (b* (((mv ?collision inverse)
                (svtv-name-lhs-map-inverse (car x))))
            inverse)
          (svtv-name-lhs-map-inverse-list (cdr x)))))

(define svtv-name-lhs-map-extract-list ((keyslist svarlist-list-p)
                                        (x svtv-name-lhs-map-p))
  :returns (maplist svtv-name-lhs-map-list-p)
  (if (atom keyslist)
      nil
    (cons (acl2::fal-extract (Svarlist-fix (car keyslist)) (svtv-name-lhs-map-fix x))
          (svtv-name-lhs-map-extract-list (cdr keyslist) x))))


(define svtv-name-lhs-map-list-eval-x-envlist ((x svtv-name-lhs-map-list-p)
                                             (envs svex-envlist-p))
  :returns (evals svex-envlist-p)
  (if (atom x)
      nil
    (cons (svtv-name-lhs-map-eval-x (car x) (car envs))
          (svtv-name-lhs-map-list-eval-x-envlist (cdr x) (cdr envs)))))

(define svtv-name-lhs-map-list-keys-change-override ((x svtv-name-lhs-map-list-p)
                                                     (type svar-overridetype-p))
  :returns (new-x svtv-name-lhs-map-list-p)
  (if (atom x)
      nil
    (cons (svtv-name-lhs-map-keys-change-override (car x) type)
          (svtv-name-lhs-map-list-keys-change-override (cdr x) type))))




(defthm svtv-name-lhs-map-eval-x-of-keys-change-override
  (equal (svtv-name-lhs-map-eval-x (svtv-name-lhs-map-keys-change-override x type) env)
         (svex-env-keys-change-override (svtv-name-lhs-map-eval-x x env) type))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-x svtv-name-lhs-map-keys-change-override
                                    svex-env-keys-change-override))))


(defthm svtv-fsm-to-base-fsm-inputs-with-only-override-vals
  (equal (svtv-fsm-to-base-fsm-inputs
          (repeat len nil) override-vals nil namemap)
         (svex-envlist-keys-change-override
          (svtv-name-lhs-map-list-eval-x-envlist
           (fast-alistlist-clean
            (svtv-name-lhs-map-inverse-list
             (svtv-name-lhs-map-extract-list
              (svex-env-keys-list (take len override-vals))
              namemap)))
           override-vals)
          :val))
  :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs
                                    svex-env-keys-list
                                    take
                                    repeat
                                    svex-envlist-keys-change-override
                                    fast-alistlist-clean
                                    svtv-name-lhs-map-extract-list
                                    svtv-name-lhs-map-inverse-list
                                    svtv-name-lhs-map-list-eval-x-envlist
                                    (:i nthcdr)
                                    svtv-fsm-phase-inputs
                                    svtv-fsm-env-inversemap)
          :expand ((:free (x) (fal-extract nil x)))
          :induct (nthcdr len override-vals))))

(defthm svtv-fsm-to-base-fsm-inputs-with-only-override-tests
  (equal (svtv-fsm-to-base-fsm-inputs
          (repeat len nil) nil override-tests namemap)
         (svex-envlist-keys-change-override
          (svtv-name-lhs-map-list-eval-x-envlist
           (fast-alistlist-clean
            (svtv-name-lhs-map-inverse-list
             (svtv-name-lhs-map-extract-list
              (svex-env-keys-list (take len override-tests))
              namemap)))
           override-tests)
           :test))
  :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs
                                    svex-env-keys-list
                                    take
                                    repeat
                                    fast-alistlist-clean
                                    svex-envlist-keys-change-override
                                    svtv-name-lhs-map-extract-list
                                    svtv-name-lhs-map-inverse-list
                                    svtv-name-lhs-map-list-keys-change-override
                                    svtv-name-lhs-map-list-eval-x-envlist
                                    (:i nthcdr)
                                    svtv-fsm-phase-inputs
                                    svtv-fsm-env-inversemap)
          :expand ((:free (x) (fal-extract nil x)))
          :induct (nthcdr len override-tests))))
                                    
         
