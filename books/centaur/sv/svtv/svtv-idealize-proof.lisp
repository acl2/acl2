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

(include-book "svtv-idealize-defs")
(include-book "cycle-probe")
;; (include-book "centaur/misc/starlogic" :dir :system)
;; (include-book "centaur/meta/variable-free" :dir :system)
(local (include-book "../svex/alist-thms"))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/alists/fal-extract" :dir :system))
(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (include-book "centaur/bitops/floor-mod" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/alists/alist-equiv" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
  
(local (in-theory (disable mod floor ceiling)))

(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable acl2::alist-keys-member-hons-assoc-equal)))


(defcong svex-envlists-similar svex-envlists-similar (svtv-name-lhs-map-eval-list map envs) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))





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





;; (defsection svex-alist-invert

;;   ;; For reconstructing pipeline inputs from FSM inputs, it's useful to be able
;;   ;; to invert an svex alist whose expressions only contain variables and
;;   ;; constants -- i.e. map the variables in the values to the corresponding
;;   ;; keys.  This isn't exact wrt variables used more than once.
  
;;   (define svex-alist-quote/var-p ((x svex-alist-p))
;;     (if (atom x)
;;         t
;;       (and (or (not (mbt (and (consp (car x))
;;                               (svar-p (caar x)))))
;;                (not (svex-case (cdar x) :call)))
;;            (svex-alist-quote/var-p (Cdr x))))
;;     ///
;;     (local (in-theory (enable svex-alist-fix))))

;;   (define svex-alist-var-rlookup ((v svar-p) (x svex-alist-p))
;;     :returns (key (iff (svar-p key) key))
;;     (if (atom x)
;;         nil
;;       (if (and (mbt (and (consp (car x))
;;                          (svar-p (caar x))))
;;                (svex-case (cdar x) :var)
;;                (equal (svar-fix v) (svex-var->name (cdar x))))
;;           (caar x)
;;         (svex-alist-var-rlookup v (cdr x))))
;;     ///
;;     ;; (local (in-theory (disable acl2::consp-under-iff-when-true-listp
;;     ;;                            acl2::consp-of-car-when-alistp
;;     ;;                            ryl::consp-when-member-equal-of-mod-uops-map-p
;;     ;;                            ryl::consp-when-member-equal-of-mod-owner-map-p
;;     ;;                            svar-p-when-member-equal-of-svarlist-p
;;     ;;                            svarlist-p-when-subsetp-equal)))
;;     (local (in-theory (disable (:d svex-alist-var-rlookup))))
;;     (defret lookup-of-<fn>
;;       (implies (and key
;;                     (no-duplicatesp-equal (svex-alist-keys x)))
;;                (equal (svex-lookup key x) (svex-var v)))
;;       :hints(("Goal" :in-theory (enable svex-lookup-of-cons)
;;               :induct <call>
;;               :expand ((svex-alist-keys x)
;;                        <call>))))

;;     (local (defthm sfix-of-singleton
;;              (Equal (sfix (list x))
;;                     (list x))
;;              :hints(("Goal" :in-theory (enable sfix empty setp)))))
  
;;     (defret <fn>-under-iff-when-quote/var-p
;;       (implies (svex-alist-quote/var-p x)
;;                (iff (svex-alist-var-rlookup v x)
;;                     (member-equal (svar-fix v) (svex-alist-vars x))))
;;       :hints(("Goal" 
;;               :induct <call>
;;               :expand ((svex-alist-vars x)
;;                        (svex-alist-quote/var-p x)
;;                        (svex-vars (cdar x))
;;                        <call>))))
    
;;     (local (in-theory (enable svex-alist-fix))))



;;   (define svex-alist-invert ((x svex-alist-p))
;;     :returns (new-x svex-alist-p)
;;     (if (atom x)
;;         nil
;;       (if (and (mbt (and (consp (car x))
;;                          (svar-p (caar x))))
;;                (svex-case (cdar x) :var))
;;           (cons (cons (svex-var->name (cdar x)) (svex-var (caar x)))
;;                 (svex-alist-invert (cdr x)))
;;         (svex-alist-invert (cdr x))))
;;     ///
;;     (local (Defthm svex-eval-when-var
;;              (implies (svex-case x :var)
;;                       (equal (svex-eval x env) (svex-env-lookup (svex-var->name x) env)))
;;              :hints(("Goal" :in-theory (enable svex-eval)))))

;;     (local (Defthm svex-eval-when-quote
;;              (implies (svex-case x :quote)
;;                       (equal (svex-eval x env) (svex-quote->val x)))
;;              :hints(("Goal" :in-theory (enable svex-eval)))))

;;     (defret svex-lookup-of-<fn>
;;       (equal (svex-lookup v new-x)
;;              (let ((key (svex-alist-var-rlookup v x)))
;;                (and key (svex-var key))))
;;       :hints(("Goal" :in-theory (enable svex-alist-var-rlookup
;;                                         svex-lookup-of-cons))))
  
;;     (defret lookup-in-eval-of-svex-alist-invert
;;       (implies (and (svex-alist-quote/var-p x)
;;                     (no-duplicatesp-equal (svex-alist-keys x)))
;;                (equal (svex-env-lookup var (svex-alist-eval new-x (svex-alist-eval x env)))
;;                       (if (member-equal (svar-fix var) (svex-alist-vars x))
;;                           (svex-env-lookup var env)
;;                         (4vec-x))))
;;       :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons-split
;;                                         svex-alist-eval
;;                                         svex-alist-keys
;;                                         svex-alist-vars
;;                                         svex-lookup-of-cons
;;                                         svex-alist-quote/var-p))))



;;     (defret eval-of-svex-alist-invert
;;       (implies (and (svex-alist-quote/var-p x)
;;                     (no-duplicatesp-equal (svex-alist-keys x)))
;;                (svex-envs-equivalent (svex-alist-eval new-x (svex-alist-eval x env))
;;                                      (svex-env-extract (svex-alist-vars x) env)))
;;       :hints(("Goal" :in-theory (enable svex-envs-equivalent))))
  
;;     (local (defthm svex-lookup-of-atom
;;              (implies (atom x)
;;                       (equal (svex-lookup v x) nil))
;;              :hints(("Goal" :in-theory (enable svex-lookup)))))
  
;;     ;; (local (defthm svex-kind-of-lookup-when-svex-alist-quote/var-p
;;     ;;          (implies (svex-alist-quote/var-p x)
;;     ;;                   (not (equal (svex-kind (svex-lookup v x)) :call)))
;;     ;;          :hints(("Goal" :in-theory (enable svex-alist-quote/var-p
;;     ;;                                            svex-lookup-of-cons)
;;     ;;                  :induct t))))

;;     (local (defthm name-of-svex-lookup-member-svex-alist-vars
;;              (implies (svex-case (svex-lookup v x) :var)
;;                       (member-equal (svex-var->name (svex-lookup v x))
;;                                     (svex-alist-vars x)))
;;              :hints(("Goal" :in-theory (enable svex-alist-vars
;;                                                svex-lookup-of-cons)))))

;;     (local (defthm svex-kind-of-lookup-when-svex-alist-quote/var-p
;;              (implies (and (svex-alist-quote/var-p x)
;;                            (not (svex-case (svex-lookup v x) :var)))
;;                       (equal (svex-kind (svex-lookup v x)) :quote))
;;              :hints(("Goal" :in-theory (enable svex-alist-quote/var-p
;;                                                svex-lookup-of-cons)
;;                      :induct t))))
  
;;     (defret eval-of-svex-alist-invert-invert
;;       (implies (and (svex-alist-quote/var-p x)
;;                     (no-duplicatesp-equal (svex-alist-keys x)))
;;                (equal (svex-alist-eval x (svex-alist-eval new-x (svex-alist-eval x env)))
;;                       (svex-alist-eval x env))))

;;     (local (in-theory (enable svex-alist-fix)))))

;; (local (in-theory (disable hons-dups-p)))

;; (defsection svex-alistlist-invert

;;   ;; For reconstructing pipeline inputs from FSM inputs, it's useful to be able
;;   ;; to invert an svex alist whose expressions only contain variables and
;;   ;; constants -- i.e. map the variables in the values to the corresponding
;;   ;; keys.  This isn't exact wrt variables used more than once.
  
;;   (define svex-alistlist-quote/var-p ((x svex-alistlist-p))
;;     (if (atom x)
;;         t
;;       (and (svex-alist-quote/var-p (car x))
;;            (svex-alistlist-quote/var-p (cdr x)))))


;;   (define svex-alistlist-no-duplicate-keys-p ((x svex-alistlist-p))
;;     (if (atom x)
;;         t
;;       (and (not (acl2::hons-dups-p (svex-alist-keys (car x))))
;;            (svex-alistlist-no-duplicate-keys-p (cdr x))))
;;     ///
;;     (local (in-theory (enable svex-alistlist-p))))
  

;;   (define svex-alistlist-invert ((x svex-alistlist-p))
;;     :returns (new-x svex-alistlist-p)
;;     (if (atom x)
;;         nil
;;       (cons (svex-alist-invert (car x))
;;             (svex-alistlist-invert (cdr x))))))


;; (define svex-alist-all-xes ((x svex-alist-p))
;;   (if (atom x)
;;       t
;;     (and (or (not (mbt (and (consp (car x))
;;                             (svar-p (caar x)))))
;;              (svex-equiv (cdar x) (svex-x)))
;;          (svex-alist-all-xes (cdr x))))
;;   ///
;;   (local (defthm svex-lookup-when-svex-alist-all-xes
;;            (implies (and (svex-alist-all-xes x)
;;                          (svex-lookup k x))
;;                     (equal (svex-lookup k x) (svex-x)))
;;            :hints(("Goal" :in-theory (enable svex-lookup-redef)))))
;;   (defthmd svex-alist-all-xes-implies-bottom
;;     (implies (svex-alist-all-xes x)
;;              (svex-env-<<= (svex-alist-eval x env) any))
;;     :hints(("Goal" :in-theory (enable svex-env-<<=))))

;;   (defthmd svex-alist-all-xes-implies-eval-similar-nil
;;     (implies (svex-alist-all-xes x)
;;              (svex-envs-similar (svex-alist-eval x env) nil))
;;     :hints(("Goal" :in-theory (enable svex-envs-similar))))

;;   (local (in-theory (enable svex-alist-fix))))






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

  (defthm svex-env-remove-override-vars-when-non-override
    (implies (and (svarlist-override-p remkeys :val)
                  (svarlist-override-p (alist-keys (svex-env-fix x)) nil))
             (equal (svex-env-removekeys remkeys x)
                    (svex-env-fix x)))
    :hints(("Goal" :in-theory (enable svex-env-removekeys
                                      svex-env-fix
                                      alist-keys
                                      svarlist-override-p))))

  (defthm svex-env-remove-override-tests-when-non-override
    (implies (and (svarlist-override-p remkeys :test)
                  (svarlist-override-p (alist-keys (svex-env-fix x)) nil))
             (equal (svex-env-removekeys remkeys x)
                    (svex-env-fix x)))
    :hints(("Goal" :in-theory (enable svex-env-removekeys
                                      svex-env-fix
                                      alist-keys
                                      svarlist-override-p))))

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
                  (bind-free (prog2$ (cw "keys: ~x0~%" keys)
                                     (case-match keys
                                       (('svarlist-change-override & key-type)
                                        `((key-type . ,key-type)))
                                       (& nil)))
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


(defthm alist-keys-of-svex-env-keys-change-override
  (equal (alist-keys (svex-env-keys-change-override x type))
         (svarlist-change-override (alist-keys (svex-env-fix x)) type))
  :hints(("Goal" :in-theory (enable svarlist-change-override svex-env-keys-change-override
                                    svex-env-fix alist-keys))))

;; ;; Need to change this to take only the override-val/override-test keys of the namemap!
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








;; Propagating svar-override-triplelist-envlists-ok-<<= through svtv-cycle-run-fsm-inputs

;; (local (defun svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs-when-no-i/o-ind (phases ref-envs)
;;          (if (atom phases)
;;              ref-envs
;;            (svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs-when-no-i/o-ind
;;             (Cdr phases) (cdr ref-envs)))))


(local (defthm svex-env-lookup-of-override-test-var-when-no-override-keys
         (implies (and (svar-override-p key :test)
                       (svarlist-override-p (alist-keys (svex-env-fix env)) nil))
                  (equal (svex-env-lookup key env) (4vec-x)))
         :hints(("Goal" :in-theory (enable svex-env-lookup
                                           svarlist-override-p
                                           svex-env-fix
                                           alist-keys
                                           svar-override-p)))))

;; (defthm svar-override-triplelist-env-ok-<<=-when-no-override-keys
;;   (implies (and (svarlist-override-p (alist-keys (svex-env-fix override-env)) nil)
;;                 (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
;;                 (svarlist-override-p (svar-override-triplelist->valvars triples) :val))
;;            (svar-override-triplelist-env-ok-<<= triples override-env ref-env))
;;   :hints(("Goal" :in-theory (enable svar-override-triplelist-env-ok-<<=
;;                                     svar-override-triplelist->valvars
;;                                     svar-override-triplelist->testvars
;;                                     svarlist-override-p))))

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

;; (defthm svar-override-triplelist-env-ok-<<=-of-append-when-no-override-keys
;;   (implies (and (svarlist-override-p (alist-keys (svex-env-fix env1)) nil)
;;                 (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
;;                 (svarlist-override-p (svar-override-triplelist->valvars triples) :val))
;;            (equal (svar-override-triplelist-env-ok-<<= triples (append env1 override-env) ref-env)
;;                   (svar-override-triplelist-env-ok-<<= triples override-env ref-env)))
;;   :hints(("Goal" :in-theory (enable svar-override-triplelist-env-ok-<<=
;;                                     svar-override-triplelist->valvars
;;                                     svar-override-triplelist->testvars
;;                                     svarlist-override-p))))

;; (defthm svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs-when-no-i/o
;;   (implies (and (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
;;                 (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
;;                 (svarlist-override-p (svar-override-triplelist->valvars triples) :val)
;;                 (svtv-cyclephaselist-no-i/o-phase phases))
;;            (equal (svar-override-triplelist-envlists-ok-<<=
;;                    triples (svtv-cycle-fsm-inputs ins phases) ref-envs)
;;                   t))
;;   :hints(("Goal" :in-theory (enable svtv-cyclephaselist-no-i/o-phase
;;                                     svtv-cycle-fsm-inputs
;;                                     svtv-cyclephaselist-keys
;;                                     svar-override-triplelist-envlists-ok-<<=
;;                                     svtv-cycle-step-fsm-inputs)
;;           :induct (svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs-when-no-i/o-ind
;;                    phases ref-envs))))


(local (defthm svtv-cyclephaselist-has-outputs-captured-when-unique-i/o
         (implies (svtv-cyclephaselist-unique-i/o-phase phases)
                  (svtv-cyclephaselist-has-outputs-captured phases))
         :hints(("Goal" :in-theory (enable svtv-cyclephaselist-has-outputs-captured
                                           svtv-cyclephaselist-unique-i/o-phase)))))

;; (defthm svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs
;;   (implies (and (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
;;                 (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
;;                 (svarlist-override-p (svar-override-triplelist->valvars triples) :val)
;;                 (svtv-cyclephaselist-unique-i/o-phase phases))
;;            (equal (svar-override-triplelist-envlists-ok-<<=
;;                    triples (svtv-cycle-fsm-inputs ins phases) ref-envs)
;;                   (svar-override-triplelist-env-ok-<<=
;;                    triples ins (nth (svtv-cycle-output-phase phases) ref-envs))))
;;   :hints(("Goal" :in-theory (enable svtv-cyclephaselist-keys
;;                                     svtv-cyclephaselist-unique-i/o-phase
;;                                     svtv-cycle-fsm-inputs
;;                                     svtv-cycle-output-phase
;;                                     svar-override-triplelist-envlists-ok-<<=
;;                                     svtv-cycle-step-fsm-inputs)
;;           :induct (svar-override-triple-envlists-ok-of-svtv-cycle-fsm-inputs-when-no-i/o-ind
;;                    phases ref-envs))))








 


;; (local (defun svar-override-triplelist-envlists-ok-<<=-of-append-ind (x ref-envs)
;;          (if (atom x)
;;              ref-envs
;;            (svar-override-triplelist-envlists-ok-<<=-of-append-ind (cdr x) (cdr ref-envs)))))

;; (defthm svar-override-triplelist-envlists-ok-<<=-of-append
;;   (equal (svar-override-triplelist-envlists-ok-<<= triples (append x y) ref-envs)
;;          (and (svar-override-triplelist-envlists-ok-<<= triples x (take (len x) ref-envs))
;;               (svar-override-triplelist-envlists-ok-<<= triples y (nthcdr (len x) ref-envs))))
;;   :hints(("Goal" :in-theory (enable svar-override-triplelist-envlists-ok-<<=)
;;           :induct (svar-override-triplelist-envlists-ok-<<=-of-append-ind x ref-envs))))


;; (local (defun svar-override-triple-envlists-ok-of-svtv-cycle-run-fsm-inputs-ind (phases ins ref-envs)
;;          (if (atom ins)
;;              (list phases ref-envs)
;;            (svar-override-triple-envlists-ok-of-svtv-cycle-run-fsm-inputs-ind phases (cdr ins)
;;                                                                               (nthcdr (if (consp phases) (len phases) 1)
;;                                                                                       ref-envs)))))

(defthm svtv-cyclephaselist-unique-i/o-phase-when-atom
  (implies (atom x)
           (not (svtv-cyclephaselist-unique-i/o-phase x)))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-unique-i/o-phase))))

(local
 (defthmd svtv-cyclephaselist-unique-i/o-phase-implies-natp-output-phase
   (implies (svtv-cyclephaselist-unique-i/o-phase x)
            (natp (svtv-cycle-output-phase x)))
   :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                     svtv-cyclephaselist-unique-i/o-phase)))
   :rule-classes :type-prescription))

(defthm svtv-cycle-output-phase-bound
  (implies (svtv-cycle-output-phase phases)
           (< (svtv-cycle-output-phase phases) (len phases)))
  :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                    svtv-cyclephaselist-has-outputs-captured)))
  :rule-classes :linear)

;; (defthm svar-override-triple-envlists-ok-of-svtv-cycle-run-fsm-inputs
;;   (implies (and (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
;;                 (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
;;                 (svarlist-override-p (svar-override-triplelist->valvars triples) :val)
;;                 (svtv-cyclephaselist-unique-i/o-phase phases))
;;            (equal (svar-override-triplelist-envlists-ok-<<=
;;                    triples (svtv-cycle-run-fsm-inputs ins phases) ref-envs)
;;                   (svar-override-triplelist-envlists-ok-<<=
;;                    triples ins (svex-envlist-phase-outputs-extract-cycle-outputs
;;                                 phases ref-envs))))
;;   :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs
;;                                     svex-envlist-phase-outputs-extract-cycle-outputs
;;                                     svar-override-triplelist-envlists-ok-<<=)
;;           :induct (svar-override-triple-envlists-ok-of-svtv-cycle-run-fsm-inputs-ind
;;                    phases ins ref-envs))))






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





;; (defthm svar-override-triplelist-env-ok-<<=-implies-override-values-ok-of-member
;;   (implies (and (svar-override-triplelist-env-ok-<<= x override-env ref-env)
;;                 (member-equal trip (svar-override-triplelist-fix x)))
;;            (b* (((svar-override-triple trip)))
;;              (4vec-override-values-ok-<<= (svex-env-lookup trip.testvar override-env)
;;                                           (svex-env-lookup trip.valvar override-env)
;;                                           (svex-env-lookup trip.refvar ref-env))))
;;   :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=
;;                                     svar-override-triplelist-env-ok-<<=
;;                                     svar-override-triplelist-fix))))

;; (defthm triple-when-member-of-svarlist-to-override-triples
;;   (implies (svarlist-override-p vars nil)
;;            (iff (member-equal trip (svarlist-to-override-triples vars))
;;                 (and (svar-override-triple-p trip)
;;                      (b* (((svar-override-triple trip)))
;;                        (and (member-equal trip.refvar (svarlist-fix vars))
;;                             (equal trip.valvar (svar-change-override trip.refvar :val))
;;                             (equal trip.testvar (svar-change-override trip.refvar :test)))))))
;;   :hints(("Goal" :in-theory (e/d (svarlist-to-override-triples
;;                                     svar-change-override
;;                                     svarlist-fix
;;                                     svarlist-override-p
;;                                     svar-override-p)
;;                                  (member-equal))
;;           :induct (len vars))))

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
    :hints(("Goal" :in-theory (enable svtv-cycle-output-phase))))

  (defret svtv-cyclephaselist-keys-of-<fn>
    (equal (svtv-cyclephaselist-keys new-x) nil)
    :hints(("Goal" :in-theory (enable svtv-cyclephaselist-keys)))))
  


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





(defcong svex-envlists-similar equal (svex-envlist-<<= x y) 1
  :hints (("goal" :cases ((svex-envlist-<<= x y))
           :in-theory (enable svex-envlist-<<=))))

(defcong svex-envlists-similar equal (svex-envlist-<<= x y) 2
  :hints (("goal" :cases ((svex-envlist-<<= x y))
           :in-theory (enable svex-envlist-<<=))))





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

  (local (defthm svtv-cycle-output-phase-when-not-outputs-captured
           (implies (not (svtv-cyclephaselist-has-outputs-captured phases))
                    (not (svtv-cycle-output-phase phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                             svtv-cyclephaselist-has-outputs-captured)))))
  
  (defthm svex-envlist-phase-outputs-extract-cycle-outputs-monotonic
    (implies (svex-envlist-<<= x y)
             (svex-envlist-<<= (svex-envlist-phase-outputs-extract-cycle-outputs phases x)
                               (svex-envlist-phase-outputs-extract-cycle-outputs phases y)))
    :hints(("Goal" :in-theory (e/d (svex-envlist-phase-outputs-extract-cycle-outputs)
                                   (SVEX-ENV-<<=-NIL-MEANS-SIMILAR-TO-NIL))
            :induct (ind phases x y)
            :expand ((svex-envlist-phase-outputs-extract-cycle-outputs phases x)
                     (svex-envlist-phase-outputs-extract-cycle-outputs phases y)
                     (:free (a b c) (svex-envlist-<<= (cons a b) c))
                     (:free (y) (svex-envlist-<<= nil y))))
           (and stable-under-simplificationp
                '(:cases ((svtv-cyclephaselist-has-outputs-captured phases)))))))




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
                (<= (len x) (len y)))
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
  

  (local (defthm svex-envlist-phase-outputs-extract-cycle-outputs-of-atom
           (implies (atom envs)
                    (equal (svex-envlist-phase-outputs-extract-cycle-outputs phases envs) nil))
           :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs)))))
  
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
                                svtv-cycle-run-fsm-inputs
                                svtv-cyclephaselist-unique-i/o-phase-implies-natp-output-phase)
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







(define svtv-name-lhs-map-list-eval-x-envlist ((x svtv-name-lhs-map-list-p)
                                             (envs svex-envlist-p))
  :returns (evals svex-envlist-p)
  (if (atom x)
      nil
    (cons (svtv-name-lhs-map-eval-x (car x) (car envs))
          (svtv-name-lhs-map-list-eval-x-envlist (cdr x) (cdr envs)))))


(define svtv-name-lhs-map-list-eval-envlist ((x svtv-name-lhs-map-list-p)
                                             (envs svex-envlist-p))
  :returns (evals svex-envlist-p)
  (if (atom x)
      nil
    (cons (svtv-name-lhs-map-eval (car x) (car envs))
          (svtv-name-lhs-map-list-eval-envlist (cdr x) (cdr envs)))))

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


(defthm svtv-fsm-to-base-fsm-inputs-with-only-override-vals-lemma
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


(defthm svtv-fsm-to-base-fsm-inputs-with-only-override-vals
  (implies (and (syntaxp (quotep null-inputs))
                (equal null-inputs (repeat (len null-inputs) nil)))
           (equal (svtv-fsm-to-base-fsm-inputs
                   null-inputs override-vals nil namemap)
                  (svex-envlist-keys-change-override
                   (svtv-name-lhs-map-list-eval-x-envlist
                    (fast-alistlist-clean
                     (svtv-name-lhs-map-inverse-list
                      (svtv-name-lhs-map-extract-list
                       (svex-env-keys-list (take (len null-inputs) override-vals))
                       namemap)))
                    override-vals)
                   :val))))

(defthm svtv-fsm-to-base-fsm-inputs-with-only-override-tests-lemma
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


(defthm svtv-fsm-to-base-fsm-inputs-with-only-override-tests
  (implies (and (syntaxp (quotep null-inputs))
                (equal null-inputs (repeat (len null-inputs) nil)))
           (equal (svtv-fsm-to-base-fsm-inputs
                   null-inputs nil override-tests namemap)
                  (svex-envlist-keys-change-override
                   (svtv-name-lhs-map-list-eval-x-envlist
                    (fast-alistlist-clean
                     (svtv-name-lhs-map-inverse-list
                      (svtv-name-lhs-map-extract-list
                       (svex-env-keys-list (take (len null-inputs) override-tests))
                       namemap)))
                    override-tests)
                   :test))))
                                    
         
(defthmd take-of-svex-alistlist-eval
  (equal (take n (svex-alistlist-eval x env))
         (svex-alistlist-eval (take n x) env))
  :hints(("Goal" :in-theory (e/d (take svex-alistlist-eval)
                                 (acl2::take-of-too-many
                                  acl2::take-when-atom))
          :induct (take n x)
          :expand ((svex-alist-eval nil env)))))


(defthmd svex-alist-keys-list-of-take
  (equal (svex-alist-keys-list (take n x))
         (take n (svex-alist-keys-list x)))
  :hints(("Goal" :in-theory (e/d (take svex-alist-keys-list)
                                 (acl2::take-of-too-many
                                  acl2::take-when-atom))
          :induct (take n x))))





(define svar-override-keys-check-envs ((keys svarlist-p)
                                       (test-env svex-env-p)
                                       (val-env svex-env-p)
                                       (ref-env svex-env-p))
  :returns (ok)
  (if (atom keys)
      t
    (and (4vec-override-values-ok-<<= (svex-env-lookup (car keys) test-env)
                                      (svex-env-lookup (car keys) val-env)
                                      (svex-env-lookup (car keys) ref-env))
         (svar-override-keys-check-envs (cdr keys) test-env val-env ref-env)))
  ///
  (defthm svar-override-keys-check-override-envs-of-env-keys-change-override
    (implies (and (svarlist-override-p (alist-keys (svex-env-fix test-env)) nil)
                  (svarlist-override-p (alist-keys (svex-env-fix val-env)) nil)
                  (svarlist-override-p keys nil))
             (equal (svar-override-keys-check-override-envs
                     keys
                     (svex-env-keys-change-override test-env :test)
                     (svex-env-keys-change-override val-env :val)
                     ref-env)
                    (svar-override-keys-check-envs
                     keys test-env val-env ref-env)))
    :hints(("Goal" :in-theory (disable (:d svar-override-keys-check-envs))
            :induct (len keys)
            :expand ((svar-override-keys-check-envs keys test-env val-env ref-env)
                     (:free (test-env val-env ref-env)
                      (svar-override-keys-check-override-envs keys test-env val-env ref-env))
                     (svarlist-override-p keys nil)))))

  (defret <fn>-implies-when-member
    (implies (and ok
                  (member-equal (svar-fix var) (svarlist-fix keys)))
             (4vec-override-values-ok-<<= (svex-env-lookup var test-env)
                                          (svex-env-lookup var val-env)
                                          (svex-env-lookup var ref-env))))


  (defund svar-override-keys-check-envs-witness (keys test-env val-env ref-env)
    (if (atom keys)
        nil
      (if (4vec-override-values-ok-<<= (svex-env-lookup (car keys) test-env)
                                       (svex-env-lookup (car keys) val-env)
                                       (svex-env-lookup (car keys) ref-env))
          (svar-override-keys-check-envs-witness (cdr keys) test-env val-env ref-env)
        (svar-fix (car keys)))))

  (local (in-theory (enable svar-override-keys-check-envs-witness)))
  
  

  (defthmd svar-override-keys-check-envs-when-witness
    (implies (b* ((var (svar-override-keys-check-envs-witness keys test-env val-env ref-env)))
               (or (not (member-equal (svar-fix var) (svarlist-fix keys)))
                   (4vec-override-values-ok-<<= (svex-env-lookup var test-env)
                                                (svex-env-lookup var val-env)
                                                (svex-env-lookup var ref-env))))
             (svar-override-keys-check-envs keys test-env val-env ref-env)))

  (defthmd svar-override-keys-check-envs-by-witness
    (implies (acl2::rewriting-positive-literal `(svar-override-keys-check-envs ,keys ,test-env ,val-env ,ref-env))
             (equal (svar-override-keys-check-envs keys test-env val-env ref-env)
                    (b* ((var (svar-override-keys-check-envs-witness keys test-env val-env ref-env)))
               (or (not (member-equal (svar-fix var) (svarlist-fix keys)))
                   (4vec-override-values-ok-<<= (svex-env-lookup var test-env)
                                                (svex-env-lookup var val-env)
                                                (svex-env-lookup var ref-env)))))))

  (defcong set-equiv equal (svar-override-keys-check-envs keys test-env val-env ref-env) 1
    :hints (("goal" :cases ((svar-override-keys-check-envs keys test-env val-env ref-env)
                            (svar-override-keys-check-envs keys-equiv test-env val-env ref-env))
             :in-theory (enable svar-override-keys-check-envs-when-witness
                                svar-override-keys-check-envs-by-witness))))

  
  (defcong svex-envs-similar equal (svar-override-keys-check-envs keys test-env val-env ref-env) 2)
  (defcong svex-envs-similar equal (svar-override-keys-check-envs keys test-env val-env ref-env) 3)
  (defcong svex-envs-similar equal (svar-override-keys-check-envs keys test-env val-env ref-env) 4))


(define svex-envs-overrides-ok ((test-env svex-env-p)
                                (val-env svex-env-p)
                                (ref-env svex-env-p))
  :returns (ok)
  ;; This effectively universally quantifies over the keys checked in svar-override-keys-check-envs
  (svar-override-keys-check-envs (alist-keys (svex-env-fix val-env))
                                 test-env val-env ref-env)
  ///
  
  (defret <fn>-implies
    (implies ok
             (4vec-override-values-ok-<<= (svex-env-lookup var test-env)
                                          (svex-env-lookup var val-env)
                                          (svex-env-lookup var ref-env)))
    :hints (("goal" :cases ((member-equal (svar-fix var) (alist-keys (svex-env-fix val-env)))))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svex-env-boundp
                                    svex-env-lookup
                                    acl2::alist-keys-member-hons-assoc-equal))))))
  
  (defund svex-envs-overrides-ok-witness (test-env val-env ref-env)
    (svar-override-keys-check-envs-witness
     (alist-keys (svex-env-fix val-env)) test-env val-env ref-env))

  (local (in-theory (enable svex-envs-overrides-ok-witness)))

  (defthmd svex-envs-overrides-ok-when-witness
    (implies (b* ((var (svex-envs-overrides-ok-witness test-env val-env ref-env)))
               (4vec-override-values-ok-<<= (svex-env-lookup var test-env)
                                            (svex-env-lookup var val-env)
                                            (svex-env-lookup var ref-env)))
             (svex-envs-overrides-ok test-env val-env ref-env))
    :hints(("Goal" :in-theory (enable svar-override-keys-check-envs-when-witness))))

  (defthmd svex-envs-overrides-ok-by-witness
    (implies (acl2::rewriting-positive-literal `(svex-envs-overrides-ok ,test-env ,val-env ,ref-env))
             (equal (svex-envs-overrides-ok test-env val-env ref-env)
                    (b* ((var (svex-envs-overrides-ok-witness test-env val-env ref-env)))
                      (4vec-override-values-ok-<<= (svex-env-lookup var test-env)
                                                   (svex-env-lookup var val-env)
                                                   (svex-env-lookup var ref-env)))))
    :hints(("Goal" :in-theory (enable svar-override-keys-check-envs-by-witness)
            :cases ((svex-envs-overrides-ok test-env val-env ref-env)))))

  (local (in-theory (disable svex-envs-overrides-ok
                             svex-envs-overrides-ok-witness)))

    
  (defret svar-override-keys-check-envs-when-<fn>
    (implies ok
             (svar-override-keys-check-envs keys test-env val-env ref-env))
    :hints(("Goal" :in-theory (e/d (svar-override-keys-check-envs-by-witness)
                                   (<fn>)))))


  (local (defret <fn>-implies-free
           (implies (and ok
                         (equal (svex-env-lookup var test-env1)
                                (svex-env-lookup var test-env))
                         (equal (svex-env-lookup var val-env1)
                                (svex-env-lookup var val-env))
                         (equal (svex-env-lookup var ref-env1)
                                (svex-env-lookup var ref-env)))
                    (4vec-override-values-ok-<<= (svex-env-lookup var test-env1)
                                                 (svex-env-lookup var val-env1)
                                                 (svex-env-lookup var ref-env1)))))
  
  (defcong svex-envs-similar equal (svex-envs-overrides-ok test-env val-env ref-env) 1
    :hints (("goal" :cases ((svex-envs-overrides-ok test-env val-env ref-env)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-envs-overrides-ok-by-witness))))
    :otf-flg t)

  (defcong svex-envs-similar equal (svex-envs-overrides-ok test-env val-env ref-env) 2
    :hints (("goal" :cases ((svex-envs-overrides-ok test-env val-env ref-env)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-envs-overrides-ok-by-witness))))
    :otf-flg t)
  
  (defcong svex-envs-similar equal (svex-envs-overrides-ok test-env val-env ref-env) 3
    :hints (("goal" :cases ((svex-envs-overrides-ok test-env val-env ref-env)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-envs-overrides-ok-by-witness))))
    :otf-flg t)

  (defthm svex-envs-overrides-ok-empty-test-env
    (svex-envs-overrides-ok nil val-env ref-env)
    :hints(("Goal" :in-theory (enable svex-envs-overrides-ok-by-witness))))

  (defthm svex-envs-overrides-ok-empty-val-env
    (svex-envs-overrides-ok test-env nil ref-env)
    :hints(("Goal" :in-theory (enable svex-envs-overrides-ok-by-witness))))


  (defthm svex-envs-overrides-ok-of-svex-env-reduce
    (implies (subsetp-equal (intersection-equal (alist-keys (svex-env-fix test-env))
                                                (alist-keys (svex-env-fix val-env)))
                            (svarlist-fix keys))
             (iff (svex-envs-overrides-ok test-env val-env (svex-env-reduce keys ref-env))
                  (svex-envs-overrides-ok test-env val-env ref-env)))
    :hints(("Goal" :in-theory (enable svex-envs-overrides-ok-by-witness
                                      svex-env-lookup-when-not-boundp
                                      svex-env-boundp-iff-member-alist-keys))
           (and stable-under-simplificationp
                (b* ((call (acl2::find-call-lst 'svex-envs-overrides-ok-witness clause))
                     ((unless call) nil)
                     (ref-env (nth 3 call))
                     (other-ref-env (if (eq ref-env 'ref-env) '(svex-env-reduce keys ref-env) 'ref-env)))
                  `(:computed-hint-replacement
                    ('(:use ((:instance svex-envs-overrides-ok-implies (var key) (ref-env ,other-ref-env)))
                       :in-theory (e/d (svex-env-lookup-when-not-boundp
                                        svex-env-boundp-iff-member-alist-keys)
                                       (svex-envs-overrides-ok-implies
                                        svex-envs-overrides-ok-implies-free))))
                    :clause-processor (acl2::generalize-with-alist-cp clause '((,call . key))))))
           (acl2::set-reasoning))))



(define 4vec-<<=-badbit ((a 4vec-p) (b 4vec-p))
  :returns (badbit natp :rule-classes :type-prescription)
  :prepwork (  )
  (b* (((4vec a))
       ((4vec b))
       (vec (lognot (logior (logand (logeqv a.upper b.upper)
                                    (logeqv a.lower b.lower))
                            (logand a.upper (lognot a.lower))))))
    (bitops::trailing-0-count vec))
  ///
  (defthm 4vec-<<=-implies-bit-index
    (implies (and (4vec-<<= x y)
                  (not (equal (4vec-bit-index n x) (4vec-1x))))
             (equal (4vec-bit-index n y) (4vec-bit-index n x)))
    :hints(("Goal" :in-theory (enable 4vec-<<= 4vec-bit-index))
           (bitops::logbitp-reasoning)))

  (local (defthmd logbitp-of-trailing-0-count
           (equal (logbitp (bitops::trailing-0-count x) x)
                  (not (zip x)))
           :hints(("Goal" :in-theory (enable bitops::trailing-0-count-properties)))))
  
  (defretd 4vec-<<=-when-badbit
    (implies (or (equal (4vec-bit-index badbit a) (4vec-1x))
                 (equal (4vec-bit-index badbit a) (4vec-bit-index badbit b)))
             (4vec-<<= a b))
    :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-<<=)
            :use ((:instance logbitp-of-trailing-0-count
                   (x (b* (((4vec a))
                           ((4vec b))
                           (vec (lognot (logior (logand (logeqv a.upper b.upper)
                                                        (logeqv a.lower b.lower))
                                                (logand a.upper (lognot a.lower))))))
                        vec))))))))
     

(define 4vec-override-values-ok-<<=-badbit ((test 4vec-p)
                                            (val 4vec-p)
                                            (ref 4vec-p))
  :returns (badbit natp :rule-classes :type-prescription)
  (4vec-<<=-badbit (4vec-bit?! test val 0)
                   (4vec-bit?! test ref 0))
  ///
  (local (Defthm 4vec-bit-index-of-4vec-bit?!
           (equal (4vec-bit-index n (4vec-bit?! test then else))
                  (if (eql (4vec-bit-index n test) 1)
                      (4vec-bit-index n then)
                    (4vec-bit-index n else)))
           :hints(("Goal" :in-theory (enable 4vec-bit-index
                                             4vec-bit?!)))))
  
  (defthm 4vec-override-values-ok-<<=-implies-bit-index
    (implies (and (4vec-override-values-ok-<<= test val ref)
                  (equal 1 (4vec-bit-index n test))
                  (not (equal (4vec-1x) (4vec-bit-index n val))))
             (equal (4vec-bit-index n ref)
                    (4vec-bit-index n val)))
    :hints(("Goal" :in-theory (e/d (4vec-override-values-ok-<<=)
                                   (4vec-<<=-implies-bit-index))
            :use ((:instance 4vec-<<=-implies-bit-index
                   (x (4vec-bit?! test val 0))
                   (y (4vec-bit?! test ref 0)))))))


  (defretd 4vec-override-values-ok-<<=-when-badbit
    (implies (or (not (equal 1 (4vec-bit-index badbit test)))
                 (equal (4vec-1x) (4vec-bit-index badbit val))
                 (equal (4vec-bit-index badbit ref)
                        (4vec-bit-index badbit val)))
             (4vec-override-values-ok-<<= test val ref))
    :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=
                                      4vec-<<=-when-badbit))))

  (defretd 4vec-override-values-ok-<<=-by-badbit
    (implies (acl2::rewriting-positive-literal `(4vec-override-values-ok-<<= ,test ,val ,ref))
             (equal (4vec-override-values-ok-<<= test val ref)
                    (or (not (equal 1 (4vec-bit-index badbit test)))
                        (equal (4vec-1x) (4vec-bit-index badbit val))
                        (equal (4vec-bit-index badbit ref)
                               (4vec-bit-index badbit val)))))
    :hints(("Goal" :in-theory (e/d (4vec-override-values-ok-<<=-when-badbit)
                                   (4vec-override-values-ok-<<=-badbit))))))
    

(define lhbit-eval-x ((x lhbit-p)
                      (env svex-env-p))
  (lhbit-case x
    :z (4vec-1x)
    :var (4vec-bit-index x.idx (svex-env-lookup x.name env)))
  ///
  (local (defthm 4vec-bit-index-of-4vec-concat
           (implies (natp w)
                    (equal (4vec-bit-index n (4vec-concat (2vec w) x y))
                           (if (< (nfix n) w)
                               (4vec-bit-index n x)
                             (4vec-bit-index (- (nfix n) w) y))))
           :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-concat)))))

  (local (defthm 4vec-bit-index-of-4vec-rsh
           (implies (natp sh)
                    (equal (4vec-bit-index n (4vec-rsh (2vec sh) x))
                           (4vec-bit-index (+ (nfix n) sh) x)))
           :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-rsh 4vec-shift-core)))))

  (local (defthm 4vec-bit-index-of-x
           (equal (4vec-bit-index n (4vec-x))
                  (4vec-1x))
           :hints(("Goal" :in-theory (enable 4vec-bit-index)))))
  
  (defthm 4vec-bit-index-of-lhs-eval-x
    (equal (4vec-bit-index n (lhs-eval-x x env))
           (lhbit-eval-x (lhs-bitproj n x) env))
    :hints(("Goal" :in-theory (enable lhs-eval-x lhs-bitproj lhatom-bitproj lhatom-eval-x)))))


(define lhbit-eval-zero ((x lhbit-p)
                         (env svex-env-p))
  (lhbit-case x
    :z 0
    :var (4vec-bit-index x.idx (svex-env-lookup x.name env)))
  ///
  (local (defthm 4vec-bit-index-of-4vec-concat
           (implies (natp w)
                    (equal (4vec-bit-index n (4vec-concat (2vec w) x y))
                           (if (< (nfix n) w)
                               (4vec-bit-index n x)
                             (4vec-bit-index (- (nfix n) w) y))))
           :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-concat)))))

  (local (defthm 4vec-bit-index-of-4vec-rsh
           (implies (natp sh)
                    (equal (4vec-bit-index n (4vec-rsh (2vec sh) x))
                           (4vec-bit-index (+ (nfix n) sh) x)))
           :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-rsh 4vec-shift-core)))))

  (local (defthm 4vec-bit-index-of-0
           (equal (4vec-bit-index n 0)
                  0)
           :hints(("Goal" :in-theory (enable 4vec-bit-index)))))

  (defthm 4vec-bit-index-of-lhs-eval-zero
    (equal (4vec-bit-index n (lhs-eval-zero x env))
           (lhbit-eval-zero (lhs-bitproj n x) env))
    :hints(("Goal" :in-theory (enable lhs-eval-zero lhs-bitproj lhatom-bitproj lhatom-eval-zero)))))



  
(defsection svex-envs-overrides-ok-of-eval-inverse

  (defthm svex-env-lookup-of-svtv-name-lhs-map-eval
    (equal (svex-env-lookup v (svtv-name-lhs-map-eval namemap env))
           (b* ((look (hons-assoc-equal (svar-fix v) namemap)))
             (if look
                 (lhs-eval-zero (cdr look) env)
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval svex-env-lookup))))
  

  ;; (defthm svex-envs-overrides-ok-of-eval-inverse-lemma
  ;;   (implies (svex-envs-overrides-ok test-env val-env
  ;;                                    (svtv-name-lhs-map-eval namemap ref-env))
  ;;            (4vec-override-values-ok-<<=
  ;;             (svtv-name-lhs-map-var-inverse-eval-x v namemap test-env)
  ;;             (svtv-name-lhs-map-var-inverse-eval-x v namemap val-env)
  ;;             (svex-env-lookup v ref-env)))
  ;;   :hints (("goal" :induct (len namemap)
  ;;            :expand ((:free (env) (svtv-name-lhs-map-var-inverse-eval-x v namemap test-env))
  ;;                     (svtv-name-lhs-map-eval namemap ref-env)))))

  (local (in-theory (disable EVAL-SVTV-NAME-LHS-MAP-INVERSE-OF-LOOKUP-GEN)))

  (local (defthmd 4vec-override-values-ok-<<=-implies-bit-index-rev
           (implies (and (4vec-override-values-ok-<<= test val ref)
                         (equal 1 (4vec-bit-index n test))
                         (not (equal (4vec-1x) (4vec-bit-index n val))))
                    (equal (4vec-bit-index n val)
                           (4vec-bit-index n ref)))))
    
  
  (local
   (defthm svex-envs-overrides-ok-of-eval-inverse-lemma
     (implies (and (svex-envs-overrides-ok
                    test-env val-env
                    (svtv-name-lhs-map-eval namemap ref-env))
                   (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix namemap))))
              (4vec-override-values-ok-<<=
               (lhs-eval-x (cdr (hons-assoc-equal (svar-fix v) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) test-env)
               (lhs-eval-x (cdr (hons-assoc-equal (svar-fix v) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) val-env)
               (svex-env-lookup v ref-env)))
     :hints (("goal"
              :in-theory (enable 4vec-override-values-ok-<<=-by-badbit))
             (and stable-under-simplificationp
                  (let ((call (acl2::find-call-lst '4vec-override-values-ok-<<=-badbit clause)))
                    (and call
                         `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badbit)))))))
             (and stable-under-simplificationp
                  '(:use ((:instance
                           svex-envs-overrides-ok-implies
                           (ref-env (svtv-name-lhs-map-eval namemap ref-env))
                           (var (LHBIT-VAR->NAME
                                 (SVTV-NAME-LHS-MAP-VAR/IDX-FIND
                                  V badbit
                                  NAMEMAP)))))
                    :in-theory (e/d (lhbit-eval-x lhbit-eval-zero
                                                  4vec-override-values-ok-<<=-implies-bit-index-rev)
                                    (svex-envs-overrides-ok-implies
                                     4vec-override-values-ok-<<=-implies-bit-index
                                     )))))))

  
  (defthm svex-envs-overrides-ok-of-eval-inverse
    (implies (and (svex-envs-overrides-ok
                   test-env val-env
                   (svtv-name-lhs-map-eval namemap ref-env))
                  (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix namemap))))
             (svex-envs-overrides-ok
              (svtv-name-lhs-map-eval-x
               (mv-nth 1 (svtv-name-lhs-map-inverse namemap))
               test-env)
              (svtv-name-lhs-map-eval-x
               (mv-nth 1 (svtv-name-lhs-map-inverse namemap))
               val-env)
              ref-env))
    :hints(("Goal" :in-theory (e/d (svex-envs-overrides-ok-by-witness)
                                   (svex-envs-overrides-ok))))))

(local (in-theory (disable hons-dups-p)))

(define svtv-name-lhs-map-list-keys-no-dups ((x svtv-name-lhs-map-list-p))
  (if (atom x)
      t
    (and (mbe :logic (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix (car x))))
              :exec (not (hons-dups-p (alist-keys (svtv-name-lhs-map-fix (car x))))))
         (svtv-name-lhs-map-list-keys-no-dups (cdr x)))))


(define svex-envlists-overrides-ok ((test-envs svex-envlist-p)
                                    (val-envs svex-envlist-p)
                                    (ref-envs svex-envlist-p))
  :returns (ok)
  (if (atom test-envs)
      t
    (and (svex-envs-overrides-ok (car test-envs) (car val-envs) (car ref-envs))
         (svex-envlists-overrides-ok (cdr test-envs) (cdr val-envs) (cdr ref-envs))))
  ///
  (local (defthm svar-override-keys-check-override-envs-of-empty-vals
           (svar-override-keys-check-override-envs keys test-env nil ref-env)
           :hints(("Goal" :in-theory (enable svar-override-keys-check-override-envs)))))
  
  (defret <fn>-implies-svar-override-keys-check-envlists
    (implies (and ok
                  (svarlist-override-p (svex-envlist-all-keys test-envs) nil)
                  (svarlist-override-p (svex-envlist-all-keys val-envs) nil)
                  (svarlist-override-p keys nil))
             (svar-override-keys-check-override-envlists
              keys
              (svex-envlist-keys-change-override test-envs :test)
              (svex-envlist-keys-change-override val-envs :val)
              ref-envs))
    :hints(("Goal" :in-theory (enable svar-override-keys-check-override-envlists
                                      svex-envlist-keys-change-override
                                      svex-envlist-all-keys))))

  (defretd <fn>-implies-svar-override-keys-check-envlists-double-rw
    (implies (and (double-rewrite ok)
                  (svarlist-override-p (svex-envlist-all-keys test-envs) nil)
                  (svarlist-override-p (svex-envlist-all-keys val-envs) nil)
                  (svarlist-override-p keys nil))
             (svar-override-keys-check-override-envlists
              keys
              (svex-envlist-keys-change-override test-envs :test)
              (svex-envlist-keys-change-override val-envs :val)
              ref-envs)))

  

  (local (defun ind (namemaps test-envs val-envs ref-envs)
           (if (atom namemaps)
               (list test-envs val-envs ref-envs)
             (ind (cdr namemaps) (cdr test-envs) (cdr val-envs) (cdr ref-envs)))))


  (local (defthm 4vec-rsh-x
           (implies (natp w)
                    (equal (4vec-rsh (2vec w) (4vec-x)) (4vec-x)))
           :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core)))))
  
  (local (defthm 4vec-concat-x
           (implies (natp w)
                    (equal (4vec-concat (2vec w) (4vec-x) (4vec-x))
                           (4vec-x)))
           :hints(("Goal" :in-theory (enable 4vec-concat)))))
  
  (local (defthm lhs-eval-x-empty-env
           (equal (lhs-eval-x x nil) (4vec-x))
           :hints(("Goal" :in-theory (enable lhs-eval-x lhatom-eval-x)))))

  (local (defthm svtv-name-lhs-map-eval-x-empty-env
           (svex-envs-similar (svtv-name-lhs-map-eval-x x nil) nil)
           :hints(("Goal" :in-theory (enable svex-envs-similar)))))

  ;; omg!!
  (defthm svex-envlists-overrides-ok-of-eval-inverse
    (implies (and (svex-envlists-overrides-ok
                   test-envs val-envs
                   (svtv-name-lhs-map-list-eval-envlist namemaps ref-envs))
                  (svtv-name-lhs-map-list-keys-no-dups namemaps))
             (svex-envlists-overrides-ok
              (svtv-name-lhs-map-list-eval-x-envlist
               (svtv-name-lhs-map-inverse-list namemaps)
               test-envs)
              (svtv-name-lhs-map-list-eval-x-envlist
               (svtv-name-lhs-map-inverse-list namemaps)
               val-envs)
              ref-envs))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-list-eval-x-envlist
                                      svtv-name-lhs-map-list-eval-envlist
                                      svtv-name-lhs-map-list-keys-no-dups
                                      svtv-name-lhs-map-inverse-list)
            :induct (ind namemaps test-envs val-envs ref-envs))))

  (defcong svex-envlists-equivalent equal (svex-envlists-overrides-ok test-envs val-envs ref-envs) 1)
  (defcong svex-envlists-equivalent equal (svex-envlists-overrides-ok test-envs val-envs ref-envs) 2)
  (defcong svex-envlists-equivalent equal (svex-envlists-overrides-ok test-envs val-envs ref-envs) 3))





(define alistlist-equiv (x y)
  (cond ((atom x) (atom y))
        ((atom y) nil)
        (t (and (alist-equiv (car x) (car y))
                (alistlist-equiv (cdr x) (cdr y)))))
  ///
  (defthm alistlist-equiv-refl
    (alistlist-equiv x x))
  (defthm alistlist-equiv-symm
    (implies (alistlist-equiv x y)
             (alistlist-equiv y x)))
  (defthm alistlist-equiv-trans
    (implies (and (alistlist-equiv x y)
                  (alistlist-equiv y z))
             (alistlist-equiv x z)))
  
  (defequiv alistlist-equiv))


(defcong alist-equiv svex-envs-equivalent (svtv-name-lhs-map-eval-x namemap env) 1
  :hints(("Goal" :in-theory (enable svex-envs-equivalent))))

(defcong alistlist-equiv svex-envlists-equivalent (svtv-name-lhs-map-list-eval-x-envlist namemaps envs) 1
  :hints(("Goal" :in-theory (enable alistlist-equiv
                                    svtv-name-lhs-map-list-eval-x-envlist))))

(defcong alist-equiv svex-envs-equivalent (svtv-name-lhs-map-eval namemap env) 1
  :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                    svex-env-boundp))))

(defcong alistlist-equiv svex-envlists-equivalent (svtv-name-lhs-map-list-eval-envlist namemaps envs) 1
  :hints(("Goal" :in-theory (enable alistlist-equiv
                                    svtv-name-lhs-map-list-eval-envlist))))

(defthm fast-alist-clean-under-alist-equiv
  (alist-equiv (fast-alist-clean x) x)
  :hints(("Goal" :in-theory (enable acl2::alist-equiv-iff-agree-on-bad-guy))))

(defthm fast-alistlist-clean-under-alistlist-equiv
  (alistlist-equiv (fast-alistlist-clean x) x)
  :hints(("Goal" :in-theory (enable alistlist-equiv fast-alistlist-clean))))





(defthm svex-envlist-all-keys-of-svtv-name-lhs-map-list-eval-x-envlist
  (equal (svex-envlist-all-keys (svtv-name-lhs-map-list-eval-x-envlist x env))
         (svtv-name-lhs-map-list-all-keys x))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-list-all-keys
                                    svtv-name-lhs-map-list-eval-x-envlist
                                    svex-envlist-all-keys))))


(defthm alist-keys-of-svtv-name-lhs-map-fix-of-fast-alist-clean-under-set-equiv
  (set-equiv (alist-keys (svtv-name-lhs-map-fix (fast-alist-clean x)))
             (alist-keys (svtv-name-lhs-map-fix x)))
  :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw
                                    acl2::alist-keys-member-hons-assoc-equal)
          :do-not-induct t)))




(defthm svex-env-boundp-of-svtv-name-lhs-map-eval
  (iff (svex-env-boundp v (svtv-name-lhs-map-eval x env))
       (hons-assoc-equal (svar-fix v) x))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval svex-env-boundp))))

(defthm svtv-name-lhs-map-eval-of-fal-extract
  (implies (svarlist-p vars)
           (equal (svtv-name-lhs-map-eval (fal-extract vars x) env)
                  (svex-env-reduce vars (svtv-name-lhs-map-eval x env))))
  :hints(("Goal" :in-theory (enable svex-env-reduce-redef svtv-name-lhs-map-eval fal-extract svarlist-p))))


(defcong set-equiv svex-envs-equivalent (svex-env-reduce keys x) 1
  :hints (("goal" :in-theory (enable svex-envs-equivalent))))


(define svex-envlist-reduce-varlists ((vars svarlist-list-p)
                                      (envs svex-envlist-p))
  :returns (new-envs svex-envlist-p)
  (if (atom vars)
      nil
    (cons (svex-env-reduce (car vars) (car envs))
          (svex-envlist-reduce-varlists (cdr vars) (cdr envs)))))


(defsection svtv-name-lhs-map-list-eval-envlist-of-extract-list
  (local (defun ind (vars envs)
           (if (atom vars)
               (list envs)
             (ind (cdr vars) (cdr envs)))))
  (defthm svtv-name-lhs-map-list-eval-envlist-of-extract-list
    (implies (and (svarlist-list-p vars)
                  (<= (len vars) (len envs)))
             (equal (svtv-name-lhs-map-list-eval-envlist (svtv-name-lhs-map-extract-list vars x) envs)
                    (svex-envlist-reduce-varlists vars (svtv-name-lhs-map-eval-list x envs))))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-list-eval-envlist
                                      svtv-name-lhs-map-extract-list
                                      svex-envlist-reduce-varlists
                                      svarlist-list-p
                                      svtv-name-lhs-map-eval-list)
            :induct (ind vars envs)))))






;; this is a more special case than svex-envs-overrides-ok-of-svex-env-reduce, but it will do
(defsection svex-envlists-overrides-ok-of-svex-envlist-reduce-varlists
  (local (defthm subsetp-intersection-1
           (subsetp-equal (intersection-equal x y) x)
           :hints(("Goal" :in-theory (enable subsetp-equal intersection-equal)))))
  (local (defthm subsetp-intersection-2
           (subsetp-equal (intersection-equal x y) y)
           :hints(("Goal" :in-theory (enable subsetp-equal intersection-equal)))))
  
  ;; (local (defthm svex-envlists-overrides-ok-of-svex-envlist-reduce-varlists-lemma
  ;;          (iff (svex-envlists-overrides-ok test-envs val-envs
  ;;                                           (svex-envlist-reduce-varlists (append (svex-env-keys-list test-envs) rest) ref-envs))
  ;;               (svex-envlists-overrides-ok test-envs val-envs ref-envs))
  ;;          :hints(("Goal" :in-theory (enable svex-envlists-overrides-ok
  ;;                                            svex-envlist-reduce-varlists
  ;;                                            svex-env-keys-list)
  ;;                  :induct (svex-envlists-overrides-ok test-envs val-envs ref-envs)
  ;;                  :expand ((:free (ref-envs) (svex-envlists-overrides-ok test-envs val-envs ref-envs)))))))

  ;; (local (defthmd append-take-nthcdr
  ;;          (implies (<= (nfix n) (len x))
  ;;                   (equal (append (take n x) (nthcdr n x))
  ;;                          x))))

  ;; (local (defthm append-take-nthcdr-free
  ;;          (implies (and (equal y (take n x))
  ;;                        (case-split (<= (nfix n) (len x))))
  ;;                   (equal (append y (nthcdr n x)) x))
  ;;          :hints(("Goal" :in-theory (enable append-take-nthcdr)))))

  (local (defun ind (keys test-envs val-envs ref-envs)
           (if (atom test-envs)
               (list keys val-envs ref-envs)
             (ind (cdr keys) (cdr test-envs) (cdr val-envs) (cdr ref-envs)))))

  (local (defthm svex-env-lookup-when-no-alist-keys
           (implies (not (alist-keys (svex-env-fix x)))
                    (equal (svex-env-lookup k x) (4vec-x)))
           :hints(("Goal" :in-theory (enable alist-keys svex-env-fix svex-env-lookup)))))
  
  (local (defthm svex-env-overrides-ok-when-test-env-no-alist-keys
           (implies (not (alist-keys (svex-env-fix test-env)))
                    (svex-envs-overrides-ok test-env val-env ref-env))
           :hints(("Goal" :in-theory (enable svex-envs-overrides-ok-by-witness)))))
  
  (defthm svex-envlists-overrides-ok-of-svex-envlist-reduce-varlists
    (implies (equal (take (len test-envs) keys) (svex-env-keys-list test-envs))
             (iff (svex-envlists-overrides-ok test-envs val-envs (svex-envlist-reduce-varlists keys ref-envs))
                  (svex-envlists-overrides-ok test-envs val-envs ref-envs)))
    :hints (("Goal" :in-theory (e/d (svex-envlists-overrides-ok
                                             svex-envlist-reduce-varlists
                                             svex-env-keys-list)
                                    (acl2::take-when-atom
                                     acl2::take-of-too-many))
             :induct (ind keys test-envs val-envs ref-envs)
             :expand ((:free (ref-envs) (svex-envlists-overrides-ok test-envs val-envs ref-envs)))))))




;; We want to show

;; (sv::svex-envlists-overrides-ok
;;  (sv::svex-alistlist-eval override-test-alist
;;                           pipe-env)
;;  (sv::svex-alistlist-eval override-val-alist
;;                           pipe-env)
;;  svtv-fsm-outs)

;; given something like

;; (svar-override-triplelist-env-ok-<<= triples pipe-env
;;                                      (svtv-probealist-extract probes svtv-fsm-outs))

;; except some of the triples will have constants instead of vars for the test
;; and val (but always a variable for the ref).

;; To make this connection we need a syntactic check between the triples and
;; the keys of the override-test-alist and override-val-alist and the
;; probes. Namely, for each variable v that is a key of both the nth
;; override-test-alist and override-val-alist, there is a triple containing the
;; corresponding test and value from the override-test-alist and
;; override-value-alist, and the ref variable of the triple is a key of the
;; probes where the corresponding probe is v at time n.

;; I think it's ok to allow the tests/vals of the triples to be svexes, even
;; though practically they'll only be constants/variables.




(defthm no-duplicatesp-of-fal-extract
  (implies (no-duplicatesp-equal vars)
           (no-duplicatesp-equal (alist-keys (fal-extract vars x))))
  :hints(("Goal" :in-theory (enable fal-extract alist-keys
                                    acl2::alist-keys-member-hons-assoc-equal))))



(defthm svtv-name-lhs-map-list-keys-no-dups-of-extract-list
  (implies (no-duplicatesp-each (svarlist-list-fix keys))
           (svtv-name-lhs-map-list-keys-no-dups
            (svtv-name-lhs-map-extract-list keys x)))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-extract-list
                                    svtv-name-lhs-map-list-keys-no-dups
                                    no-duplicatesp-each))))



;; (define alist-keys-list (x)
;;   (if (atom x)
;;       nil
;;     (cons (alist-keys (car x))
;;           (alist-keys-list (cdr x))))
;;   ///
;;   (defthm svtv-name-lhs-map-list-keys-no-dups-in-terms-of-keys
;;     (equal (svtv-name-lhs-map-list-keys-no-dups x)
;;            (no-duplicatesp-each (alist-keys-list (svtv-name-lhs-map-list-fix x))))
;;     :hints(("Goal" :in-theory (enable no-duplicatesp-each
;;                                       svtv-name-lhs-map-list-keys-no-dups))))

;;   (defthm alist-keys-list-of-svtv-name-lhs-map-extract-list
;;     (equal (alist-keys-list (svtv-name-lhs-map-extract-list keys x))
;;            (svarlist-list-fix keys))
;;     :hints(("Goal" :in-theory (enable svtv-name-lhs-map-extract-list svarlist-list-fix)))))



(defcong set-equiv equal (svarlist-override-p x type) 1
  :hints (("goal" :use ((:instance (:functional-instance acl2::element-list-p-set-equiv-congruence
                                    (acl2::element-p (lambda (x) (svar-override-p x type)))
                                    (acl2::element-list-final-cdr-p (lambda (x) t))
                                    (acl2::element-list-p (lambda (x) (svarlist-override-p x type))))
                         (x x) (y x-equiv)))
           :in-theory (enable svarlist-override-p))))
             


(defthm svtv-name-lhs-map-list-all-keys-of-fast-alistlist-clean-under-set-equiv
  (set-equiv (svtv-name-lhs-map-list-all-keys (fast-alistlist-clean x))
             (svtv-name-lhs-map-list-all-keys x))
  :hints(("Goal" :in-theory (enable fast-alistlist-clean svtv-name-lhs-map-list-all-keys))))


;; (defthm SVTV-NAME-LHS-MAP-LIST-ALL-KEYS
;;   (FAST-ALISTLIST-CLEAN

(local
 (defsection floor-when-equal-*
   (local (defun count-down (y)
            (if (zp y)
                y
              (count-down (1- y)))))

   (local (defthm floor-of-times-div
            (implies (and (posp y) (natp z))
                     (equal (floor (* y z) y) z))
            :hints (("goal" :induct (count-down z)
                     :expand ((:with acl2::floor-redef (floor (* y z) y)))))))

   (local (defthm mod-of-times-div
            (implies (and (posp y) (natp z))
                     (equal (mod (* y z) y) 0))
            :hints(("Goal" :in-theory (enable mod)))))

   (defthm floor-when-equal-*
     (implies (and (equal x (* y z))
                   (natp x) (posp y) (natp z))
              (equal (floor x y) z)))

   (defthm mod-when-equal-*
     (implies (and (equal x (* y z))
                   (natp x) (posp y) (natp z))
              (equal (mod x y) 0)))))


(local (defthm svtv-cyclephaselist-unique-i/o-phase-implies-consp
         (implies (svtv-cyclephaselist-unique-i/o-phase phases)
                  (consp phases))
         :hints(("Goal" :in-theory (enable svtv-cyclephaselist-unique-i/o-phase)))
         :rule-classes :forward-chaining))


(defsection svtv-override-triplemap-syntax-check
  
  (local (std::set-define-current-function svtv-override-triplemap-syntax-check))
  (local (in-theory (enable svtv-override-triplemap-syntax-check)))
  (defret <fn>-implies
    (implies (and ok
                  (svtv-override-triplemap-ok triplemap pipe-env
                                              (svtv-probealist-extract probes ref-envs)))
             (svar-override-keys-check-envs keys
                                            (svex-alist-eval test-alist pipe-env)
                                            (svex-alist-eval val-alist pipe-env)
                                            (nth phase ref-envs)))
    :hints(("Goal" :in-theory (enable svar-override-keys-check-envs
                                      svtv-override-triplemap-key-check-implies-lookup-in-triplemap))))

  (defret <fn>-implies-val-alist-keys
    :pre-bind ((keys (svex-alist-keys val-alist)))
    (implies (and ok
                  (svtv-override-triplemap-ok triplemap pipe-env
                                              (svtv-probealist-extract probes ref-envs)))
             (svex-envs-overrides-ok (svex-alist-eval test-alist pipe-env)
                                     (svex-alist-eval val-alist pipe-env)
                                     (nth phase ref-envs)))
    :hints(("Goal" :in-theory (enable svex-envs-overrides-ok)))))

(defsection svtv-override-triplemaplist-syntax-check-aux
  
  (local (std::set-define-current-function svtv-override-triplemaplist-syntax-check-aux))
  (local (in-theory (enable svtv-override-triplemaplist-syntax-check-aux)))

  
  (local (defthm svex-envlists-overrides-ok-of-empty-vals
           (svex-envlists-overrides-ok tests nil refs)
           :hints(("Goal" :in-theory (enable svex-envlists-overrides-ok)))))
  
  (defretd <fn>-implies
    (implies (and ok
                  (svtv-override-triplemaplist-ok triplemaps pipe-env
                                                  (svtv-probealist-extract probes ref-envs)))
             (svex-envlists-overrides-ok (svex-alistlist-eval test-alists pipe-env)
                                         (svex-alistlist-eval val-alists pipe-env)
                                         (nthcdr phase ref-envs)))
    :hints (("goal" :induct <call>
             :in-theory (enable svex-envlists-overrides-ok svex-alistlist-eval
                                svtv-override-triplemaplist-ok
                                nthcdr)
             :expand ((:Free (ref-env) (svtv-override-triplemap-ok nil pipe-env ref-env)))))))


(defsection svtv-override-triplemaplist-syntax-check
  
  (local (std::set-define-current-function svtv-override-triplemaplist-syntax-check))
  (local (in-theory (enable svtv-override-triplemaplist-syntax-check)))
  
  (defret <fn>-implies
    (implies (and ok
                  (svtv-override-triplemaplist-ok triplemaps pipe-env
                                                  (svtv-probealist-extract probes ref-envs)))
             (svex-envlists-overrides-ok (svex-alistlist-eval test-alists pipe-env)
                                         (svex-alistlist-eval val-alists pipe-env)
                                         ref-envs))
    :hints (("goal" :use ((:instance svtv-override-triplemaplist-syntax-check-aux-implies
                           (phase 0)))
             :in-theory (disable svtv-override-triplemaplist-syntax-check-aux-implies)))))



(defthm svtv-override-triplemaplist-ok-of-spec-outs-implies-svar-override-keys-check-override-envlists-of-spec-ins
  (b* (((svtv-spec spec)))
    (implies (and
              (svtv-override-triplemaplist-ok triplemaps pipe-env
                                              (svtv-spec-phase-outs->pipe-out spec phase-outs))
              (svtv-override-triplemaplist-syntax-check
               spec.override-test-alists spec.override-val-alists
               spec.probes triplemaps)
              (svarlist-override-p override-keys nil)
              (svarlist-override-p (svtv-cyclephaselist-keys spec.cycle-phases) nil)
              (svtv-cyclephaselist-unique-i/o-phase spec.cycle-phases)
              (equal (svex-alist-keys-list spec.override-test-alists)
                     (svex-alist-keys-list spec.override-val-alists))
              (no-duplicatesp-each (svex-alist-keys-list spec.override-test-alists))
              (svarlist-override-p
               (svtv-name-lhs-map-list-all-keys
                (svtv-name-lhs-map-inverse-list
                 (svtv-name-lhs-map-extract-list
                  (take (len (svtv-probealist-outvars (svtv-spec->probes spec)))
                        (svex-alist-keys-list (svtv-spec->override-test-alists spec)))
                  (svtv-spec->namemap spec))))
               nil)
              (equal (len phase-outs) (* (len spec.cycle-phases)
                                         (len (svtv-probealist-outvars (svtv-spec->probes spec)))))
              (<= (len (svtv-spec->override-test-alists spec))
                  (len (svtv-probealist-outvars (svtv-spec->probes spec)))))
             
             (svar-override-triplelist-envlists-ok-<<=
              (svarlist-to-override-triples override-keys)
              (svtv-spec-pipe-env->phase-envs spec pipe-env)
              phase-outs)))
  :hints(("Goal" :in-theory (e/d (svtv-spec-pipe-env->phase-envs
                                  svtv-spec-phase-outs->pipe-out
                                  svex-envlists-overrides-ok-implies-svar-override-keys-check-envlists-double-rw
                                  take-of-svex-alistlist-eval
                                  svex-alist-keys-list-of-take
                                  svtv-cyclephaselist-unique-i/o-phase-implies-natp-output-phase)
                                 (acl2::take-of-too-many)))))






(defsection svex-envlist-<<=-of-svtv-spec-pipe-env->phase-envs
  (local (defthm svex-envlist-<<=-of-take
           (implies (svex-envlist-<<= x y)
                    (svex-envlist-<<= (take n x) (take n y)))
           :hints(("Goal" :in-theory (e/d (svex-envlist-<<= take)
                                          (acl2::take-when-atom acl2::take-of-too-many))))))

  (local (defthm svex-alistlist-check-monotonic-of-take
           (implies (svex-alistlist-check-monotonic x)
                    (svex-alistlist-check-monotonic (take n x)))
           :hints(("Goal" :in-theory (e/d (svex-alistlist-check-monotonic take)
                                          (acl2::take-when-atom acl2::take-of-too-many))))))
  
  (defthm svex-envlist-<<=-of-svtv-spec-pipe-env->phase-envs
    (b* (((svtv-spec spec)))
      (implies (and (svex-env-<<= pipe-env1 pipe-env2)
                    (svex-alistlist-check-monotonic spec.in-alists)
                    (svex-alistlist-check-monotonic spec.override-test-alists)
                    (svex-alistlist-check-monotonic spec.override-val-alists))
               (svex-envlist-<<= (svtv-spec-pipe-env->phase-envs spec pipe-env1)
                                 (svtv-spec-pipe-env->phase-envs spec pipe-env2))))
    :hints(("Goal" :in-theory (enable svtv-spec-pipe-env->phase-envs
                                      take-of-svex-alistlist-eval
                                      svex-alist-keys-list-of-take)))))



(defsection svex-env-<<=-of-svtv-spec-phase-outs->pipe-out
  (local (defthm len-equal-0
           (equal (Equal (len x) 0) (atom x))))
  (local (defun ind (phases x y)
           (declare (xargs :measure (len x)))
           (if (atom x)
               y
             (ind phases (nthcdr (max 1 (len phases)) x)
                  (nthcdr (max 1 (len phases)) y)))))
  
  (local (defthm svex-envlist-phase-outputs-extract-cycle-outputs-length-monotonic
           (implies (<= (len x) (len y))
                    (<= (len (svex-envlist-phase-outputs-extract-cycle-outputs phases x))
                        (len (svex-envlist-phase-outputs-extract-cycle-outputs phases y))))
           :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs)
                   :induct (ind phases x y)
                   :expand ((svex-envlist-phase-outputs-extract-cycle-outputs phases x)
                            (svex-envlist-phase-outputs-extract-cycle-outputs phases y))))))

  (defthm svex-env-<<=-of-svtv-spec-phase-outs->pipe-out
    (implies (and (svex-envlist-<<= phase-outs1 phase-outs2)
                  (<= (len phase-outs1) (len phase-outs2)))
             (svex-env-<<= (svtv-spec-phase-outs->pipe-out spec phase-outs1)
                           (svtv-spec-phase-outs->pipe-out spec phase-outs2)))
    :hints(("Goal" :in-theory (enable svtv-spec-phase-outs->pipe-out)
            :do-not-induct t))))


(defthm base-fsm-eval-monotonic
  (b* (((base-fsm fsm)))
    (implies (and (svex-envlist-<<= ins1 ins2)
                  (<= (len ins1) (len ins2))
                  (svex-env-<<= initst1 initst2)
                  (svex-alist-monotonic-p fsm.values)
                  (svex-alist-monotonic-p fsm.nextstate))
             (svex-envlist-<<= (base-fsm-eval ins1 initst1 fsm)
                               (base-fsm-eval ins2 initst2 fsm))))
  :hints(("Goal" :in-theory (enable base-fsm-eval
                                    base-fsm-step
                                    base-fsm-step-env
                                    base-fsm-step-outs
                                    svex-envlist-<<=))))


;; Svtv-spec-run is NOT monotonic in pipe-env in general, but it is in the case
;; where base-ins and initst are empty.  Additionally, it is monotonic in
;; base-ins and initst (provided the FSM itself and the input alists are
;; monotonic).

(defthm svtv-spec-run-monotonic-in-pipe-env-when-empty-base-ins/initst
  (b* (((svtv-spec spec))
       ((base-fsm spec.fsm)))
    (implies (and (svex-env-<<= pipe-env1 pipe-env2)
                  (svex-alistlist-check-monotonic spec.in-alists)
                  (svex-alistlist-check-monotonic spec.override-test-alists)
                  (svex-alistlist-check-monotonic spec.override-val-alists)
                  (svex-alist-check-monotonic spec.initst-alist)
                  (svex-alist-monotonic-p spec.fsm.values)
                  (svex-alist-monotonic-p spec.fsm.nextstate))
             (svex-env-<<= (svtv-spec-run spec pipe-env1)
                           (svtv-spec-run spec pipe-env2))))
  :hints(("Goal" :in-theory (enable svtv-spec-run
                                    svex-alist-monotonic-p-necc))))

(encapsulate nil
  (local (defthm compare-len-of-svex-envlist-x-override
           (equal (< (len (svex-envlist-x-override a b1))
                     (len (svex-envlist-x-override a b2)))
                  (and (< (len b1) (len b2))
                       (< (len a) (len b2))))))
  (local (in-theory (disable len-of-svex-envlist-x-override)))

  (defthm svtv-spec-run-monotonic-in-base-ins
    (b* (((svtv-spec spec))
         ((base-fsm spec.fsm)))
      (implies (and (svex-envlist-<<= base-ins1 base-ins2)
                    (<= (len base-ins1) (len base-ins2))
                    (svex-alist-monotonic-p spec.fsm.values)
                    (svex-alist-monotonic-p spec.fsm.nextstate))
               (svex-env-<<= (svtv-spec-run spec pipe-env :base-ins base-ins1 :initst initst)
                             (svtv-spec-run spec pipe-env :base-ins base-ins2 :initst initst))))
    :hints(("Goal" :in-theory (enable svtv-spec-run
                                      svex-alist-monotonic-p-necc)))))


(defthm svtv-spec-run-monotonic-in-initst
    (b* (((svtv-spec spec))
         ((base-fsm spec.fsm)))
      (implies (and (svex-env-<<= initst1 initst2)
                    (svex-alist-monotonic-p spec.fsm.values)
                    (svex-alist-monotonic-p spec.fsm.nextstate))
               (svex-env-<<= (svtv-spec-run spec pipe-env :base-ins base-ins :initst initst1)
                             (svtv-spec-run spec pipe-env :base-ins base-ins :initst initst2))))
    :hints(("Goal" :in-theory (enable svtv-spec-run
                                      svex-alist-monotonic-p-necc))))




(defsection svtv-spec-run-remove-overrides
  (defthm svarlist-override-p-when-svarlist-addr-p
    (implies (svarlist-addr-p x)
             (svarlist-override-p x nil))
    :hints(("Goal" :in-theory (enable svarlist-override-p
                                      svarlist-addr-p
                                      svar-override-p
                                      svar-addr-p))))

  (local (defthm svar-override-p-when-member
           (implies (and (svarlist-override-p vars type)
                         (member-equal (svar-fix v) (svarlist-fix vars)))
                    (svar-override-p v type))
           :hints(("Goal" :in-theory (enable svarlist-override-p)))))
  

  (local (defthm svex-env-extract-of-append-filter-override
           (implies (svarlist-override-p vars nil)
                    (svex-envs-similar (svex-env-extract vars (append a (svex-env-filter-override b nil)))
                                       (svex-env-extract vars (append a b))))
           :hints(("Goal" :in-theory (enable svex-envs-similar)))))

  (local (defthm svex-alist-eval-of-append-filter-override
           (implies (svarlist-override-p (svex-alist-vars x) nil)
                    (equal (svex-alist-eval x (append a (svex-env-filter-override b nil)))
                           (svex-alist-eval x (append a b))))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equal-when-extract-vars-similar)
                   :do-not-induct t))))
  
  (defthm base-fsm-eval-of-svex-envlist-filter-overrides
    (b* (((base-fsm x)))
      (implies (and (svarlist-override-p (svex-alist-vars x.values) nil)
                    (svarlist-override-p (svex-alist-vars x.nextstate) nil))
               (equal (base-fsm-eval (svex-envlist-filter-override envs nil) initst x)
                      (base-fsm-eval envs initst x))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      base-fsm-step
                                      base-fsm-step-env
                                      base-fsm-step-outs
                                      svex-envlist-filter-override))))

  (defthm svex-env-filter-override-of-svex-env-x-override
    (equal (svex-env-filter-override (svex-env-x-override a b) type)
           (svex-env-x-override (svex-env-filter-override a type)
                                (svex-env-filter-override b type)))
    :hints(("Goal" :in-theory (enable svex-env-filter-override svex-env-x-override))))
  
  (defthm svex-envlist-filter-override-of-svex-envlist-x-override
    (equal (svex-envlist-filter-override (svex-envlist-x-override a b) type)
           (svex-envlist-x-override (svex-envlist-filter-override a type)
                                    (svex-envlist-filter-override b type)))
    :hints(("Goal" :in-theory (enable svex-envlist-filter-override
                                      svex-envlist-x-override))))

  (defthm svex-envlist-filter-override-of-svtv-cycle-fsm-inputs
    (implies (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
             (equal (svex-envlist-filter-override (svtv-cycle-fsm-inputs env phases) nil)
                    (svtv-cycle-fsm-inputs (svex-env-filter-override env nil) phases)))
    :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                      svtv-cyclephaselist-keys
                                      svtv-cycle-step-fsm-inputs
                                      svex-envlist-filter-override))))

  (defthm svex-envlist-filter-override-of-svtv-cycle-run-fsm-inputs
    (implies (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
             (equal (svex-envlist-filter-override (svtv-cycle-run-fsm-inputs env phases) nil)
                    (svtv-cycle-run-fsm-inputs (svex-envlist-filter-override env nil) phases)))
    :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs
                                      svex-envlist-filter-override))))


  (defthm svex-env-filter-override-of-svex-env-keys-change-override
    (equal (svex-env-filter-override (svex-env-keys-change-override x type1) type2)
           (and (svar-overridetype-equiv type1 type2)
                (svex-env-keys-change-override x type1)))
    :hints(("Goal" :in-theory (enable svex-env-keys-change-override
                                      svex-env-filter-override))))
             

  (defthm svex-env-filter-override-of-svtv-fsm-phase-inputs
    (equal (svex-env-filter-override (svtv-fsm-phase-inputs inputs override-vals override-tests namemap) nil)
           (svtv-fsm-phase-inputs inputs nil nil namemap))
    :hints(("Goal" :in-theory (enable svtv-fsm-phase-inputs
                                      svtv-fsm-env-inversemap)
            :expand ((:free (a) (fal-extract nil a))))))


  (defthm svex-envlist-filter-override-of-svtv-fsm-to-base-fsm-inputs
    (equal (svex-envlist-filter-override (svtv-fsm-to-base-fsm-inputs inputs override-vals override-tests namemap) nil)
           (svtv-fsm-to-base-fsm-inputs inputs nil nil namemap))
    :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs
                                      svex-envlist-filter-override))))
  
  (defthm svtv-spec-phase-outs->pipe-out-of-svtv-spec
    (implies (syntaxp (not (subsetp-equal (list fsm in-alists override-test-alists override-val-alists initst-alist)
                                          `('nil ',(base-fsm-fix nil)))))
             (equal (svtv-spec-phase-outs->pipe-out (make-svtv-spec
                                                     :fsm fsm
                                                     :cycle-phases cycle-phases
                                                     :namemap namemap
                                                     :probes probes
                                                     :in-alists in-alists
                                                     :override-test-alists override-test-alists
                                                     :override-val-alists override-val-alists
                                                     :initst-alist initst-alist)
                                                    phase-outs)
                    (svtv-spec-phase-outs->pipe-out (make-svtv-spec
                                                     :cycle-phases cycle-phases
                                                     :namemap namemap
                                                     :probes probes)
                                                    phase-outs)))
    :hints(("Goal" :in-theory (enable svtv-spec-phase-outs->pipe-out))))

  (local (defthm svar-override-type-fix-equal
           (implies (equal (svar-overridetype-fix x) (svar-overridetype-fix y))
                    (svar-overridetype-equiv x y))
           :rule-classes :forward-chaining))

  
  
  
  (defthm svex-env-filter-override-of-svex-env-filter-override
    (equal (svex-env-filter-override (svex-env-filter-override x type1) type2)
           (and (svar-overridetype-equiv type1 type2)
                (svex-env-filter-override x type1)))
    :hints(("Goal" :in-theory (enable svex-env-filter-override)
            :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable svar-override-p)))))

  (defthm svex-envlist-filter-override-of-svex-envlist-filter-override
    (equal (svex-envlist-filter-override (svex-envlist-filter-override x type1) type2)
           (if (svar-overridetype-equiv type1 type2)
               (svex-envlist-filter-override x type1)
             (repeat (len x) nil)))
    :hints(("Goal" :in-theory (enable svex-envlist-filter-override repeat))))


  (defthm svex-envlist-filter-override-of-svtv-spec-pipe-env->phase-envs
    (implies (svarlist-override-p (svtv-cyclephaselist-keys (svtv-spec->cycle-phases x)) nil)
             (equal (svex-envlist-filter-override (svtv-spec-pipe-env->phase-envs x env)
                                                  nil)
                    (svtv-spec-pipe-env->phase-envs
                     (change-svtv-spec x :override-test-alists nil
                                       :override-val-alists nil)
                     env)))
    :hints(("Goal" :in-theory (enable svtv-spec-pipe-env->phase-envs))))
  
  (local (defthm base-fsm-eval-apply-svex-envlist-filter-override
           (b* (((base-fsm x)))
             (implies (and (svarlist-override-p (svex-alist-vars x.values) nil)
                           (svarlist-override-p (svex-alist-vars x.nextstate) nil)
                           ;; (syntaxp (or (cw "envs: ~x0~%" envs) t))
                           (equal envs1 (double-rewrite (svex-envlist-filter-override envs nil)))
                           ;; (syntaxp (or (cw "envs1: ~x0~%" envs1) t))
                           (bind-free
                            (case-match envs1
                              (('svex-envlist-filter-override envs2 ''nil) `((envs2 . ,envs2)))
                              (& `((envs2 . ,envs1))))
                            (envs2))
                           ;; (syntaxp (or (cw "envs2: ~x0~%" envs2) t))
                           (syntaxp (not (equal envs2 envs)))
                           (equal (svex-envlist-filter-override envs2 nil) envs1))
                      (equal (base-fsm-eval envs initst x)
                             (base-fsm-eval envs2 initst x))))
           :hints (("goal" :use ((:instance base-fsm-eval-of-svex-envlist-filter-overrides
                                  (envs envs))
                                 (:instance base-fsm-eval-of-svex-envlist-filter-overrides
                                  (envs envs2)))
                    :in-theory (disable base-fsm-eval-of-svex-envlist-filter-overrides)))))


  (defthm base-fsm-eval-of-pipe-env->phase-envs-remove-overrides
    (b* (((base-fsm x)))
      (implies (and (syntaxp (not (and (equal override-test-alists ''nil)
                                       (equal override-val-alists ''nil))))
                    (svarlist-override-p (svex-alist-vars x.values) nil)
                    (svarlist-override-p (svex-alist-vars x.nextstate) nil)
                    (svarlist-override-p (svtv-cyclephaselist-keys cycle-phases) nil))
               (equal (base-fsm-eval
                       (svex-envlist-x-override
                        (svtv-spec-pipe-env->phase-envs
                         (make-svtv-spec
                          :fsm fsm
                          :cycle-phases cycle-phases
                          :namemap namemap
                          :probes probes
                          :in-alists in-alists
                          :override-test-alists override-test-alists
                          :override-val-alists override-val-alists
                          :initst-alist initst-alist)
                         pipe-env)
                        base-ins)
                       initst
                       x)
                      (base-fsm-eval
                       (svex-envlist-x-override
                        (svtv-spec-pipe-env->phase-envs
                         (make-svtv-spec
                          :fsm fsm
                          :cycle-phases cycle-phases
                          :namemap namemap
                          :probes probes
                          :in-alists in-alists
                          :override-test-alists nil
                          :override-val-alists nil
                          :initst-alist initst-alist)
                         pipe-env)
                        base-ins)
                       initst
                       x))))
    :hints(("Goal" :in-theory (enable svtv-spec-pipe-env->phase-envs))))

  
  (defthm svtv-spec-run-remove-overrides
    (b* (((base-fsm x)))
      (implies (and (syntaxp (not (and (equal override-test-alists ''nil)
                                       (equal override-val-alists ''nil))))
                    (svarlist-override-p (svex-alist-vars x.values) nil)
                    (svarlist-override-p (svex-alist-vars x.nextstate) nil)
                    (svarlist-override-p (svtv-cyclephaselist-keys cycle-phases) nil))
               (equal (svtv-spec-run (make-svtv-spec
                                      :fsm x
                                      :cycle-phases cycle-phases
                                      :namemap namemap
                                      :probes probes
                                      :in-alists in-alists
                                      :override-test-alists override-test-alists
                                      :override-val-alists override-val-alists
                                      :initst-alist initst-alist)
                                     pipe-env :base-ins base-ins :initst initst)
                      (svtv-spec-run (make-svtv-spec
                                      :fsm x
                                      :cycle-phases cycle-phases
                                      :namemap namemap
                                      :probes probes
                                      :in-alists in-alists
                                      :initst-alist initst-alist)
                                     pipe-env :base-ins base-ins :initst initst))))
    :hints(("Goal" :in-theory (enable svtv-spec-run
                                      svtv-spec-pipe-env->phase-envs))))

  (local (defthm svex-alistlist-eval-of-svex-env-reduce-when-vars-subset
           (implies (subsetp-equal (svex-alistlist-vars x) (svarlist-fix vars))
                    (equal (svex-alistlist-eval x (svex-env-reduce vars env))
                           (svex-alistlist-eval x env)))
           :hints(("Goal" :in-theory (enable svex-alistlist-eval
                                             svex-alistlist-vars)))))

  
  (defthm svtv-spec-pipe-env->phase-envs-of-svex-env-reduce
    (b* (((svtv-spec spec)))
      (implies (and (subsetp-equal (svex-alistlist-vars spec.in-alists) (svarlist-fix vars))
                    (subsetp-equal (svex-alistlist-vars spec.override-test-alists) (svarlist-fix vars))
                    (subsetp-equal (svex-alistlist-vars spec.override-val-alists) (svarlist-fix vars)))
               (equal (svtv-spec-pipe-env->phase-envs spec (svex-env-reduce vars env))
                      (svtv-spec-pipe-env->phase-envs spec env))))
    :hints(("Goal" :in-theory (enable svtv-spec-pipe-env->phase-envs))))

  (defthm svtv-spec-run-of-svex-env-reduce
    (b* (((svtv-spec spec)))
      (implies (and (subsetp-equal (svex-alistlist-vars spec.in-alists) (svarlist-fix vars))
                    (subsetp-equal (svex-alistlist-vars spec.override-test-alists) (svarlist-fix vars))
                    (subsetp-equal (svex-alistlist-vars spec.override-val-alists) (svarlist-fix vars))
                    (subsetp-equal (svex-alist-vars spec.initst-alist) (svarlist-fix vars)))
               (equal (svtv-spec-run spec (svex-env-reduce vars env) :base-ins base-ins :initst initst)
                      (svtv-spec-run spec env :base-ins base-ins :initst initst))))
    :hints(("Goal" :in-theory (enable svtv-spec-run)))))



(defthm svtv-spec-pipe-env->phase-envs-of-svtv-spec
  (implies (syntaxp (not (or (equal fsm ''nil)
                             (equal fsm `',(base-fsm-fix nil)))))
           (equal (svtv-spec-pipe-env->phase-envs (make-svtv-spec
                                                   :fsm fsm
                                                   :cycle-phases cycle-phases
                                                   :namemap namemap
                                                   :probes probes
                                                   :in-alists in-alists
                                                   :override-test-alists override-test-alists
                                                   :override-val-alists override-val-alists
                                                   :initst-alist initst-alist)
                                                  pipe-env)
                  (svtv-spec-pipe-env->phase-envs (make-svtv-spec
                                                   :cycle-phases cycle-phases
                                                   :probes probes
                                                   :namemap namemap
                                                   :in-alists in-alists
                                                   :override-test-alists override-test-alists
                                                   :override-val-alists override-val-alists
                                                   :initst-alist initst-alist)
                                                  pipe-env)))
  :hints(("Goal" :in-theory (enable svtv-spec-pipe-env->phase-envs))))



(defthm svex-envlist-<<=-nil
  (svex-envlist-<<= nil x)
  :hints(("Goal" :in-theory (enable svex-envlist-<<=))))



(define svex-envlist-reduce ((keys svarlist-p)
                             (x svex-envlist-p))
  :returns (new-x svex-envlist-p)
  (if (atom x)
      nil
    (cons (svex-env-reduce keys (car x))
          (svex-envlist-reduce keys (cdr x)))))
    

(defthmd svex-envlist-<<=-transitive-1
  (implies (and (svex-envlist-<<= x y)
                (svex-envlist-<<= y z))
           (svex-envlist-<<= x z))
  :hints(("Goal" :in-theory (enable svex-envlist-<<=
                                    svex-env-<<=-transitive-1))))

(defthmd svex-envlist-<<=-transitive-2
  (implies (and (svex-envlist-<<= y z)
                (svex-envlist-<<= x y))
           (svex-envlist-<<= x z))
  :hints(("Goal" :in-theory (enable svex-envlist-<<=
                                    svex-env-<<=-transitive-1))))






(local
 (encapsulate nil
   ;; The original version of this theorem isn't quite general enough for
   ;; us. Generalizing by making it explicit that the ref-inputs only have to be
   ;; greater than the override inputs on variables that are used in the FSM.
   
   ;; To instantiate that theorem and prove this one, we need to instantiate with ref-inputs-inst satisfying
   ;; (svex-envlist-<<= (svex-envlist-removekeys override-vars override-inputs) ref-inputs-inst)
   ;; for which the FSM will evaluate to the same as with just ref-inputs.
   ;; but we only have
   ;; (svex-envlist-<<= (svex-envlist-reduce input-vars override-inputs) ref-inputs)
   ;; They only need to agree on input-vars.

   (local (defun compose-ref-input-envs (override-inputs ref-inputs input-vars)
            (if (atom override-inputs)
                (svex-envlist-fix ref-inputs)
              (cons (append (svex-env-extract input-vars (car ref-inputs)) (svex-env-fix (car override-inputs)))
                    (compose-ref-input-envs (cdr override-inputs) (cdr ref-inputs) input-vars)))))

   (local (defthm svex-env-reduce-vars-lemma
            (implies (subsetp-equal (svarlist-fix vars1) (svarlist-fix vars2))
                     (equal (svex-env-extract vars1 (append env1 (svex-env-extract vars2 env2) env3))
                            (svex-env-extract vars1 (append env1 env2))))
            :hints(("Goal" :in-theory (enable svex-env-extract)
                    :induct (len vars1)))))
   

   (local (defthm svex-alist-eval-append-reduce
            (implies (subsetp-equal (svex-alist-vars x) (svarlist-fix input-vars))
                     (equal (svex-alist-eval x (append env1 (svex-env-extract input-vars env2) env3))
                            (svex-alist-eval x (append env1 env2))))
            :hints(("Goal" :in-theory (enable svex-alist-eval-equal-when-extract-vars-similar)))))
                          
   
   (local (defthm base-fsm-eval-of-compose-ref-input-envs
            (b* (((base-fsm fsm)))
              (implies (and (subsetp-equal (svex-alist-vars fsm.values) (svarlist-fix input-vars))
                            (subsetp-equal (svex-alist-vars fsm.nextstate) (svarlist-fix input-vars))
                            (<= (len override-inputs) (len ref-inputs)))
                       (equal (base-fsm-eval (compose-ref-input-envs override-inputs ref-inputs input-vars)
                                             initst fsm)
                              (base-fsm-eval ref-inputs initst fsm))))
            :hints(("Goal" :in-theory (enable base-fsm-eval
                                              base-fsm-step
                                              base-fsm-step-outs
                                              base-fsm-step-env)))))


   (local (defthm len-of-compose-ref-input-envs
            (equal (len (compose-ref-input-envs override-inputs ref-inputs input-vars))
                   (max (len override-inputs) (len ref-inputs)))))

   (local (defthm svex-envlist-<<=-removekeys-compose-ref-input-envs-lemma
            (implies (svex-env-<<= (svex-env-reduce input-vars override-input) ref-input)
                     (svex-env-<<= (svex-env-removekeys override-vars override-input)
                                   (append (svex-env-extract input-vars ref-input)
                                           override-input)))
            :hints ((and stable-under-simplificationp
                         (b* ((lit (car (last clause)))
                              (witness `(svex-env-<<=-witness . ,(cdr lit))))
                           `(:expand (,lit)
                             :use ((:instance svex-env-<<=-necc
                                    (var ,witness)
                                    (x (svex-env-reduce input-vars override-input))
                                    (y ref-input)))
                             :in-theory (disable svex-env-<<=-necc)))))))
                                    
   

   (local (defthm svex-envlist-<<=-removekeys-compose-ref-input-envs
            (implies (svex-envlist-<<= (svex-envlist-reduce input-vars override-inputs) ref-inputs)
                     (svex-envlist-<<= (svex-envlist-removekeys override-vars override-inputs)
                                       (compose-ref-input-envs override-inputs ref-inputs input-vars)))
            :hints(("Goal" :in-theory (enable svex-envlist-removekeys
                                              svex-envlist-<<=
                                              svex-envlist-reduce
                                              compose-ref-input-envs)))))
   

   (local (defthm svex-envlist-removekeys-of-repeat-nil
            (equal (svex-envlist-removekeys keys (repeat n nil))
                   (repeat n nil))
            :hints(("Goal" :in-theory (enable svex-envlist-removekeys
                                              repeat)))))

   (local (defthm svex-envlist-<<=-of-repeat-nil
            (svex-envlist-<<= (repeat n nil) y)
            :hints(("Goal" :in-theory (enable repeat svex-envlist-<<=)
                    :induct (nthcdr n y)))))

   (local (defthm svex-envlist-<<=-of-append-repeat-nil
            (equal (svex-envlist-<<= (append x (repeat n nil)) y)
                   (svex-envlist-<<= x y))
            :hints(("Goal" :in-theory (enable svex-envlist-<<=)))))


   (local
    (defthm svex-envlist-<<=-of-base-fsm-eval-append-repeat
      (svex-envlist-<<= (base-fsm-eval ins initst fsm)
                        (base-fsm-eval (append ins (repeat n nil)) initst fsm))
      :hints(("Goal" :in-theory (enable base-fsm-eval
                                        svex-envlist-<<=)))))
   
   

   (local (defthm svar-override-triplelist-env-ok-of-nil
            (svar-override-triplelist-env-ok-<<=
             triples nil ref)
            :hints(("Goal" :in-theory (enable svar-override-triplelist-env-ok-<<=)))))
   
   (local (defthm svar-override-triplelist-envlists-ok-of-repeat-nil
            (svar-override-triplelist-envlists-ok-<<=
             triples (repeat n nil) refs)
            :hints(("Goal" :in-theory (enable svar-override-triplelist-envlists-ok-<<= repeat)
                    :induct (nthcdr n refs)))))
   
   (local (defthm svar-override-triplelist-envlists-ok-of-append-repeat-nil
            (equal (svar-override-triplelist-envlists-ok-<<=
                    triples (append override-inputs (repeat n nil)) refs)
                   (svar-override-triplelist-envlists-ok-<<=
                    triples override-inputs refs))
            :hints(("Goal" :in-theory (enable svar-override-triplelist-envlists-ok-<<=)))))
   
   (defthm base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-gen
     (b* (((base-fsm ideal-fsm) (design->ideal-fsm x))
          ((svtv-data-obj data))
          (triples
           (svarlist-to-override-triples
            (svtv-assigns-override-vars (flatnorm-res->assigns data.flatnorm)
                                        (phase-fsm-config->override-config data.phase-fsm-setup))))
          ;; (override-vars (svar-override-triplelist-override-vars triples))
          (spec-values (base-fsm-eval ref-inputs ref-initst ideal-fsm))
          (impl-values (base-fsm-eval override-inputs override-initst data.phase-fsm)))
       (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic data))
                     data.flatten-validp
                     data.flatnorm-validp
                     data.phase-fsm-validp
                     (flatnorm-setup->monotonify data.flatnorm-setup)
                     (equal data.design x)

                     (<= (len override-inputs) (len ref-inputs))
                     (svex-envlist-<<= (svex-envlist-reduce input-vars override-inputs) ref-inputs)
                     (subsetp-equal (svex-alist-vars ideal-fsm.values) (svarlist-fix input-vars))
                     (subsetp-equal (svex-alist-vars ideal-fsm.nextstate) (svarlist-fix input-vars))
                     (svar-override-triplelist-envlists-ok-<<= triples override-inputs spec-values)
                     (svex-env-<<= override-initst ref-initst))
                (svex-envlist-<<= impl-values spec-values)))
     :hints (("Goal" :do-not-induct t
              :use ((:instance base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation
                     (ref-inputs (compose-ref-input-envs
                                  override-inputs ref-inputs input-vars))
                     (override-inputs (append override-inputs (repeat (- (len ref-inputs)
                                                                         (len override-inputs))
                                                                      nil)))))
              :in-theory (e/d (svex-envlist-<<=-transitive-2
                               svex-envlist-<<=-transitive-1)
                              (base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation))))
     :otf-flg t)))



(defsection svtv-spec-run-of-take-base-ins
  (local (in-theory (disable acl2::take-of-too-many
                             acl2::take-when-atom
                             nth
                             acl2::nth-when-zp
                             (tau-system)
                             acl2::take-of-len-free
                             take)))
  
  (defthm svtv-probealist-extract-of-take
    (implies (<= (len (svtv-probealist-outvars probes)) (nfix len))
             (equal (svtv-probealist-extract probes (take len envs))
                    (svtv-probealist-extract probes envs)))
    :hints(("Goal" :in-theory (e/d (svtv-probealist-extract svtv-probealist-outvars)
                                   (take))
            :induct (len probes))))

  (local (defthm take-of-svtv-name-lhs-map-eval-list
           (implies (<= (nfix n) (len envs))
                    (equal (take n (svtv-name-lhs-map-eval-list namemap envs))
                           (svtv-name-lhs-map-eval-list namemap (take n envs))))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-list
                                             take)))))

  (local (defun take-of-cycle-ind (n phases envs)
           (if (zp n)
               envs
             (take-of-cycle-ind (1- n) phases (nthcdr (len phases) envs)))))

  (local (defthm nthcdr-of-take
           (equal (nthcdr n (take m x))
                  (take (- (nfix m) (nfix n)) (nthcdr n x)))
           :hints(("Goal" :in-theory (enable nthcdr take)))))

  (local (defthm floor-lemma
           (implies (and (natp x) (posp y))
                    (<= (* (floor x y) y) x))
           :hints(("Goal" :in-theory (enable acl2::floor-redef)
                   :induct (acl2::floor-mod-ind x y)))))

  ;; (local (defthm floor-lemma2
  ;;          (implies (and (natp n)
  ;;                        (natp x) (posp y)
  ;;                        (<= n (floor x y)))
  ;;                   (<= x (* n y)))
  ;;          :hints (("goal" :use floor-lemma
  ;;                   :in-theory (disable floor-lemma)))))

  (local (defthm lemma
           (implies (and (posp n)
                         (natp output-phase)
                         (< output-phase (len phases)))
                    (< output-phase (* n (len phases))))
           :hints (("goal" :nonlinearp t
                    :do-not-induct t))))
  
  (local (defthm take-of-svex-envlist-phase-outputs-extract-cycle-outputs
           (implies (and (case-split
                           (<= (nfix n)
                               (+ (floor (len envs)
                                         (len phases))
                                  (if (< (svtv-cycle-output-phase phases) (mod (len envs) (len phases))) 1 0))))
                         ;; (consp phases)
                         (svtv-cyclephaselist-has-outputs-captured phases))
                    (equal (take n (svex-envlist-phase-outputs-extract-cycle-outputs
                                    phases envs))
                           (svex-envlist-phase-outputs-extract-cycle-outputs
                            phases (take (* (nfix n) (len phases)) envs))))
           :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs)
                   :induct  (take-of-cycle-ind n phases envs)
                   :expand ((svex-envlist-phase-outputs-extract-cycle-outputs phases envs)
                            (svex-envlist-phase-outputs-extract-cycle-outputs phases (take (* n (len phases)) envs))
                            (:free (x) (take n x))
                            (:with acl2::floor-redef (floor (len envs) (len phases)))
                            (:with acl2::mod-redef (mod (len envs) (len phases))))))))


  (local (defthm floor-natp
           (implies (and (case-split (natp x)) (natp y))
                    (natp (floor x y)))
           :hints(("Goal" :in-theory (enable floor)))
           :rule-classes (:rewrite :type-prescription)))
  
  (local (defun floor-gte-product-ind (x y z)
           (declare (xargs :measure (abs (floor (nfix x) (nfix z)))
                           :hints (("goal" :in-theory (enable acl2::floor-redef)))))
           (if (zp z)
               y
             (if (< (nfix x) z)
                 y
               (floor-gte-product-ind (- (nfix x) z) (- y 1) z)))))
  
  (local (defthm floor-when-gte-product
           (implies (and (integerp x)
                         (<= (* z y) x)
                         (natp y) (posp z))
                    (<= y (floor x z)))
           :hints (("Goal" :induct (floor-gte-product-ind x y z)
                    :expand ((:with acl2::floor-redef (floor x z))))
                   (and stable-under-simplificationp
                        '(:nonlinearp t)))
           :rule-classes (:rewrite :linear)))

  (local (defthm floor-when-gte-product-+-1
           (implies (and (integerp x)
                         (<= (* z y) x)
                         (natp y) (posp z))
                    (<= y (+ 1 (floor x z))))
           :hints (("goal" :use floor-when-gte-product
                    :in-theory (disable floor-when-gte-product)))
           :rule-classes (:rewrite :linear)))

  (local (defthm len->-0
           (equal (< 0 (len x)) (consp x))))

  (local (defthm len-posp
           (equal (posp (len x)) (consp x))))

  (local (defthm len-of-extract-cycle-outputs-lemma
           (implies (and (<= (* (len phases)
                                outvars-len)
                             (len envs))
                         (natp outvars-len)
                         (consp phases))
                    (<= outvars-len (len (svex-envlist-phase-outputs-extract-cycle-outputs phases envs))))
           :hints (("goal" :do-not-induct t))
           :otf-flg t))

  (local (defthm svtv-cyclephaselist-has-outputs-captured-implies-consp
           (implies (svtv-cyclephaselist-has-outputs-captured phases)
                    (consp phases))
           :hints(("Goal" :in-theory (enable svtv-cyclephaselist-has-outputs-captured)))
           :rule-classes :forward-chaining))

  (defthm svtv-spec-phase-outs->pipe-out-of-take
    (implies (and (<= (* (len (svtv-spec->cycle-phases spec))
                         (len (svtv-probealist-outvars (svtv-spec->probes spec))))
                      (nfix len))
                  (<= (nfix len) (len envs))
                  (svtv-cyclephaselist-has-outputs-captured
                   (svtv-spec->cycle-phases spec)))
             (equal (svtv-spec-phase-outs->pipe-out spec (take len envs))
                    (svtv-spec-phase-outs->pipe-out spec envs)))
    :hints(("Goal" :use ((:instance svtv-probealist-extract-of-take
                          (len (len (svtv-probealist-outvars (svtv-spec->probes spec))))
                          (probes (svtv-spec->probes spec))
                          (envs (SVTV-NAME-LHS-MAP-EVAL-LIST (SVTV-SPEC->NAMEMAP SPEC)
                                          (SVEX-ENVLIST-PHASE-OUTPUTS-EXTRACT-CYCLE-OUTPUTS
                                               (SVTV-SPEC->CYCLE-PHASES SPEC)
                                               (TAKE LEN ENVS)))))
                         (:instance svtv-probealist-extract-of-take
                          (len (len (svtv-probealist-outvars (svtv-spec->probes spec))))
                          (probes (svtv-spec->probes spec))
                          (envs (SVTV-NAME-LHS-MAP-EVAL-LIST (SVTV-SPEC->NAMEMAP SPEC)
                                          (SVEX-ENVLIST-PHASE-OUTPUTS-EXTRACT-CYCLE-OUTPUTS
                                               (SVTV-SPEC->CYCLE-PHASES SPEC)
                                               envs)))))
            :in-theory (e/d (svtv-spec-phase-outs->pipe-out)
                            (svtv-probealist-extract-of-take
                             len-of-svex-envlist-phase-outputs-extract-cycle-outputs
                             ))
            :do-not-induct t)))
  

  (defthmd base-fsm-eval-of-take
    (implies (<= (nfix n) (len ins))
             (equal (base-fsm-eval (take n ins) initst fsm)
                    (take n (base-fsm-eval ins initst fsm))))
    :hints(("Goal" :in-theory (enable base-fsm-eval take))))


  (local (defun base-fsm-eval-ins-ind (ins ins-equiv initst fsm)
           (if (atom ins)
               (list ins-equiv initst)
             (base-fsm-eval-ins-ind (cdr ins) (cdr ins-equiv)
                                    (base-fsm-step (car ins) initst (base-fsm->nextstate fsm))
                                    fsm))))
  
  (defcong svex-envlists-equivalent equal (base-fsm-eval ins initst fsm) 1
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      base-fsm-step
                                      base-fsm-step-outs
                                      base-fsm-step-env)
            :induct (base-fsm-eval-ins-ind ins ins-equiv initst fsm)
            :expand ((base-fsm-eval ins initst fsm)
                     (base-fsm-eval ins-equiv initst fsm)))))
  
  (local (defthm svex-envlist-x-override-of-take
           (implies (and (<= (len a) (nfix n)))
                    (svex-envlists-equivalent (svex-envlist-x-override a (take n b))
                                              (take n (svex-envlist-x-override a b))))
           :hints(("Goal" :in-theory (enable svex-envlist-x-override
                                             svex-envlist-fix
                                             take)
                   :induct (list (take n a) (take n b))))))

  (local (defthm base-fsm-eval-of-take-split
           (implies (case-split (<= (nfix n) (len ins)))
                    (equal (base-fsm-eval (take n ins) initst fsm)
                           (take n (base-fsm-eval ins initst fsm))))
           :hints(("Goal" :in-theory (enable base-fsm-eval-of-take)))))


  (local (defthm svtv-spec-phase-outs->pipe-out-of-take-split
           (implies (and (<= (* (len (svtv-spec->cycle-phases spec))
                                (len (svtv-probealist-outvars (svtv-spec->probes spec))))
                             (nfix len))
                         (case-split (<= (nfix len) (len envs)))
                         (svtv-cyclephaselist-has-outputs-captured
                          (svtv-spec->cycle-phases spec)))
                    (equal (svtv-spec-phase-outs->pipe-out spec (take len envs))
                           (svtv-spec-phase-outs->pipe-out spec envs)))))
  
  (defthm svtv-spec-run-of-take-base-ins
    (implies (and (svtv-cyclephaselist-has-outputs-captured
                   (svtv-spec->cycle-phases spec))
                  (equal len (* (len (svtv-spec->cycle-phases spec))
                                (len (svtv-probealist-outvars (svtv-spec->probes spec))))))
             (equal (svtv-spec-run spec pipe-env
                                   :base-ins (take len base-ins)
                                   :initst initst)
                    (svtv-spec-run spec pipe-env :base-ins base-ins :initst initst)))
    :hints(("Goal" :in-theory (enable svtv-spec-run
                                      base-fsm-eval-of-take)))))



(defsection svtv-data-obj->ideal-spec
  
  (local (std::set-define-current-function svtv-data-obj->ideal-spec))
  (local (in-theory (enable svtv-data-obj->ideal-spec)))

  (local (defthm svex-env-reduce-<<=
           (svex-env-<<= (svex-env-reduce keys x) x)
           :hints(("Goal" :in-theory (enable svex-env-<<=)))))
  
  (local (defthm svex-envlist-reduce-<<=-lemma
           (svex-envlist-<<= (svex-envlist-reduce keys x) x)
           :hints(("Goal" :in-theory (enable svex-envlist-reduce
                                             svex-envlist-<<=)))))

  (local (defthm svex-envlist-reduce-<<=-rw
           (implies (svex-envlist-<<= x y)
                    (svex-envlist-<<= (svex-envlist-reduce keys x) y))
           :hints(("Goal" :in-theory (enable svex-envlist-<<=-transitive-2
                                             svex-envlist-<<=-transitive-1)))))

  (local (defthm svex-envlist-x-override->>=-rw
           (implies (svex-envlist-<<= x y)
                    (svex-envlist-<<= x (svex-envlist-x-override y z)))
           :hints(("Goal" :in-theory (enable svex-envlist-<<=-transitive-2
                                             svex-envlist-<<=-transitive-1)))))

  (defthm design-flatten-okp-when-flatten-validp
    (b* (((svtv-data-obj x)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp)
               (design-flatten-okp x.design)))
    :hints(("Goal" :in-theory (enable design-flatten-okp))))

  (local (defthm max-when-<=
           (implies (and (<= b a)
                         (rationalp b) (rationalp a))
                    (equal (max a b)
                           a))))

  (local (defthm <<=-4vec-x-override-when-<<=-first-arg
           (implies (4vec-<<= a b)
                    (4vec-<<= a (4vec-x-override b c)))
           :hints(("Goal" :in-theory (enable 4vec-<<=-transitive-1
                                             4vec-<<=-transitive-2)))))

  (local (defthm svex-env-<<=-of-svex-env-x-override
           (implies (svex-env-<<= a b)
                    (svex-env-<<= a (svex-env-x-override b c)))
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))
  


  (local
   (defthm svex-envlist-<<=-of-svtv-spec-pipe-env->phase-envs-reduce
     (b* (((svtv-spec spec)))
       (implies (and (svex-env-<<= (svex-env-reduce vars pipe-env1) pipe-env2)
                     (subsetp-equal (svex-alistlist-vars spec.in-alists) (svarlist-fix vars))
                     (subsetp-equal (svex-alistlist-vars spec.override-test-alists) (svarlist-fix vars))
                     (subsetp-equal (svex-alistlist-vars spec.override-val-alists) (svarlist-fix vars))
                     (svex-alistlist-check-monotonic spec.in-alists)
                     (svex-alistlist-check-monotonic spec.override-test-alists)
                     (svex-alistlist-check-monotonic spec.override-val-alists))
                (svex-envlist-<<= (svtv-spec-pipe-env->phase-envs spec pipe-env1)
                                  (svtv-spec-pipe-env->phase-envs spec pipe-env2))))
     :hints(("Goal" :use ((:instance svtv-spec-pipe-env->phase-envs-of-svex-env-reduce
                           (env pipe-env1)))
             :in-theory (e/d () (svtv-spec-pipe-env->phase-envs-of-svex-env-reduce))))))


  (local (defthm svex-env-<<=-of-svex-alist-eval-when-<<=-on-vars
           (implies (and (svex-env-<<= (svex-env-reduce vars a) b)
                         (subsetp-equal (svex-alist-vars x) (svarlist-fix vars))
                         (svex-alist-monotonic-p x))
                    (svex-env-<<= (svex-alist-eval x a)
                                  (svex-alist-eval x b)))
           :hints (("goal" :use ((:instance svex-alist-monotonic-p-necc
                                  (env1 (svex-env-reduce vars a))
                                  (env2 b)))
                    :in-theory (disable svex-alist-monotonic-p-necc)))))


  (local (defthm svex-env-reduce-of-svex-env-filter-overrides
           (implies (svarlist-override-p vars nil)
                    (equal (svex-env-reduce vars (svex-env-filter-override env nil))
                           (svex-env-reduce vars env)))
           :hints(("Goal" :in-theory (enable svex-env-reduce-redef
                                             svarlist-override-p)
                   :induct (len vars)))))
  
  (local (defthm svex-envlist-reduce-of-svex-envlist-filter-overrides
           (implies (svarlist-override-p vars nil)
                    (equal (svex-envlist-reduce vars (svex-envlist-filter-override envs nil))
                           (svex-envlist-reduce vars envs)))
           :hints(("Goal" :in-theory (enable svex-envlist-reduce
                                             svex-envlist-filter-override)))))
  

  (local (defthm svex-envlist-reduce-non-override-vars-of-svtv-spec-pipe-env->phase-envs
           (implies (and (equal override-tests (svtv-spec->override-test-alists x))
                         (equal override-vals (svtv-spec->override-val-alists x))
                         (syntaxp (not (and (equal override-vals ''nil)
                                            (equal override-tests ''nil))))
                         (svarlist-override-p vars nil)
                         (svarlist-override-p (svtv-cyclephaselist-keys (svtv-spec->cycle-phases x)) nil))
                    (equal (svex-envlist-reduce vars (svtv-spec-pipe-env->phase-envs x env))
                           (svex-envlist-reduce vars
                                                (svtv-spec-pipe-env->phase-envs
                                                 (change-svtv-spec x :override-test-alists nil :override-val-alists nil)
                                                 env))))
           :hints (("goal" :use ((:instance svex-envlist-reduce-of-svex-envlist-filter-overrides
                                  (envs (svtv-spec-pipe-env->phase-envs x env))))
                    :in-theory (disable svex-envlist-reduce-of-svex-envlist-filter-overrides)))))


  (local (defthm svex-env-<<=-of-svex-env-reduce-both
           (equal (svex-env-<<= (svex-env-reduce vars envs1)
                                    (svex-env-reduce vars envs2))
                  (svex-env-<<= (svex-env-reduce vars envs1) envs2))
           :hints(("goal" :cases ((svex-env-<<= (svex-env-reduce vars envs1) envs2)))
                  (and stable-under-simplificationp
                       (b* ((lit (assoc 'svex-env-<<= clause))
                            (witness `(svex-env-<<=-witness . ,(cdr lit)))
                            (other (if (eq (caddr lit) 'envs2) '(svex-env-reduce vars envs2) 'envs2)))
                         `(:expand (,lit)
                           :use ((:instance svex-env-<<=-necc
                                  (var ,witness)
                                  (x (svex-env-reduce vars envs1))
                                  (y ,other)))
                           :in-theory (disable svex-env-<<=-necc)))))
           :otf-flg t))
  

  (local (defun cdr2 (x y)
           (if (atom x)
               y
             (cdr2 (cdr x) (cdr y)))))
  
  (local (defthm svex-envlist-<<=-of-svex-envlist-reduce-both
           (equal (svex-envlist-<<= (svex-envlist-reduce vars envs1)
                                    (svex-envlist-reduce vars envs2))
                  (svex-envlist-<<= (svex-envlist-reduce vars envs1) envs2))
           :hints(("Goal" :in-theory (enable svex-envlist-<<=
                                             svex-envlist-reduce)
                   :induct (cdr2 envs1 envs2)
                   :expand ((svex-envlist-reduce vars envs1)
                            (svex-envlist-reduce vars envs2))))))
  

  (local (defthm svex-envlist-<<=-of-svex-envlist-reduce-try-crazy-thing
           (implies (and (equal envs3 (svex-envlist-reduce vars envs2))
                         (bind-free
                          (case-match envs3
                            (('svex-envlist-reduce & envs4) `((envs4 . ,envs4)))
                            (& `((envs4 . ,envs3))))
                          (envs4))
                         (syntaxp (not (equal envs2 envs4)))
                         (equal (svex-envlist-reduce vars envs4) envs3))
                    (equal (svex-envlist-<<= (svex-envlist-reduce vars envs1) envs2)
                           (svex-envlist-<<= (svex-envlist-reduce vars envs1) envs4)))
           :hints (("goal" :use ((:instance svex-envlist-<<=-of-svex-envlist-reduce-both)
                                 (:instance svex-envlist-<<=-of-svex-envlist-reduce-both
                                  (envs2 envs4)))
                    :in-theory (disable svex-envlist-<<=-of-svex-envlist-reduce-both)))))
  
  
  (local
   (defret <fn>-run-refines-svtv-spec-run-with-len-spec-base-ins-bound
    (b* (((svtv-spec impl) (svtv-data-obj->spec x))
         ((svtv-spec spec))
         ((svtv-data-obj x))
         ((pipeline-setup x.pipeline-setup))
         (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
         (impl-run (svtv-spec-run impl pipe-env)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    x.phase-fsm-validp
                    x.cycle-fsm-validp
                    x.pipeline-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup)
                    

                    (svtv-override-triplemaplist-ok triplemaps pipe-env spec-run)
                    (svtv-override-triplemaplist-syntax-check
                     x.pipeline-setup.override-tests x.pipeline-setup.override-vals
                     x.pipeline-setup.probes triplemaps)
                    
                    (svarlist-override-p (svtv-cyclephaselist-keys x.cycle-phases) nil)
                    (svtv-cyclephaselist-unique-i/o-phase x.cycle-phases)
                    (equal (svex-alist-keys-list x.pipeline-setup.override-tests)
                           (svex-alist-keys-list x.pipeline-setup.override-vals))
                    (no-duplicatesp-each (svex-alist-keys-list x.pipeline-setup.override-tests))
                    (svarlist-override-p
                     (svtv-name-lhs-map-list-all-keys
                      (svtv-name-lhs-map-inverse-list
                       (svtv-name-lhs-map-extract-list
                        (take (len (svtv-probealist-outvars x.pipeline-setup.probes))
                              (svex-alist-keys-list x.pipeline-setup.override-tests))
                        x.namemap)))
                     nil)
                    (<= (len x.pipeline-setup.override-tests)
                        (len (svtv-probealist-outvars x.pipeline-setup.probes)))
                    (<= (len spec-base-ins)
                        (* (len x.cycle-phases)
                           (len (svtv-probealist-outvars x.pipeline-setup.probes))))
                    
                    (svex-env-<<= (svex-env-reduce
                                   (append (svex-alist-vars x.pipeline-setup.initst)
                                           (svex-alistlist-vars x.pipeline-setup.inputs))
                                   pipe-env)
                                  spec-pipe-env)
                    
                    (svex-alistlist-check-monotonic x.pipeline-setup.inputs)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-vals)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-tests)
                    (svex-alist-check-monotonic x.pipeline-setup.initst)
                    )
               (svex-env-<<= impl-run spec-run)))
    :hints(("Goal" :in-theory (e/d (svtv-spec-run
                                    svtv-data-obj->spec
                                    svar-override-triplelist-override-vars-of-triples-when-svarlist-override-p)
                                   (base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation
                                    base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-gen
                                    SVAR-OVERRIDE-TRIPLELIST-ENV-OK-<<=-IN-TERMS-OF-CHECK-OVERRIDE-ENVLISTS))
            :restrict ((svtv-override-triplemaplist-ok-of-spec-outs-implies-svar-override-keys-check-override-envlists-of-spec-ins
                        ((triplemaps triplemaps))))
            :use ((:instance base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-gen
                   (data x)
                   (x (svtv-data-obj->design x))
                   (ref-inputs (b* (((svtv-data-obj x))
                                    ((pipeline-setup x.pipeline-setup)))
                                 (svex-envlist-x-override
                                  (svtv-spec-pipe-env->phase-envs
                                   (make-svtv-spec :fsm (design->ideal-fsm x.design)
                                                   :cycle-phases x.cycle-phases
                                                   :namemap x.namemap
                                                   :probes x.pipeline-setup.probes
                                                   :in-alists x.pipeline-setup.inputs
                                                   :override-test-alists x.pipeline-setup.override-tests
                                                   :override-val-alists x.pipeline-setup.override-vals
                                                   :initst-alist x.pipeline-setup.initst)
                                   spec-pipe-env)
                                  spec-base-ins)))
                   (input-vars (b* (((svtv-data-obj x))
                                    ((base-fsm fsm) (design->ideal-fsm x.design)))
                                 (append (svex-alist-vars fsm.nextstate)
                                         (svex-alist-vars fsm.values))))
                   (ref-initst (svex-env-x-override
                                (b* (((svtv-data-obj x))
                                     ((pipeline-setup x.pipeline-setup)))
                                  (svex-alist-eval x.pipeline-setup.initst spec-pipe-env))
                                spec-initst))
                   (override-inputs (svtv-spec-pipe-env->phase-envs
                                     (svtv-data-obj->spec x)
                                     pipe-env))
                   (override-initst (b* (((svtv-data-obj x))
                                         ((pipeline-setup x.pipeline-setup)))
                                      (svex-alist-eval x.pipeline-setup.initst pipe-env)))))))))


  (defret <fn>-run-refines-svtv-spec-run
    (b* (((svtv-spec impl) (svtv-data-obj->spec x))
         ((svtv-spec spec))
         ((svtv-data-obj x))
         ((pipeline-setup x.pipeline-setup))
         (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
         (impl-run (svtv-spec-run impl pipe-env)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    x.phase-fsm-validp
                    x.cycle-fsm-validp
                    x.pipeline-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup)
                    

                    (svtv-override-triplemaplist-ok triplemaps pipe-env spec-run)
                    (svtv-override-triplemaplist-syntax-check
                     x.pipeline-setup.override-tests x.pipeline-setup.override-vals
                     x.pipeline-setup.probes triplemaps)
                    
                    (svarlist-override-p (svtv-cyclephaselist-keys x.cycle-phases) nil)
                    (svtv-cyclephaselist-unique-i/o-phase x.cycle-phases)
                    (equal (svex-alist-keys-list x.pipeline-setup.override-tests)
                           (svex-alist-keys-list x.pipeline-setup.override-vals))
                    (no-duplicatesp-each (svex-alist-keys-list x.pipeline-setup.override-tests))
                    (svarlist-override-p
                     (svtv-name-lhs-map-list-all-keys
                      (svtv-name-lhs-map-inverse-list
                       (svtv-name-lhs-map-extract-list
                        (take (len (svtv-probealist-outvars x.pipeline-setup.probes))
                              (svex-alist-keys-list x.pipeline-setup.override-tests))
                        x.namemap)))
                     nil)
                    (<= (len x.pipeline-setup.override-tests)
                        (len (svtv-probealist-outvars x.pipeline-setup.probes)))
                    
                    (svex-env-<<= (svex-env-reduce
                                   (append (svex-alist-vars x.pipeline-setup.initst)
                                           (svex-alistlist-vars x.pipeline-setup.inputs))
                                   pipe-env)
                                  spec-pipe-env)
                    
                    (svex-alistlist-check-monotonic x.pipeline-setup.inputs)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-vals)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-tests)
                    (svex-alist-check-monotonic x.pipeline-setup.initst)
                    )
               (svex-env-<<= impl-run spec-run)))
    :hints(("Goal" :use ((:instance <fn>-run-refines-svtv-spec-run-with-len-spec-base-ins-bound
                          (spec-base-ins (b* (((svtv-data-obj x))
                                              ((pipeline-setup x.pipeline-setup)))
                                           (take (* (len x.cycle-phases)
                                                    (len (svtv-probealist-outvars x.pipeline-setup.probes)))
                                                 spec-base-ins)))))
            :in-theory (disable <fn>-run-refines-svtv-spec-run-with-len-spec-base-ins-bound)))))
  



(defthmd set-equiv-by-mergesort-equal
  (implies (syntaxp (and (quotep x) (quotep y)))
           (equal (set-equiv x y)
                  (equal (mergesort x) (mergesort y))))
  :hints (("goal" :use ((:instance set::mergesort-under-set-equiv (x x))
                        (:instance set::mergesort-under-set-equiv (x y)))
           :in-theory (disable set::mergesort-under-set-equiv))))
