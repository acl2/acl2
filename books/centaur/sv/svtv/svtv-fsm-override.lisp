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

(include-book "../svex/override")
(include-book "svtv-stobj-export")
(include-book "centaur/fgl/def-fgl-thm" :dir :system)
(include-book "centaur/misc/starlogic" :dir :system)
(include-book "centaur/meta/variable-free" :dir :system)
(local (include-book "../svex/alist-thms"))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))

(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable acl2::alist-keys-member-hons-assoc-equal)))








(define pipeline-run ((setup pipeline-setup-p)
                      (namemap svtv-name-lhs-map-p)
                      (cycle base-fsm-p)
                      (env svex-env-p))
  :guard (and (equal (svex-alist-keys (pipeline-setup->initst setup))
                     (svex-alist-keys (base-fsm->nextstate cycle)))
              (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate cycle)))))
  :guard-hints (("goal" :in-theory (enable svtv-fsm->renamed-fsm)))
  (b* ((fsm (svtv-fsm cycle namemap))
       ((pipeline-setup setup))
       (outvars (svtv-probealist-outvars setup.probes)))
    (SVTV-PROBEALIST-EXTRACT
     setup.probes
     (BASE-FSM-RUN
      (SVEX-ALISTLIST-EVAL
       (SVTV-FSM-RUN-INPUT-SUBSTS
        (TAKE
         (LEN outvars)
         setup.inputs)
        setup.overrides
        fsm)
       ENV)
      (SVEX-ALIST-EVAL setup.initst ENV)
      (SVTV-FSM->RENAMED-FSM fsm)
      outvars))))







(define svex-envlist-removekeys* ((vars svarlist-list-p)
                                  (envs svex-envlist-p))
  (if (atom envs)
      nil
    (cons (svex-env-removekeys (car vars) (car envs))
          (svex-envlist-removekeys* (cdr vars) (cdr envs))))
  ///
  (defthm svex-envlist-removekeys*-of-cons
    (Equal (svex-envlist-removekeys* vars (cons env envs))
           (cons (svex-env-removekeys (car vars) env)
                 (svex-envlist-removekeys* (cdr vars) envs))))

  ;; (defthm svex-envlist-removekeys*-of-append
  ;;   (Equal (svex-envlist-removekeys* vars (append envs envs2))
  ;;          (append (svex-envlist-removekeys* vars envs)
  ;;                  (svex-envlist-removekeys* (nthcdr (len envs) vars) envs2))))
  )

(fty::deflist svex-override-triplelistlist :elt-type svex-override-triplelist :true-listp t)

;; (define subsetlist-p ((x true-list-listp) (y true-listp))
;;   (if (atom x)
;;       t
;;     (and (subsetp-equal (car x) y)
;;          (subsetlist-p (cdr x) y))))

(defthmd intersectp-svex-alist-keys-by-hons-intersect-p1
  (iff (acl2::hons-intersect-p1 x (svex-alist-fix y))
       (intersectp-equal x (svex-alist-keys y)))
  :hints(("Goal" :in-theory (enable intersectp-equal acl2::hons-intersect-p1 svex-lookup))))

(defthmd subsetp-svex-alist-keys-by-hons-subset1
  (iff (subsetp-equal x (svex-alist-keys y))
       (acl2::hons-subset1 x (svex-alist-fix y)))
  :hints(("Goal" :in-theory (enable subsetp-equal acl2::hons-subset1 svex-lookup))))

(defthmd intersectp-by-hons-intersect-p
  (iff (intersectp-equal x y)
       (acl2::hons-intersect-p x y)))


(local (defthmd hons-assoc-equal-member-alist-keys
         (iff (hons-assoc-equal k x)
              (member-equal k (alist-keys x)))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(defthmd hons-subset1-is-subsetp-alist-keys
  (iff (acl2::hons-subset1 x y)
       (subsetp-equal x (alist-keys y)))
  :hints(("Goal" :in-theory (enable acl2::hons-subset1 subsetp-equal alist-keys
                                    hons-assoc-equal-member-alist-keys))))

(defthmd subsetp-alist-keys-by-hons-subset1
  (iff (subsetp-equal x (alist-keys y))
       (acl2::hons-subset1 x y))
  :hints(("Goal" :in-theory (enable hons-subset1-is-subsetp-alist-keys))))

(defthm alist-keys-of-hons-put-list
  (implies (atom val)
           (acl2::set-equiv (alist-keys (acl2::hons-put-list x val rest))
                            (append x (alist-keys rest)))))
(defthm hons-subset2-is-subsetp-equal
  (iff (acl2::hons-subset2 x y)
       (subsetp-equal x y)))
(defthm hons-subset-is-subsetp-equal
  (iff (acl2::hons-subset x y)
       (subsetp-equal x y))
  :hints(("Goal" :in-theory (enable acl2::hons-subset
                                    hons-subset1-is-subsetp-alist-keys))))

(defthmd subsetp-equal-by-hons-subset
  (iff (subsetp-equal x y)
       (acl2::hons-subset x y)))


(defthmd append-set-diff-under-set-equiv
  (implies (subsetp x y)
           (set-equiv (append (set-difference-equal y x) x) y))
  :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw))))


(defthmd nthcdr-0
  (equal (nthcdr 0 x) x)
  :hints(("Goal" :expand ((nthcdr 0 x)))))


(define svex-override-triple-subsetlist-p-exec ((x svex-override-triplelistlist-p)
                                                (triples-set))
  :hooks nil
  (if (atom x)
      t
    (and (not (acl2::hons-dups-p (svex-override-triplelist-vars (car x))))
         (acl2::hons-subset1 (car x) triples-set)
         (svex-override-triple-subsetlist-p-exec (cdr x) triples-set))))




(define svex-override-triple-subsetlist-p ((x svex-override-triplelistlist-p)
                                           (triples  svex-override-triplelist-p))
  :verify-guards nil
  (mbe :logic (if (atom x)
                  t
                (and (no-duplicatesp-equal (svex-override-triplelist-vars (car x)))
                     (subsetp-equal (svex-override-triplelist-fix (car x))
                                    (svex-override-triplelist-fix triples))
                     (svex-override-triple-subsetlist-p (cdr x) triples)))
       :exec (b* ((set (acl2::hons-put-list triples t nil))
                  (ans (svex-override-triple-subsetlist-p-exec x set)))
               (fast-alist-free set)
               ans))
  ///
  
  (local (defthm svex-override-triple-subsetlist-p-exec-elim
           (implies (and (svex-override-triplelistlist-p x)
                         (svex-override-triplelist-p triples))
                    (equal (svex-override-triple-subsetlist-p-exec x (acl2::hons-put-list triples t nil))
                           (svex-override-triple-subsetlist-p x triples)))
           :hints(("Goal" :in-theory (enable svex-override-triple-subsetlist-p-exec
                                             hons-subset1-is-subsetp-alist-keys)))))
  
  (verify-guards svex-override-triple-subsetlist-p)

  (defthm svex-override-triple-subsetlist-p-of-cdr
    (implies (svex-override-triple-subsetlist-p x triples)
             (svex-override-triple-subsetlist-p (cdr x) triples)))

  (defthm no-duplicatesp-car-when-svex-override-triplelist-p
    (implies (svex-override-triple-subsetlist-p x triples)
             (no-duplicatesp-equal (svex-override-triplelist-vars (car x)))))

  (defthm svexlist-check-overridetriples-car-when-svex-override-triplelist-p
    (implies (and (svex-override-triple-subsetlist-p x triples)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (not (svexlist-check-overridetriples svexes triples)))
             (not (svexlist-check-overridetriples svexes (car x))))
    :hints(("Goal" :in-theory (enable svexlist-check-overridetriples-when-subset)))))


(define svex-override-triplelistlist-vars ((x svex-override-triplelistlist-p))
  :guard-hints (("goal" :in-theory (enable svex-override-triplelistlist-p)))
  :returns (vars svarlist-list-p)
  (if (atom x)
      nil
    (cons (svex-override-triplelist-vars (car x))
          (svex-override-triplelistlist-vars (cdr x)))))


(define svex-override-triplelistlist-testvars ((x svex-override-triplelistlist-p))
  :guard-hints (("goal" :in-theory (enable svex-override-triplelistlist-p)))
  :returns (vars svarlist-list-p)
  (if (atom x)
      nil
    (cons (svex-override-triplelist-testvars (car x))
          (svex-override-triplelistlist-testvars (cdr x)))))



(define svex-override-triplelist-fsm-inputs-ok* ((triples svex-override-triplelistlist-p)
                                                 (envs svex-envlist-p)
                                                 (prev-envs svex-envlist-p)
                                                 (initst svex-env-p)
                                                 (fsm base-fsm-p))
  :guard (and (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate fsm)))
              (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate fsm)))))
  :measure (len prev-envs)
  (if (atom prev-envs)
      t
    (and (svex-override-triplelist-env-ok (car triples)
                                          (base-fsm-step-env (car envs) initst fsm)
                                          (base-fsm-step-env (car prev-envs) initst fsm))
         (svex-override-triplelist-fsm-inputs-ok* (cdr triples)
                                                  (cdr envs)
                                                  (cdr prev-envs)
                                                  (base-fsm-step (car prev-envs) initst fsm)
                                                  fsm)))
  ///
  (defthm svex-override-triplelist-fsm-inputs-ok*-of-cons
    (equal (svex-override-triplelist-fsm-inputs-ok* triples
                                                    (cons env envs)
                                                    (cons prev-env prev-envs)
                                                    initst fsm)
           (and (svex-override-triplelist-env-ok (car triples)
                                                 (base-fsm-step-env env initst fsm)
                                                 (base-fsm-step-env prev-env initst fsm))
                (svex-override-triplelist-fsm-inputs-ok* (cdr triples) envs prev-envs
                                                         (base-fsm-step prev-env initst fsm)
                                                         fsm))))

  (defthm svex-override-triplelist-fsm-inputs-ok*-of-nil
    (equal (svex-override-triplelist-fsm-inputs-ok* triples envs nil initst fsm)
           t))

  (defthm svex-override-triplelist-fsm-inputs-ok*-of-svex-alistlist-eval-cons
    (equal (svex-override-triplelist-fsm-inputs-ok* triples
                                                    envs
                                                    (svex-alistlist-eval (cons prev-env-al prev-env-als) env1)
                                                    initst fsm)
           (and (svex-override-triplelist-env-ok (car triples)
                                                 (base-fsm-step-env (car envs) initst fsm)
                                                 (base-fsm-step-env (svex-alist-eval prev-env-al env1) initst fsm))
                (svex-override-triplelist-fsm-inputs-ok* (cdr triples)
                                                         (cdr envs)
                                                         (svex-alistlist-eval prev-env-als env1)
                                                         (base-fsm-step (svex-alist-eval prev-env-al env1) initst fsm)
                                                         fsm))))

  (defcong svex-envs-similar equal (svex-override-triplelist-fsm-inputs-ok* triples envs prev-envs prev-st fsm) 4))



(defprod svar-override-triple
  ((testvar svar-p)
   (valvar svar-p)
   (refvar svar-p))
  :layout :list)

(fty::deflist svar-override-triplelist :elt-type svar-override-triple :true-listp t)

(define svar->svex-override-triplelist ((x svar-override-triplelist-p)
                                        (values svex-alist-p))
  :returns (triples svex-override-triplelist-p)
  (if (atom x)
      nil
    (cons (b* (((svar-override-triple x1) (car x)))
            (make-svex-override-triple :testvar x1.testvar
                                       :valvar x1.valvar
                                       :valexpr (or (svex-fastlookup x1.refvar values)
                                                    (svex-x))))
          (svar->svex-override-triplelist (cdr x) values)))
  ///
  (defret len-of-<fn>
    (equal (len triples) (len x))))


(defprojection svar-override-triplelist->valvars ((x svar-override-triplelist-p))
  :returns (valvars svarlist-p)
  (svar-override-triple->valvar x))

(defprojection svar-override-triplelist->testvars ((x svar-override-triplelist-p))
  :returns (testvars svarlist-p)
  (svar-override-triple->testvar x)
  ///
  (defthm svex-override-triplelist-testvars-of-svar->svex-override-triplelist
    (equal (svex-override-triplelist-testvars (svar->svex-override-triplelist x values))
           (svar-override-triplelist->testvars x))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-testvars
                                      svar->svex-override-triplelist)))))

(defprojection svar-override-triplelist->refvars ((x svar-override-triplelist-p))
  :returns (refvars svarlist-p)
  (svar-override-triple->refvar x))

(define svar-override-triplelist-lookup-valvar ((valvar svar-p) (table svar-override-triplelist-p))
  :returns (val (iff (svar-override-triple-p val) val))
  (b* (((when (atom table)) nil)
       ((svar-override-triple x1) (svar-override-triple-fix (car table)))
       ((when (equal (svar-fix valvar) x1.valvar)) x1))
    (svar-override-triplelist-lookup-valvar valvar (cdr table)))
  ///
  (defret lookup-valvar-under-iff
    (iff val
         (member-equal (svar-fix valvar)
                       (svar-override-triplelist->valvars table)))))




(local (defthm consp-hons-assoc-equal
         (iff (consp (hons-assoc-equal k x))
              (hons-assoc-equal k x))))


(local (defthm svex-env-boundp-when-member-svex-env-alist-keys
         (implies (member-equal (svar-fix v) (alist-keys (svex-env-fix env)))
                  (svex-env-boundp v env))
         :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-fix alist-keys)))))

(define svar-override-triplelist-env-ok ((x svar-override-triplelist-p)
                                         (override-env svex-env-p)
                                         (ref-env svex-env-p))
  (if (atom x)
      t
    (acl2::and*
     (b* (((svar-override-triple trip) (car x))
          (testval (svex-env-lookup trip.testvar override-env))
          (valval (svex-env-lookup trip.valvar override-env))
          (refval (svex-env-lookup trip.refvar ref-env)))
       (or (equal (4vec-bit?! testval valval 0)
                  (4vec-bit?! testval refval 0))
           (prog2$ (cw "~x0: failed signal: ~x1.~%" std::__function__ trip.refvar)
                   (svtv-print-alist-readable
                    `((test . ,(2vec (logand (4vec->upper testval) (4vec->lower testval))))
                      (val  . ,(4vec-bit?! testval valval 0))
                      (ref  . ,(4vec-bit?! testval refval 0)))))))
     (svar-override-triplelist-env-ok (cdr x) override-env ref-env)))
  ///
  (defthm svar-override-triplelist-env-ok-in-terms-of-svex-override-triplelist-env-ok
    (equal (svar-override-triplelist-env-ok x override-env (svex-alist-eval values prev-env))
           (svex-override-triplelist-env-ok
            (svar->svex-override-triplelist x values)
            override-env prev-env))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-env-ok
                                      svar->svex-override-triplelist))))

  (defthm svar-override-triplelist-env-ok-of-append-ref-envs-when-subsetp-first
    (implies (subsetp-equal (svar-override-triplelist->refvars x)
                            (alist-keys (svex-env-fix ref-env)))
             (equal (svar-override-triplelist-env-ok x override-env (append ref-env ref-env2))
                    (svar-override-triplelist-env-ok x override-env ref-env)))
    :hints(("Goal" :in-theory (enable svar-override-triplelist->refvars)))))

(local (defthmd svex-env-boundp-iff-member-svex-env-alist-keys
         (iff (svex-env-boundp v env)
              (member-equal (svar-fix v) (alist-keys (svex-env-fix env))))
         :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-fix alist-keys)))))

(local (defthm car-of-nthcdr
         (equal (car (nthcdr n x)) (nth n x))))
(local (defthm cdr-of-nthcdr
         (equal (cdr (nthcdr n x)) (nthcdr n (cdr x)))))
(local (in-theory (disable acl2::nthcdr-of-cdr)))
(local (defthm nthcdr-of-nil
         (equal (nthcdr n nil) nil)))
(local (defthm consp-of-nthcdr
         (iff (consp (nthcdr n x))
              (< (nfix n) (len x)))))

(local (defun nth-of-base-fsm-eval-ind (n ins st fsm)
         (if (zp n)
             (list ins st fsm)
           (nth-of-base-fsm-eval-ind (1- n) (cdr ins)
                                     (base-fsm-step (car ins) st fsm)
                                     fsm))))

(local (Defthm svex-env-lookup-when-not-bound
         (implies (not (svex-env-boundp k x))
                  (equal (svex-env-lookup k x) (4vec-x)))
         :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp)))))

(local (defthm svex-envs-equivalent-of-extract-keys
         (implies (equal keys (alist-keys (svex-env-fix x)))
                  (svex-envs-equivalent (svex-env-extract keys x) x))
         :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                           svex-env-boundp-iff-member-svex-env-alist-keys)))))

(local (defthm base-fsm-final-state-of-take-n+1
         (implies (and (natp n)
                       ;; (no-duplicatesp-equal (svex-alist-keys (base-fsm->nextstate x)))
                       )
                  (svex-envs-equivalent
                   (base-fsm-final-state (take (+ 1 n) ins) prev-st x)
                   (base-fsm-step (nth n ins)
                                  (base-fsm-final-state (take n ins) prev-st x)
                                  x)))
         :hints(("Goal" :in-theory (e/d (take nth base-fsm-final-state)
                                        (acl2::take-of-too-many
                                         acl2::take-when-atom))
                 :induct (nth-of-base-fsm-eval-ind n ins prev-st x)
                 :expand ((take 1 ins)))
                (and stable-under-simplificationp
                     '(:in-theory (enable base-fsm-step))))))



(fty::deflist svar-override-triplelistlist :elt-type svar-override-triplelist :true-listp t)

(define svar->svex-override-triplelistlist ((x svar-override-triplelistlist-p)
                                            (values svex-alist-p))
  :returns (svex-triples svex-override-triplelistlist-p)
  (if (atom x)
      nil
    (cons (svar->svex-override-triplelist (car x) values)
          (svar->svex-override-triplelistlist (cdr x) values)))
  ///
  (defret len-of-<fn>
    (equal (len svex-triples)
           (len x))))

(define svar-override-triplelist-override-vars ((x svar-override-triplelist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (b* (((svar-override-triple x1) (car x)))
      (cons x1.testvar (cons x1.valvar (svar-override-triplelist-override-vars (cdr x))))))
  ///
  (defthm svex-override-triplelist-vars-of-svar->svex-override-triplelist
    (equal (svex-override-triplelist-vars (svar->svex-override-triplelist x values))
           (svar-override-triplelist-override-vars x))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars svar->svex-override-triplelist)))))


(define svar-override-triplelistlist-override-vars ((x svar-override-triplelistlist-p))
  :returns (vars svarlist-list-p)
  (if (atom x)
      nil
    (cons (svar-override-triplelist-override-vars (car x))
          (svar-override-triplelistlist-override-vars (cdr x))))
  ///
  (defthm svex-override-triplelistlist-vars-of-svar->svex-override-triplelistlist
    (equal (svex-override-triplelistlist-vars (svar->svex-override-triplelistlist x values))
           (svar-override-triplelistlist-override-vars x))
    :hints(("Goal" :in-theory (enable svex-override-triplelistlist-vars svar->svex-override-triplelistlist)))))


(define svar-override-triplelistlist-testvars ((x svar-override-triplelistlist-p))
  :returns (vars svarlist-list-p)
  (if (atom x)
      nil
    (cons (svar-override-triplelist->testvars (car x))
          (svar-override-triplelistlist-testvars (cdr x))))
  ///
  (defthm svex-override-triplelistlist-testvars-of-svar->svex-override-triplelistlist
    (equal (svex-override-triplelistlist-testvars (svar->svex-override-triplelistlist x values))
           (svar-override-triplelistlist-testvars x))
    :hints(("Goal" :in-theory (enable svex-override-triplelistlist-testvars svar->svex-override-triplelistlist)))))





(define append-svarlists ((x svarlist-list-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (svarlist-fix (car x))
            (append-svarlists (cdr x)))))

(define svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval ((cycle natp)
                                                             (triples svar-override-triplelistlist-p)
                                                             (envs svex-envlist-p)
                                                             (eval svex-envlist-p))
  :guard (<= cycle (len eval))
  :measure (nfix (- (len eval) (nfix cycle)))
  (if (zp (- (len eval) (lnfix cycle)))
      t
    (acl2::and* (or (svar-override-triplelist-env-ok (car triples)
                                                     (make-fast-alist (car envs))
                                                     (make-fast-alist (nth cycle eval)))
                    (cw "~x0: previous fails from cycle ~x1~%" std::__function__ cycle))
                (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval (+ 1 (lnfix cycle))
                                                                     (cdr triples)
                                                                     (cdr envs)
                                                                     eval)))
  ///
  (local (defun ind (cycle triples envs eval)
           (declare (xargs :measure (nfix (- (len eval) (nfix cycle)))))
           (if (zp (- (len eval) (nfix cycle)))
               (list triples envs)
             (ind (1+ (lnfix cycle)) (cdr triples) (cdr envs) eval))))

  (defthm svex-override-triplelist-env-ok-of-append-non-overrides
    (implies (not (intersectp-equal (svex-override-triplelist-vars triples)
                                    (alist-keys (svex-env-fix a))))
             (equal (svex-override-triplelist-env-ok
                     triples (append a b) prev-env)
                    (svex-override-triplelist-env-ok
                     triples b prev-env)))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-env-ok
                                      svex-override-triplelist-vars
                                      svex-env-boundp-iff-member-svex-env-alist-keys))))
  
  (defthm svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval-of-base-fsm-eval
    (implies (not (intersectp-equal (append-svarlists (svar-override-triplelistlist-override-vars triples))
                                    (svex-alist-keys (base-fsm->nextstate fsm))))
             (equal (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                     cycle triples envs (base-fsm-eval ins prev-st fsm))
                    (svex-override-triplelist-fsm-inputs-ok*
                     (svar->svex-override-triplelistlist triples (base-fsm->values fsm))
                     envs (nthcdr cycle ins)
                     (base-fsm-final-state (take cycle ins) prev-st fsm)
                     fsm)))
    :hints(("Goal" :in-theory (e/d (nth-of-base-fsm-eval
                                    base-fsm-step-outs
                                    append-svarlists
                                    svar-override-triplelistlist-override-vars
                                    base-fsm-step-env)
                                   (take))
            :induct (ind cycle triples envs ins) ;; bit of a hack but it works
            :expand ((:free (triples eval-ins prev-st) (svex-override-triplelist-fsm-inputs-ok* triples envs eval-ins prev-st fsm))
                     (:free (eval) (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                                    cycle triples envs eval))
                     (:free (values) (svar->svex-override-triplelistlist triples values))
                     (:free (values) (svar->svex-override-triplelistlist nil values))
                     (:free (values) (svar->svex-override-triplelist nil values)))))))







(define svex-envlist-removekeys ((vars svarlist-p)
                                 (envs svex-envlist-p))
  (if (atom envs)
      nil
    (cons (svex-env-removekeys vars (car envs))
          (svex-envlist-removekeys vars (cdr envs))))
  ///
  (defthm svex-envlist-removekeys-of-cons
    (Equal (svex-envlist-removekeys vars (cons env envs))
           (cons (svex-env-removekeys vars env)
                 (svex-envlist-removekeys vars envs))))

  (defthm svex-envlist-removekeys-of-append
    (Equal (svex-envlist-removekeys vars (append envs envs2))
           (append (svex-envlist-removekeys vars envs)
                   (svex-envlist-removekeys vars envs2)))))


(define svex-override-triplelist-fsm-inputs-ok ((triples svex-override-triplelist-p)
                                                (envs svex-envlist-p)
                                                (prev-envs svex-envlist-p)
                                                (initst svex-env-p)
                                                (fsm base-fsm-p))
  :guard (and (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate fsm)))
              (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate fsm)))))
  (if (atom envs)
      t
    (and (svex-override-triplelist-env-ok triples
                                          (base-fsm-step-env (car envs) initst fsm)
                                          (base-fsm-step-env (car prev-envs) initst fsm))
         (svex-override-triplelist-fsm-inputs-ok triples (cdr envs) (cdr prev-envs)
                                                 (base-fsm-step (car prev-envs) initst fsm)
                                                 fsm)))
  ///
  (defthm svex-override-triplelist-fsm-inputs-ok-of-cons
    (equal (svex-override-triplelist-fsm-inputs-ok triples
                                                   (cons env envs)
                                                   (cons prev-env prev-envs)
                                                   initst fsm)
           (and (svex-override-triplelist-env-ok triples
                                                 (base-fsm-step-env env initst fsm)
                                                 (base-fsm-step-env prev-env initst fsm))
                (svex-override-triplelist-fsm-inputs-ok triples envs prev-envs
                                                        (base-fsm-step prev-env initst fsm)
                                                        fsm))))

  (defthm svex-override-triplelist-fsm-inputs-ok-of-nil
    (equal (svex-override-triplelist-fsm-inputs-ok triples nil prev-envs initst fsm)
           t))

  (defthm svex-override-triplelist-fsm-inputs-ok-of-svex-alistlist-eval-cons
    (equal (svex-override-triplelist-fsm-inputs-ok triples
                                                   (svex-alistlist-eval (cons env-al env-als) env1)
                                                   prev-envs
                                                   initst fsm)
           (and (svex-override-triplelist-env-ok triples
                                                 (base-fsm-step-env (svex-alist-eval env-al env1) initst fsm)
                                                 (base-fsm-step-env (car prev-envs) initst fsm))
                (svex-override-triplelist-fsm-inputs-ok triples
                                                        (svex-alistlist-eval env-als env1)
                                                        (cdr prev-envs)
                                                        (base-fsm-step (car prev-envs) initst fsm)
                                                        fsm)))))



;; Same as svex-envlist-extract
;; (define svex-envlists-extract* ((vars svarlist-list-p)
;;                                 (envs svex-envlist-p))
;;   :returns (new-envs svex-envlist-p)
;;   (if (atom envs)
;;       nil
;;     (cons (svex-env-extract (car vars) (car envs))
;;           (svex-envlists-extract* (cdr vars) (cdr envs))))
;;   ///
;;   (defret len-of-<fn>
;;     (equal (len new-envs)
;;            (len envs)))

;;   (local (defun nth-ind (n vars envs)
;;            (if (zp n)
;;                (list vars envs)
;;              (nth-ind (1- n) (cdr vars) (cdr envs)))))
  
;;   (defret nth-of-<fn>
;;     (equal (nth n new-envs)
;;            (and (< (nfix n) (len envs))
;;                 (svex-env-extract (nth n vars) (nth n envs))))
;;     :hints(("Goal" :in-theory (enable nth)
;;             :expand <call>
;;             :induct (nth-ind n vars envs)))))

(define svex-envlist-keys-no-1s*-p ((vars svarlist-list-p)
                                    (envs svex-envlist-p))
  (if (atom vars)
      t
    (and (svex-env-keys-no-1s-p (car vars) (car envs))
         (svex-envlist-keys-no-1s*-p (cdr vars) (cdr envs)))))
            

(local
 (defsection triplelist-vars-lemmas
   (defretd not-member-when-not-lookup-<fn>
     (implies (and (not (svex-override-triplelist-lookup var x))
                   (not (svex-override-triplelist-lookup-valvar var x)))
              (not (member-equal (svar-fix var) vars)))
     :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                       svex-override-triplelist-lookup-valvar
                                       svex-override-triplelist-lookup)))
     :fn svex-override-triplelist-vars)

   (Defthm member-vars-when-member-has-test-var
     (implies (and (member-equal trip (svex-override-triplelist-fix x))
                   (equal var (svex-override-triple->testvar trip)))
              (member-equal var (svex-override-triplelist-vars x)))
     :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                       svex-override-triplelist-fix))))

  

   (Defthm member-vars-when-member-has-valvar
     (implies (and (member-equal trip (svex-override-triplelist-fix x))
                   (equal var (svex-override-triple->valvar trip)))
              (member-equal var (svex-override-triplelist-vars x)))
     :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                       svex-override-triplelist-fix))))

   (defthm svex-override-triplelist-vars-subsetp-when-triples-subsetp
     (implies (subsetp-equal (svex-override-triplelist-fix x)
                             (svex-override-triplelist-fix y))
              (subsetp-equal (svex-override-triplelist-vars x)
                             (svex-override-triplelist-vars y)))
     :hints (("goal" :in-theory (e/d (acl2::subsetp-witness-rw)
                                     (not-member-when-not-lookup-svex-override-triplelist-vars
                                      member-vars-when-member-has-valvar
                                      member-vars-when-member-has-test-var))
              :use (;; (:instance not-lookup-when-not-member-svex-override-triplelist-vars
                    ;;  (x y) (var (acl2::subsetp-witness (svex-override-triplelist-vars x)
                    ;;                                    (svex-override-triplelist-vars y))))
                    (:instance member-vars-when-member-has-test-var
                     (trip (svex-override-triplelist-lookup
                            (acl2::subsetp-witness (svex-override-triplelist-vars x)
                                                   (svex-override-triplelist-vars y))
                            x))
                     (x (svex-override-triplelist-fix y))
                     (var (acl2::subsetp-witness (svex-override-triplelist-vars x)
                                                 (svex-override-triplelist-vars y))))
                    (:instance member-vars-when-member-has-valvar
                     (trip (svex-override-triplelist-lookup-valvar
                            (acl2::subsetp-witness (svex-override-triplelist-vars x)
                                                   (svex-override-triplelist-vars y))
                            x))
                     (x (svex-override-triplelist-fix y))
                     (var (acl2::subsetp-witness (svex-override-triplelist-vars x)
                                                 (svex-override-triplelist-vars y))))
                    (:instance not-member-when-not-lookup-svex-override-triplelist-vars
                     (x x) (var (acl2::subsetp-witness (svex-override-triplelist-vars x)
                                                       (svex-override-triplelist-vars y))))))))
  

   (local (in-theory (disable acl2::intersectp-equal-commute)))

   (defthmd not-intersectp-when-subsetp
     (implies (and (not (intersectp-equal x z))
                   (subsetp y x))
              (not (intersectp-equal y z)))
     :hints(("Goal" :in-theory (enable intersectp-equal subsetp))))
  
   (defthm svex-override-triple-subsetlistp-implies-not-intersectp
     (implies (and (svex-override-triple-subsetlist-p x triples)
                   (not (intersectp-equal (svex-override-triplelist-vars triples) vars)))
              (not (intersectp-equal (svex-override-triplelist-vars (car x)) vars)))
     :hints(("Goal" :in-theory (enable svex-override-triple-subsetlist-p
                                       not-intersectp-when-subsetp))))))

(encapsulate nil
  (local (defthm append-extract-removekeys
           (implies (and (not (intersectp-equal vars keys))
                         (svarlist-p vars)
                         (svarlist-p keys))
                    (equal (append (svex-env-extract keys x)
                                   (svex-env-removekeys vars y))
                           (svex-env-removekeys
                            vars (append (svex-env-extract keys x) y))))
           :hints(("Goal" :in-theory (enable svex-env-removekeys
                                             svex-env-extract)))))
  (local (in-theory (disable svex-env-removekeys-of-append)))

  (local (defthm base-fsm-step-env-of-removekeys
           (implies (and (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm))))
                         (svarlist-p vars))
                    (equal (base-fsm-step-env
                            (svex-env-removekeys vars in)
                            initst fsm)
                           (svex-env-removekeys vars
                                                (base-fsm-step-env in initst fsm))))
           :hints(("Goal" :in-theory (enable base-fsm-step-env)))))

  (defthm remove-override-vars-of-base-fsm-eval
    (b* ((vars (svex-override-triplelist-vars triples))
         (prev-envs (svex-envlist-removekeys vars envs))
         ((base-fsm fsm))
         (bad1 (svexlist-check-overridetriples (svex-alist-vals fsm.values) triples))
         (bad2 (svexlist-check-overridetriples (svex-alist-vals fsm.nextstate) triples)))
      (implies (and (not bad1)
                    (not bad2)
                    (no-duplicatesp-equal vars)
                    (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm))))
                    (svex-override-triplelist-fsm-inputs-ok triples envs prev-envs initst fsm))
               (equal (base-fsm-eval prev-envs initst fsm)
                      (base-fsm-eval envs initst fsm))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      svex-override-triplelist-fsm-inputs-ok
                                      svex-envlist-removekeys
                                      base-fsm-step
                                      base-fsm-step-outs)
            :induct (base-fsm-eval envs initst fsm))))


  (defun remove-override-vars-of-base-fsm-eval*-ind (triplelist envs initst fsm)
    (declare (xargs :measure (len envs)))
    (if (atom envs)
        (list triplelist initst fsm)
      (remove-override-vars-of-base-fsm-eval*-ind (cdr triplelist)
                                                  (cdr envs)
                                                  (base-fsm-step (svex-env-removekeys
                                                                  (svex-override-triplelist-vars (car triplelist))
                                                                  (car envs))
                                                                 initst fsm)
                                                  fsm)))

  (local (defthm svex-env-removekeys-when-keys-nil
           (equal (svex-env-removekeys nil env)
                  (svex-env-fix env))
           :hints(("Goal" :in-theory (enable svex-env-removekeys
                                             svex-env-fix)))))

  (local (defthm svex-envlist-removekeys*-when-keys-nil
           (equal (svex-envlist-removekeys* nil env)
                  (svex-envlist-fix env))
           :hints(("Goal" :in-theory (enable svex-envlist-removekeys*
                                             svex-envlist-fix)))))

  
  (defthm remove-override-vars-of-base-fsm-eval*
    (b* ((vars (svex-override-triplelist-vars triples))
         (varslist (svex-override-triplelistlist-vars triplelist))
         (prev-envs (svex-envlist-removekeys* varslist envs))
         ((base-fsm fsm))
         (bad1 (svexlist-check-overridetriples (svex-alist-vals fsm.values) triples))
         (bad2 (svexlist-check-overridetriples (svex-alist-vals fsm.nextstate) triples)))
      (implies (and (not bad1)
                    (not bad2)
                    (svex-override-triple-subsetlist-p triplelist triples)
                    (no-duplicatesp-equal vars)
                    (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm))))
                    (svex-override-triplelist-fsm-inputs-ok* triplelist envs prev-envs initst fsm))
               (equal (base-fsm-eval prev-envs initst fsm)
                      (base-fsm-eval envs initst fsm))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      svex-override-triplelist-fsm-inputs-ok*
                                      svex-override-triplelistlist-vars
                                      svex-envlist-removekeys*
                                      base-fsm-step
                                      base-fsm-step-outs)
            :expand ((:free (vars) (svex-envlist-removekeys* vars envs))
                     (:free (envs) (base-fsm-eval envs initst fsm)))
            :induct (remove-override-vars-of-base-fsm-eval*-ind triplelist envs initst fsm)))))



(define svex-envlists-append-corresp ((x svex-envlist-p)
                                      (y svex-envlist-p))
  :Returns (new svex-envlist-p)
  (if (atom x)
      nil
    (cons (append (svex-env-fix (car x))
                  (svex-env-fix (car y)))
          (svex-envlists-append-corresp (cdr x) (cdr y))))
  ///
  (defret len-of-<fn>
    (equal (len new) (len x)))

  (local (defun nth-ind (n x y)
           (if (zp n)
               (list x y)
             (nth-ind (1- n) (cdr x) (cdr y)))))

  (defret nth-of-<fn>
    (implies (< (nfix n) (len x))
             (equal (nth n new)
                    (append (svex-env-fix (nth n x))
                            (svex-env-fix (nth n y)))))
    :hints(("Goal" :in-theory (enable nth)
            :induct (nth-ind n x y)))))



(local (defthm svex-env-keys-keys-no-1s-p-of-append-extract
         (implies (not (intersectp-equal (svarlist-fix vars) (svarlist-fix extvars)))
                  (equal (svex-env-keys-no-1s-p vars (append (svex-env-extract extvars other) ins))
                         (svex-env-keys-no-1s-p vars ins)))
         :hints(("Goal" :in-theory (e/d (svex-env-keys-no-1s-p
                                         svarlist-fix intersectp-equal))))))

(local (defthm svex-env-keys-keys-no-1s-p-of-step-env
         (implies (not (intersectp-equal (svarlist-fix vars) (svex-alist-keys (base-fsm->nextstate fsm))))
                  (equal (svex-env-keys-no-1s-p vars (base-fsm-step-env ins initst fsm))
                         (svex-env-keys-no-1s-p vars ins)))
         :hints(("Goal" :in-theory (enable base-fsm-step-env)))))


(local (defthm svex-override-triplelist-testvars-subset-of-vars-lemma
         (subsetp-equal (svex-override-triplelist-testvars x)
                        (svex-override-triplelist-vars x))
         :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                           svex-override-triplelist-testvars)))))

(local (defthm svex-override-triplelist-testvars-subset-of-vars
         (implies (subsetp-equal (svex-override-triplelist-vars x) vars)
                  (subsetp-equal (svex-override-triplelist-testvars x) vars))
         :hints (("goal" :use svex-override-triplelist-testvars-subset-of-vars-lemma
                  :in-theory (disable svex-override-triplelist-testvars-subset-of-vars-lemma)))))



(local (defthm base-fsm-step-env-of-append-extract-nonstates
         (implies (and (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm))))
                       (svarlist-p vars))
                  (svex-envs-equivalent
                   (base-fsm-step-env
                    (append (svex-env-extract vars in) in2)
                    initst fsm)
                   (append (svex-env-extract vars in)
                           (base-fsm-step-env in2 initst fsm))))
         :hints(("Goal" :in-theory (enable base-fsm-step-env
                                           svex-envs-equivalent)))))

(defsection un-append-override-vars-of-base-fsm-eval*
  (local (defun un-append-override-vars-of-base-fsm-eval*-ind (triplelist prev-envs override-envs initst fsm)
           (declare (xargs :measure (len prev-envs)))
           (if (atom prev-envs)
               (list override-envs triplelist initst fsm)
             (un-append-override-vars-of-base-fsm-eval*-ind
              (cdr triplelist)
              (cdr prev-envs)
              (cdr override-envs)
              (base-fsm-step (car prev-envs) initst fsm)
              fsm))))


  

  (in-theory (disable acl2::intersectp-equal-commute))
  

  (local (defthm len-equal-0
           (equal (equal (len x) 0)
                  (not (consp x)))))
  
  (defthm un-append-override-vars-of-base-fsm-eval*
    (b* ((vars (svex-override-triplelist-vars triples))
         (varslist (svex-override-triplelistlist-vars triplelist))
         (envs (svex-envlists-append-corresp
                (svex-envlist-extract varslist override-envs)
                prev-envs))
         ((base-fsm fsm))
         (bad1 (svexlist-check-overridetriples (svex-alist-vals fsm.values) triples))
         (bad2 (svexlist-check-overridetriples (svex-alist-vals fsm.nextstate) triples)))
      (implies (and (not bad1)
                    (not bad2)
                    (equal (len override-envs) (len prev-envs))
                    (equal (len triplelist) (len prev-envs))
                    (svex-envlist-keys-no-1s*-p
                     (svex-override-triplelistlist-testvars triplelist)
                     prev-envs)
                    (svex-override-triple-subsetlist-p triplelist triples)
                    (no-duplicatesp-equal vars)
                    (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm))))
                    (svex-override-triplelist-fsm-inputs-ok* triplelist envs prev-envs initst fsm))
               (equal (base-fsm-eval envs initst fsm)
                      (base-fsm-eval prev-envs initst fsm))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      svex-override-triplelist-fsm-inputs-ok*
                                      svex-override-triplelistlist-vars
                                      svex-override-triplelistlist-testvars
                                      svex-envlist-removekeys*
                                      base-fsm-step
                                      base-fsm-step-outs
                                      svex-override-triple-subsetlist-p
                                      svexlist-check-overridetriples-when-subset
                                      not-intersectp-when-subsetp
                                      len)
            :expand ((:free (vars) (svex-envlist-extract vars override-envs))
                     (:free (envs1) (svex-envlists-append-corresp envs1 prev-envs))
                     (:free (vars) (svex-envlist-keys-no-1s*-p vars prev-envs))
                     (:free (envs) (base-fsm-eval envs initst fsm))
                     (:free (x) (svex-env-extract nil x)))
            :induct (un-append-override-vars-of-base-fsm-eval*-ind
                     triplelist prev-envs override-envs initst fsm)))))


(define svex-envlists-agree-except ((vars svarlist-list-p)
                                    (x svex-envlist-p)
                                    (y svex-envlist-p))
  :measure (+ (len x) (len y))
  (if (and (atom x) (atom y))
      t
    (and (svex-envs-agree-except (car vars) (car x) (car y))
         (svex-envlists-agree-except (cdr vars) (cdr x) (cdr y))))
  ///
  (local (in-theory (enable svarlist-list-fix svex-envlist-fix))))

(defsection base-fsm-eval-of-overrides

  (local (defun base-fsm-eval-of-overrides-ind (triplelist prev-envs envs initst fsm)
           (declare (xargs :measure (len prev-envs)))
           (if (atom prev-envs)
               (list envs triplelist initst fsm)
             (base-fsm-eval-of-overrides-ind
              (cdr triplelist)
              (cdr prev-envs)
              (cdr envs)
              (base-fsm-step (car prev-envs) initst fsm)
              fsm))))

  (local (defthm svex-envs-agree-except-of-base-fsm-step-env
           (implies (and (svex-envs-agree-except vars env1 env2))
                    (svex-envs-agree-except
                     vars
                     (base-fsm-step-env env1 initst fsm)
                     (base-fsm-step-env env2 initst fsm)))
           :hints (("goal" :in-theory (enable base-fsm-step-env))
                   (and stable-under-simplificationp
                        `(:expand (,(car (last clause)))
                          :in-theory (enable svex-envs-agree-except-implies))))))

  (defthm base-fsm-eval-of-overrides
    (b* ((vars (svex-override-triplelist-vars triples))
         (varslist (svex-override-triplelistlist-vars triplelist))
         ((base-fsm fsm))
         (bad1 (svexlist-check-overridetriples (svex-alist-vals fsm.values) triples))
         (bad2 (svexlist-check-overridetriples (svex-alist-vals fsm.nextstate) triples)))
      (implies (and (svex-override-triplelist-fsm-inputs-ok* triplelist envs prev-envs initst fsm)
                    (not bad1)
                    (not bad2)
                    (equal (len envs) (len prev-envs))
                    (equal (len triplelist) (len prev-envs))
                    (svex-envlist-keys-no-1s*-p
                     (svex-override-triplelistlist-testvars triplelist)
                     prev-envs)
                    (svex-envlists-agree-except varslist envs prev-envs)
                    (svex-override-triple-subsetlist-p triplelist triples)
                    (no-duplicatesp-equal vars)
                    (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm)))))
               (equal (base-fsm-eval prev-envs initst fsm)
                      (base-fsm-eval envs initst fsm))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      svex-override-triplelist-fsm-inputs-ok*
                                      svex-override-triplelistlist-vars
                                      svex-override-triplelistlist-testvars
                                      svex-envlist-removekeys*
                                      base-fsm-step
                                      base-fsm-step-outs
                                      svex-override-triple-subsetlist-p
                                      svexlist-check-overridetriples-when-subset
                                      not-intersectp-when-subsetp
                                      svex-alist-eval-when-svexlist-check-overridetriples-and-svex-envs-agree-except-overrides
                                      len)
            :expand ((:free (envs1) (svex-envlists-append-corresp envs1 prev-envs))
                     (:free (vars) (svex-envlist-keys-no-1s*-p vars prev-envs))
                     (:free (envs) (base-fsm-eval envs initst fsm))
                     (:free (varslist) (svex-envlists-agree-except varslist envs prev-envs))
                     (:free (x) (svex-env-extract nil x)))
            :induct (base-fsm-eval-of-overrides-ind
                     triplelist prev-envs envs initst fsm)))))





(define svar-override-triples-from-signal-names ((x svarlist-p)) ;; values of the FSM
  :returns (triples svar-override-triplelist-p)
  :prepwork ()
  (if (atom x)
      nil
    (cons (make-svar-override-triple :testvar (change-svar (car x) :override-test t)
                                     :valvar (change-svar (car x) :override-val t)
                                     :refvar (car x))
          (svar-override-triples-from-signal-names (cdr x)))))



(define svar-override-triplelists-from-signal-names ((x svarlist-list-p)) ;; values of the FSM
  :returns (triples svar-override-triplelistlist-p)
  :guard-hints (("goal" :in-theory (enable append-svarlists)))
  (if (atom x)
      nil
    (cons (svar-override-triples-from-signal-names (car x))
          (svar-override-triplelists-from-signal-names (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len triples) (len x))))








(local (include-book "std/osets/element-list" :dir :system))
(local (fty::deflist svarlist :elt-type svar-p :true-listp t :elementp-of-nil nil))

;; move somewhere
(define svex-alistlist-vars ((x svex-alistlist-p))
  :returns (vars (and (svarlist-p vars)
                      (set::setp vars)))
  (if (atom x)
      nil
    (union (svex-alist-vars (car x))
           (svex-alistlist-vars (cdr x))))
  ///
  
  (defthmd svex-alistlist-eval-when-envs-agree
    (implies (svex-envs-agree (svex-alistlist-vars x) env1 env2)
             (equal (svex-alistlist-eval x env1)
                    (svex-alistlist-eval x env2)))
    :hints(("Goal" :in-theory (enable svex-alistlist-eval svex-alistlist-vars
                                      svex-alist-eval-when-envs-agree)))))


  

;; move somewhere

(defcong svex-envs-similar equal (svex-alistlist-eval x env) 2
  :hints(("Goal" :in-theory (enable svex-alistlist-eval)))
  :package :function)

(defcong svex-envs-similar equal (svex-env-extract keys x) 2
  :hints(("Goal" :in-theory (enable svex-env-extract))))

(local
 (defthm svex-env-p-nth-of-svex-envlist-p
   (implies (svex-envlist-p x)
            (svex-env-p (nth n x)))
   :hints(("Goal" :in-theory (enable nth svex-envlist-p)))))


(define svtv-probealist/namemap-eval ((x svtv-probealist-p)
                                      (namemap svtv-name-lhs-map-p)
                                      (evals svex-envlist-p))
  :returns (eval svex-env-p)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (cons (svar-fix (caar x))
                    (b* (((svtv-probe p) (cdar x))
                         (lhs (cdr (hons-get p.signal (svtv-name-lhs-map-fix namemap)))))
                      (lhs-eval-zero lhs (nth p.time evals))))
              (svtv-probealist/namemap-eval (cdr x) namemap evals))
      (svtv-probealist/namemap-eval (cdr x) namemap evals)))
  ///
  (local (in-theory (enable svtv-probealist-fix))))



(fty::defmap svtv-rev-probealist :key-type svtv-probe :val-type svar :true-listp t)



(define svtv-pipeline-cycle-extract-override-triples ((namemap svtv-name-lhs-map-p)
                                                      (inputs svex-alist-p)
                                                      (overrides svex-alist-p)
                                                      (rev-probes svtv-rev-probealist-p)
                                                      (cycle natp))
  :returns (mv (triples svar-override-triplelist-p
                        "In the pipeline namespace -- NOT the namemap or FSM namespaces.")
               (vars svarlist-p
                     "In the FSM namespace; may contain duplicates."))
  (b* (((when (atom namemap)) (mv nil nil))
       ((unless (mbt (and (consp (car namemap))
                          (svar-p (caar namemap)))))
        (svtv-pipeline-cycle-extract-override-triples (cdr namemap) inputs overrides rev-probes cycle))
       ((cons signame lhs) (car namemap))
       (input-look (svex-fastlookup signame inputs))
       ((unless (and input-look (svex-case input-look :var)))
        (svtv-pipeline-cycle-extract-override-triples (cdr namemap) inputs overrides rev-probes cycle))
       (override-look (svex-fastlookup signame overrides))
       ((unless (and override-look (svex-case override-look :var)))
        (svtv-pipeline-cycle-extract-override-triples (cdr namemap) inputs overrides rev-probes cycle))
       (probe-look (hons-get (make-svtv-probe :signal signame :time cycle) rev-probes))
       ((unless probe-look)
        (svtv-pipeline-cycle-extract-override-triples (cdr namemap) inputs overrides rev-probes cycle))
       ((mv rest-triples rest-vars)
        (svtv-pipeline-cycle-extract-override-triples (cdr namemap) inputs overrides rev-probes cycle)))
    (mv (cons (make-svar-override-triple :testvar (svex-var->name override-look)
                                         :valvar (svex-var->name input-look)
                                         :refvar (cdr probe-look))
              rest-triples)
        (append (lhs-vars lhs) rest-vars)))
  ///
  (local (in-theory (enable svtv-name-lhs-map-fix))))

(define svtv-pipeline-extract-override-triples ((namemap svtv-name-lhs-map-p)
                                                (inputs svex-alistlist-p)
                                                (overrides svex-alistlist-p)
                                                (rev-probes svtv-rev-probealist-p)
                                                (cycle natp))
  :measure (+ (len inputs) (len overrides))
  :returns (mv (triples svar-override-triplelist-p
                        "In the pipeline namespace -- NOT the namemap or FSM namespaces.")
               (vars svarlist-list-p
                     "In the FSM namespace, and listed by cycle."))
  :prepwork ((local (defthm svar-override-triplelist-p-implies-true-listp
                      (implies (svar-override-triplelist-p x)
                               (true-listp x)))))
  (b* (((when (and (atom inputs) (atom overrides))) (mv nil nil))
       ((mv rest-triples rest-vars)
        (svtv-pipeline-extract-override-triples
         namemap (cdr inputs) (cdr overrides) rev-probes (1+ (lnfix cycle))))
       (in (car inputs))
       (ov (car overrides))
       ((acl2::with-fast in ov))
       ((mv first-triples first-vars)
        (svtv-pipeline-cycle-extract-override-triples
         namemap in ov rev-probes cycle)))
    (mv (append first-triples rest-triples)
        (cons (mergesort first-vars) rest-vars))))






(define svtv-pipeline-override-triples-extract ((triples svar-override-triplelist-p)
                                                (ref-values svex-env-p))
  :returns (values svex-env-p)
  (if (atom triples)
      nil
    (b* (((svar-override-triple trip) (car triples))
         ((unless (svex-env-boundp trip.refvar ref-values))
          (svtv-pipeline-override-triples-extract (cdr triples) ref-values)))
      (cons (cons trip.valvar (svex-env-lookup trip.refvar ref-values))
            (svtv-pipeline-override-triples-extract (cdr triples) ref-values))))
  ///
  (local (defthm svex-env-boundp-of-cons-2
           (equal (svex-env-boundp key (cons pair rest))
                  (if (and (consp pair) (equal (svar-fix key) (car pair)))
                      t
                    (svex-env-boundp key rest)))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))
  (local (defthm svex-env-lookup-of-cons2
           (equal (svex-env-lookup v (cons x y))
                  (if (and (consp x)
                           (svar-p (car x))
                           (equal (car x) (svar-fix v)))
                      (4vec-fix (cdr x))
                    (svex-env-lookup v y)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
  
  (defcong svex-envs-equivalent svex-envs-equivalent (svtv-pipeline-override-triples-extract triples ref-values) 2
    :hints (("goal" :induct (svtv-pipeline-override-triples-extract triples ref-values))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable svex-env-boundp-of-cons-2
                                      svex-env-lookup-of-cons2))))
    :package :function)
  
  (defret keys-of-<fn>-strict
    (implies (subsetp-equal (svar-override-triplelist->refvars triples)
                            (alist-keys (svex-env-fix ref-values)))
             (equal (alist-keys values) (svar-override-triplelist->valvars triples)))
    :hints(("Goal" :in-theory (enable alist-keys
                                      svar-override-triplelist->valvars
                                      svar-override-triplelist->refvars
                                      svex-env-boundp))))

  (defret boundp-of-<fn>
    (implies (subsetp-equal (svar-override-triplelist->refvars triples)
                            (alist-keys (svex-env-fix ref-values)))
             (iff (svex-env-boundp var values)
                  (svar-override-triplelist-lookup-valvar var triples)))
    :hints(("Goal" :in-theory (enable svar-override-triplelist-lookup-valvar
                                      svar-override-triplelist->refvars)
            :induct <call>)
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-boundp)))))

  (defret lookup-of-<fn>
    (implies (subsetp-equal (svar-override-triplelist->refvars triples)
                            (alist-keys (svex-env-fix ref-values)))
             (equal (svex-env-lookup var values)
                    (b* ((look (svar-override-triplelist-lookup-valvar var triples)))
                      (if look
                          (svex-env-lookup (svar-override-triple->refvar look) ref-values)
                        (4vec-x)))))
    :hints(("Goal" :in-theory (enable svar-override-triplelist-lookup-valvar
                                      svar-override-triplelist->refvars)
            :induct <call>)
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-boundp))))))


(define svtv-name-lhs-map-eval-list ((namemap svtv-name-lhs-map-p)
                                     (envs svex-envlist-p))
  :returns (new-envs svex-envlist-p)
  (if (atom envs)
      nil
    (cons (svtv-name-lhs-map-eval namemap (car envs))
          (svtv-name-lhs-map-eval-list namemap (cdr envs))))
  ///
  (defret nth-of-<fn>
    (equal (nth n new-envs)
           (and (< (lnfix n) (len envs))
                (svtv-name-lhs-map-eval namemap (nth n envs))))
    :hints(("Goal" :in-theory (enable nth)
            :induct (nth n envs)))))


(local (Defthm svex-env-lookup-of-svtv-name-lhs-map-eval
         (equal (svex-env-lookup key (svtv-name-lhs-map-eval namemap env))
                (b* ((look (hons-assoc-equal (svar-fix key) namemap)))
                  (if look
                      (lhs-eval-zero (cdr look) env)
                    (4vec-x))))
         :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval
                                           svtv-name-lhs-map-fix
                                           svex-env-lookup-of-cons)))))

(define svtv-pipeline-override-triples-extract-values ((triples svar-override-triplelist-p)
                                                       (probes svtv-probealist-p)
                                                       (namemap svtv-name-lhs-map-p)
                                                       (evals svex-envlist-p))
  :returns (values svex-env-p)
  (b* (((when (atom triples)) nil)
       ((svar-override-triple trip) (car triples))
       (probe-look (hons-get trip.refvar (svtv-probealist-fix probes)))
       ((unless probe-look)
        (svtv-pipeline-override-triples-extract-values (cdr triples) probes namemap evals))
       ((svtv-probe probe) (cdr probe-look))
       (lhs-look (hons-get probe.signal (svtv-name-lhs-map-fix namemap)))
       ;; ((unless lhs-look)
       ;;  (svtv-pipeline-override-triples-extract-values (cdr triples) probes namemap evals))
       (eval (if lhs-look
                 (lhs-eval-zero (cdr lhs-look) (nth probe.time evals))
               (4vec-x))))
    (cons (cons trip.valvar eval)
          (svtv-pipeline-override-triples-extract-values (cdr triples) probes namemap evals)))
  ///
  

  (local (defthm svex-env-boundp-of-cons-2
           (equal (svex-env-boundp key (cons pair rest))
                  (if (and (consp pair) (equal (svar-fix key) (car pair)))
                      t
                    (svex-env-boundp key rest)))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))
  
  (local (Defthm svex-env-boundp-of-svtv-name-lhs-map-eval
           (iff (svex-env-boundp var (svtv-name-lhs-map-eval namemap env))
                (hons-get (svar-fix var) (svtv-name-lhs-map-fix namemap)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval
                                             svtv-name-lhs-map-fix)))))

  (local (defthm len-of-svtv-probealist-outvars-gte-time
           (implies (and (hons-assoc-equal var (svtv-probealist-fix probes)))
                    (< (svtv-probe->time (cdr (hons-assoc-equal var (svtv-probealist-fix probes))))
                       (len (svtv-probealist-outvars probes))))
           :hints(("Goal" :in-theory (enable svtv-probealist-outvars
                                             svtv-probealist-fix)))
           :rule-classes :linear))
  
  (defret <fn>-in-terms-of-svtv-probealist-extract
    (implies (<= (len (svtv-probealist-outvars probes)) (len evals))
             (equal values
                    (svtv-pipeline-override-triples-extract
                     triples (svtv-probealist-extract
                              probes (svtv-name-lhs-map-eval-list namemap evals)))))
    :hints(("Goal" :in-theory (enable svtv-pipeline-override-triples-extract)
            :induct <call>)))

  (local
   (defretd keys-of-<fn>-lemma
     (subsetp-equal (alist-keys values) (svar-override-triplelist->valvars triples))
     :hints(("Goal" :in-theory (enable alist-keys)))))

  (defret keys-of-<fn>
    (implies (subsetp-equal (svar-override-triplelist->valvars triples) vars)
             (subsetp-equal (alist-keys values) vars))
    :hints (("goal" :use keys-of-<fn>-lemma)))

  
  (local (defthm hons-assoc-equal-member-alist-keys
           (iff (hons-assoc-equal k x)
                (member-equal k (alist-keys x)))
           :hints(("Goal" :in-theory (enable alist-keys)))))
  
  (defret keys-of-<fn>-strict
    (implies (subsetp-equal (svar-override-triplelist->refvars triples)
                            (alist-keys (svtv-probealist-fix probes)))
             (equal (alist-keys values) (svar-override-triplelist->valvars triples)))
    :hints(("Goal" :in-theory (enable alist-keys
                                      svar-override-triplelist->valvars
                                      svar-override-triplelist->refvars
                                      acl2::alist-keys-member-hons-assoc-equal))))

  (local (defthm nth-out-of-bounds
           (implies (<= (len x) (nfix n))
                    (equal (nth n x) nil)))))



(defconst *overrides-crux-thm-template*
  '(encapsulate nil
     (local (in-theory nil))
     (make-event
      (if (fgetprop 'logand-mask-out-notnice 'acl2::untranslated-theorem nil (w state))
          (value '(value-triple :ok))
        (mv "~%Include-book \"centaur/sv/svtv/svtv-fsm-override-fgl-theory\" :dir :system before trying to run this event"
            nil state)))

     (local
      (make-event
       (b* ((?a (make-fast-alist (base-fsm->values (svtv-data-obj->cycle-fsm (<export>)))))
            (?b (make-fast-alist (base-fsm->nextstate (svtv-data-obj->cycle-fsm (<export>)))))
            (?c (make-fast-alist (svtv->outexprs (<name>)))))
         '(value-triple :ok))))
     
     ;; just a heuristic, should at least allow user override
     (local
      (defconsts (*<name>-pipeline-override-triples* *<name>-fsm-cycle-override-signals*)
        (b* ((namemap (make-fast-alist (svtv-data-obj->namemap (<export>))))
             ((pipeline-setup pipe) (svtv-data-obj->pipeline-setup (<export>)))
             (rev-probes (make-fast-alist (pairlis$ (alist-vals pipe.probes) (alist-keys pipe.probes))))
             ((mv triples signals)
              (svtv-pipeline-extract-override-triples
               namemap pipe.inputs  pipe.overrides rev-probes 0)))
          (fast-alist-free rev-probes)
          (mv triples signals))))

     (make-event
      `(defund <name>-pipeline-override-triples ()
         (declare (Xargs :guard t))
         ',*<name>-pipeline-override-triples*))

     (local
      (progn
        (make-event
         `(defund <name>-fsm-cycle-override-signals ()
            (declare (Xargs :guard t))
            ',*<name>-fsm-cycle-override-signals*))
    
    
        (fgl::def-fgl-thm <name>-fsm-override-inputs-ok-lemma
          (b* ((namemap (make-fast-alist (svtv-data-obj->namemap (<export>))))
               ((pipeline-setup pipe) (svtv-data-obj->pipeline-setup (<export>)))
               (fsm-triples (svar-override-triplelists-from-signal-names
                             (<name>-fsm-cycle-override-signals)))
               (fsm (svtv-data-obj->cycle-fsm (<export>)))
               (rename-fsm (make-svtv-fsm :base-fsm fsm :namemap namemap))
               (outvars (svtv-probealist-outvars pipe.probes))
               (substs (svtv-fsm-run-input-substs
                        (take (len outvars) pipe.inputs)
                        pipe.overrides rename-fsm)))
            (implies (equal (len spec-eval) (len outvars))
                     (b* ((spec-result (make-fast-alist
                                        (svtv-pipeline-override-triples-extract-values
                                         (<name>-pipeline-override-triples)
                                         (make-fast-alist pipe.probes)
                                         namemap spec-eval)))
                          (user-env (svex-env-append spec-result rest-env))
                          (final-envs
                           (svex-alistlist-eval substs user-env)))
                       (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                        0 fsm-triples final-envs spec-eval)))))
     
        (defthm <name>-fsm-override-inputs-ok
          (b* ((namemap (svtv-data-obj->namemap (<export>)))
               ((pipeline-setup pipe) (svtv-data-obj->pipeline-setup (<export>)))
               (fsm-triples (svar-override-triplelists-from-signal-names
                             (<name>-fsm-cycle-override-signals)))
               (fsm (svtv-data-obj->cycle-fsm (<export>)))
               (rename-fsm (make-svtv-fsm :base-fsm fsm :namemap namemap))
               (outvars (svtv-probealist-outvars pipe.probes))
               (substs (svtv-fsm-run-input-substs
                        (take (len outvars) pipe.inputs)
                        pipe.overrides rename-fsm)))
            (implies (and (equal (len spec-eval) (len outvars))
                          (svex-envs-agree
                                (svar-override-triplelist->valvars
                                 (<name>-pipeline-override-triples))
                                (svtv-pipeline-override-triples-extract-values
                                 (<name>-pipeline-override-triples)
                                 pipe.probes namemap spec-eval)
                                user-env))
                     (b* ((final-envs
                           (svex-alistlist-eval substs user-env)))
                       (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                        0 fsm-triples final-envs spec-eval))))
          :hints (("goal" :use ((:instance <name>-fsm-override-inputs-ok-lemma
                                 (rest-env user-env)))
                   :in-theory
                   '((:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ALISTLIST-EVAL-2)
                     (:DEFINITION MAKE-FAST-ALIST)
                     (:DEFINITION NOT)
                     (:EXECUTABLE-COUNTERPART SVAR-OVERRIDE-TRIPLELISTS-FROM-SIGNAL-NAMES)
                     (:REWRITE EVAL-OF-SVTV-FSM-RUN-INPUT-SUBSTS)
                     (:REWRITE svex-envs-similar-of-append-when-agree-on-keys-superset)
                     (:TYPE-PRESCRIPTION SVAR-OVERRIDE-TRIPLELIST-FSM-INPUTS-OK*-OF-FSM-EVAL)
                     (:REWRITE KEYS-OF-SVTV-PIPELINE-OVERRIDE-TRIPLES-EXTRACT-VALUES)
                     (:REWRITE SUBSETP-OF-SVAR-OVERRIDE-TRIPLELIST->VALVARS-WHEN-SUBSETP)
                     (:REWRITE ACL2::SUBSETP-REFL)
                     (:REWRITE SVARLIST-FIX-WHEN-SVARLIST-P)
                     (:REWRITE SVARLIST-P-OF-SVAR-OVERRIDE-TRIPLELIST->VALVARS)
                     (:REWRITE SVEX-ENV-FIX-WHEN-SVEX-ENV-P)
                     (:REWRITE SVEX-ENV-P-OF-SVTV-PIPELINE-OVERRIDE-TRIPLES-EXTRACT-VALUES)))))

        (defthm <name>-is-pipeline-result
          (equal (svtv->outexprs (<name>))
                 (svtv-data-obj->pipeline (<export>)))
          :hints(("Goal" :in-theory '((equal)(<name>)
                                      (<export>)
                                      (svtv->outexprs)
                                      (svtv-data-obj->pipeline)))))


        (defthm pipeline-validp-of-<export>
          (equal (svtv-data-obj->pipeline-validp (<export>)) t)
          :hints(("Goal" :in-theory '((<export>)
                                      (equal)
                                      (svtv-data-obj->pipeline-validp)))))



        (defthm <NAME>-fsm-override-vars-dont-intersect-states
          (not (intersectp-equal
                (append-svarlists
                 (svar-override-triplelistlist-override-vars
                  (svar-override-triplelists-from-signal-names
                   (<name>-fsm-cycle-override-signals))))
                (svex-alist-keys
                 (base-fsm->nextstate
                  (svtv-data-obj->cycle-fsm (<export>))))))
          :hints (("goal" :use ((:instance intersectp-svex-alist-keys-by-hons-intersect-p1
                                 (x (append-svarlists
                                     (svar-override-triplelistlist-override-vars
                                      (svar-override-triplelists-from-signal-names
                                       (<name>-fsm-cycle-override-signals)))))
                                 (y (base-fsm->nextstate
                                     (svtv-data-obj->cycle-fsm (<export>))))))
                   :in-theory '((<export>)
                                (<name>-fsm-cycle-override-signals)
                                (svar-override-triplelists-from-signal-names)
                                (svar-override-triplelistlist-override-vars)
                                (base-fsm->nextstate)
                                (svtv-data-obj->cycle-fsm)
                                (append-svarlists)
                                (svex-alist-fix)
                                (acl2::hons-intersect-p1)))))




        (defthm <NAME>-fsm-override-refvars-subsetp-values
          (subsetp-equal
           (svar-override-triplelistlist->all-refvars
            (svar-override-triplelists-from-signal-names
             (<name>-fsm-cycle-override-signals)))
           (svex-alist-keys
            (base-fsm->values
             (svtv-data-obj->cycle-fsm (<export>)))))
          :hints (("goal" :use ((:instance subsetp-svex-alist-keys-by-hons-subset1
                                 (x (svar-override-triplelistlist->all-refvars
                                     (svar-override-triplelists-from-signal-names
                                      (<name>-fsm-cycle-override-signals))))
                                 (y (base-fsm->values
                                     (svtv-data-obj->cycle-fsm (<export>))))))
                   :in-theory '((<export>)
                                (<name>-fsm-cycle-override-signals)
                                (svar-override-triplelists-from-signal-names)
                                (svar-override-triplelistlist->all-refvars)
                                (base-fsm->values)
                                (svtv-data-obj->cycle-fsm)
                                (svex-alist-fix)
                                (acl2::hons-subset1)))))

        (defthm <NAME>-pipeline-override-refvars-subsetp-probes
          (subsetp-equal
           (svar-override-triplelist->refvars
            (<NAME>-pipeline-override-triples))
           (alist-keys
            (pipeline-setup->probes
             (svtv-data-obj->pipeline-setup (<EXPORT>)))))
          :hints (("goal" :use ((:instance hons-subset1-is-subsetp-alist-keys
                                 (x (svar-override-triplelist->refvars
                                     (<NAME>-pipeline-override-triples)))
                                 (y (pipeline-setup->probes
                                     (svtv-data-obj->pipeline-setup (<EXPORT>))))))
                   :in-theory '((<NAME>-pipeline-override-triples)
                                (<EXPORT>)
                                (pipeline-setup->probes)
                                (svtv-data-obj->pipeline-setup)
                                (svar-override-triplelist->refvars)
                                (acl2::hons-subset1)))))


        (defthm <NAME>-no-duplicate-states
          (no-duplicatesp-equal
           (svex-alist-keys (base-fsm->nextstate
                             (svtv-data-obj->cycle-fsm
                              (<EXPORT>)))))
          :hints (("goal" :use ((:instance acl2::hons-dups-p-no-duplicatesp
                                 (x (svex-alist-keys (base-fsm->nextstate
                                                      (svtv-data-obj->cycle-fsm
                                                       (<EXPORT>)))))))
                   :in-theory '((<EXPORT>)
                                (svtv-data-obj->cycle-fsm)
                                (base-fsm->nextstate)
                                (svex-alist-keys)
                                (acl2::hons-dups-p)))))))

     (defthm <NAME>-no-val/testvar-intersect
       (not (intersectp-equal (svar-override-triplelist->valvars
                               (<NAME>-PIPELINE-OVERRIDE-TRIPLES))
                              (svar-override-triplelist->testvars
                               (<NAME>-PIPELINE-OVERRIDE-TRIPLES))))
       :hints (("goal" :use ((:instance acl2::hons-intersect-p-is-intersectp
                              (a (svar-override-triplelist->valvars
                                  (<NAME>-PIPELINE-OVERRIDE-TRIPLES)))
                              (b (svar-override-triplelist->testvars
                                  (<NAME>-PIPELINE-OVERRIDE-TRIPLES)))))
                :in-theory '((<NAME>-PIPELINE-OVERRIDE-TRIPLES)
                             (svar-override-triplelist->testvars)
                             (svar-override-triplelist->valvars)
                             (acl2::hons-intersect-p)))))


     (local
      (progn
        (defthm <NAME>-pipeline-override-valvars-dont-intersect-initst-vars
          (not (intersectp-equal (svar-override-triplelist->valvars
                                  (<NAME>-PIPELINE-OVERRIDE-TRIPLES))
                                 (svex-alist-vars
                                  (pipeline-setup->initst
                                   (svtv-data-obj->pipeline-setup
                                    (<EXPORT>))))))
          :hints (("goal" :use ((:instance acl2::hons-intersect-p-is-intersectp
                                 (a (svar-override-triplelist->valvars
                                     (<NAME>-PIPELINE-OVERRIDE-TRIPLES)))
                                 (b (svex-alist-vars
                                     (pipeline-setup->initst
                                      (svtv-data-obj->pipeline-setup
                                       (<export>)))))))
                   :in-theory '((<NAME>-PIPELINE-OVERRIDE-TRIPLES)
                                (<EXPORT>)
                                (svar-override-triplelist->valvars)
                                (svex-alist-vars)
                                (pipeline-setup->initst)
                                (svtv-data-obj->pipeline-setup)
                                (acl2::hons-intersect-p)))))

        (defthm <NAME>-pipeline-override-valvars-dont-intersect-initst-override-vars
          (not (intersectp-equal (svar-override-triplelist-override-vars
                                  (<NAME>-PIPELINE-OVERRIDE-TRIPLES))
                                 (svex-alist-vars
                                  (pipeline-setup->initst
                                   (svtv-data-obj->pipeline-setup
                                    (<EXPORT>))))))
          :hints (("goal" :use ((:instance acl2::hons-intersect-p-is-intersectp
                                 (a (svar-override-triplelist-override-vars
                                     (<NAME>-PIPELINE-OVERRIDE-TRIPLES)))
                                 (b (svex-alist-vars
                                     (pipeline-setup->initst
                                      (svtv-data-obj->pipeline-setup
                                       (<export>)))))))
                   :in-theory '((<NAME>-PIPELINE-OVERRIDE-TRIPLES)
                                (<EXPORT>)
                                (svar-override-triplelist-override-vars)
                                (svex-alist-vars)
                                (pipeline-setup->initst)
                                (svtv-data-obj->pipeline-setup)
                                (acl2::hons-intersect-p)))))

        (defthm <NAME>-pipeline-override-testvars-dont-intersect-initst-vars
          (not (intersectp-equal (svar-override-triplelist->testvars
                                  (<NAME>-PIPELINE-OVERRIDE-TRIPLES))
                                 (svex-alist-vars
                                  (pipeline-setup->initst
                                   (svtv-data-obj->pipeline-setup
                                    (<EXPORT>))))))
          :hints (("goal" :use ((:instance acl2::hons-intersect-p-is-intersectp
                                 (a (svar-override-triplelist->testvars
                                     (<NAME>-PIPELINE-OVERRIDE-TRIPLES)))
                                 (b (svex-alist-vars
                                     (pipeline-setup->initst
                                      (svtv-data-obj->pipeline-setup
                                       (<export>)))))))
                   :in-theory '((<NAME>-PIPELINE-OVERRIDE-TRIPLES)
                                (<EXPORT>)
                                (svar-override-triplelist->testvars)
                                (svex-alist-vars)
                                (pipeline-setup->initst)
                                (svtv-data-obj->pipeline-setup)
                                (acl2::hons-intersect-p)))))
                        

        (make-event
         `(defthm ncycles-of-<NAME>
            (equal (len (svtv-probealist-outvars
                         (pipeline-setup->probes
                          (svtv-data-obj->pipeline-setup (<EXPORT>)))))
                   ',(len (svtv-probealist-outvars
                           (pipeline-setup->probes
                            (svtv-data-obj->pipeline-setup (<EXPORT>))))))
            :hints(("Goal" :in-theory '((<export>)
                                        (len)
                                        (svtv-probealist-outvars)
                                        (pipeline-setup->probes)
                                        (svtv-data-obj->pipeline-setup))))))

        (make-event
         `(defthm ncycles-of-<name>-fsm-cycle-override-signals
            (equal (LEN (<NAME>-FSM-CYCLE-OVERRIDE-SIGNALS))
                   ',(LEN (<NAME>-FSM-CYCLE-OVERRIDE-SIGNALS)))
            :hints(("Goal" :in-theory '((len)
                                        (<name>-fsm-cycle-override-signals))))))

        (encapsulate nil
          (local
           (fgl::def-fgl-rewrite svex-env-lookup-when-svex-envs-agree-except-<NAME>
             (implies (and (syntaxp (equal env (fgl::g-var 'env)))
                           (bind-free `((vars . ,(fgl::g-concrete
                                                  (b* ((triples (<NAME>-PIPELINE-OVERRIDE-TRIPLES)))
                                                    (svar-override-triplelist-override-vars triples))))
                                        (prev-env . ,(fgl::g-var 'prev-env)))
                                      (vars prev-env))
                           (svex-envs-agree-except vars env prev-env)
                           (not (member-equal (svar-fix v) (svarlist-fix vars))))
                      (equal (svex-env-lookup v env)
                             (svex-env-lookup v prev-env)))
             :hints (("goal" :use ((:instance svex-env-lookup-when-svex-env-no-1s-p
                                    (vars vars) (x x) (v v)))
                      :in-theory (enable svex-envs-agree-except-implies)))))

          (local
           (fgl::def-fgl-rewrite svex-env-lookup-when-svex-env-no-1s-p-<NAME>
             (implies (and (syntaxp (equal x (fgl::g-var 'prev-env)))
                           (bind-free `((vars . ,(fgl::g-concrete
                                                  (svar-override-triplelist->testvars
                                                   (<NAME>-PIPELINE-OVERRIDE-TRIPLES)))))
                                      (vars))
                           (svex-env-keys-no-1s-p vars x)
                           (member-equal (svar-fix v) (svarlist-fix vars)))
                      (equal (svex-env-lookup v x)
                             (4vec-no-1s-fix (svex-env-no-1s-lookup v x))))
             :hints (("goal" :use ((:instance svex-env-lookup-when-svex-env-no-1s-p
                                    (vars vars) (x x) (v v)))))))




          (fgl::def-fgl-thm <NAME>-fsm-envs-ok-when-pipeline-envs-ok
            (B* ((NAMEMAP
                  (MAKE-FAST-ALIST
                   (SVTV-DATA-OBJ->NAMEMAP (<EXPORT>))))
                 ((PIPELINE-SETUP PIPE)
                  (SVTV-DATA-OBJ->PIPELINE-SETUP (<EXPORT>)))
                 (FSM-TRIPLES
                  (SVAR-OVERRIDE-TRIPLELISTS-FROM-SIGNAL-NAMES
                   (<NAME>-FSM-CYCLE-OVERRIDE-SIGNALS)))
                 (FSM (SVTV-DATA-OBJ->CYCLE-FSM (<EXPORT>)))
                 (RENAME-FSM (MAKE-SVTV-FSM :BASE-FSM FSM
                                            :NAMEMAP NAMEMAP))
                 (OUTVARS (SVTV-PROBEALIST-OUTVARS PIPE.PROBES))
                 (SUBSTS (SVTV-FSM-RUN-INPUT-SUBSTS
                          (TAKE (LEN OUTVARS) PIPE.INPUTS)
                          PIPE.OVERRIDES RENAME-FSM))
                 (triples (<NAME>-PIPELINE-OVERRIDE-TRIPLES)))
              (implies (and (svex-envs-agree-except (svar-override-triplelist-override-vars triples)
                                                    env prev-env)
                            (svex-env-keys-no-1s-p (svar-override-triplelist->testvars triples) prev-env))
                       (b* ((prev-env-eval
                             (make-fast-alists
                              (svex-alistlist-eval substs prev-env))))
                         (and (svex-envlists-agree-except
                               (svar-override-triplelistlist-override-vars fsm-triples)
                               (make-fast-alists
                                (svex-alistlist-eval substs env))
                               prev-env-eval)
                              (svex-envlist-keys-no-1s*-p
                               (svar-override-triplelistlist-testvars fsm-triples)
                               prev-env-eval)))))))

        (defund <name>-fsm-triple-set ()
          (svar->svex-override-triplelist (SVAR-OVERRIDE-TRIPLES-FROM-SIGNAL-NAMES
                                           (mergesort (append-lists 
                                                       (<NAME>-FSM-CYCLE-OVERRIDE-SIGNALS))))
                                          (base-fsm->values
                                           (svtv-data-obj->cycle-fsm (<export>)))))

        (defthm no-duplicate-vars-of-<name>-fsm-triple-set
          (no-duplicatesp-equal
           (svex-override-triplelist-vars (<name>-fsm-triple-set)))
          :hints (("goal" :in-theory '((svex-override-triplelist-vars)
                                       (<name>-fsm-triple-set)
                                       (acl2::hons-dups-p))
                   :use ((:instance acl2::hons-dups-p-no-duplicatesp
                          (x (svex-override-triplelist-vars (<name>-fsm-triple-set))))))))

        (defthm no-state-vars-of-<name>-fsm-triple-set
          (not (intersectp-equal
                (svex-override-triplelist-vars (<name>-fsm-triple-set))
                (svex-alist-keys
                 (base-fsm->nextstate
                  (svtv-data-obj->cycle-fsm
                   (<EXPORT>))))))
          :hints (("goal" :in-theory '((svex-override-triplelist-vars)
                                       (svex-alist-keys)
                                       (<name>-fsm-triple-set)
                                       (acl2::hons-intersect-p)
                                       (base-fsm->nextstate)
                                       (svtv-data-obj->cycle-fsm)
                                       (<export>))
                   :use ((:instance acl2::hons-intersect-p-is-intersectp
                          (a (svex-override-triplelist-vars (<name>-fsm-triple-set)))
                          (b (svex-alist-keys
                              (base-fsm->nextstate
                               (svtv-data-obj->cycle-fsm
                                (<EXPORT>))))))))))

        (defthm svex-override-triple-subsetlist-p-of-<name>-fsm-triple-set
          (svex-override-triple-subsetlist-p
           (svar->svex-override-triplelistlist
            (svar-override-triplelists-from-signal-names
             (<NAME>-FSM-CYCLE-OVERRIDE-SIGNALS))
            (base-fsm->values
             (svtv-data-obj->cycle-fsm (<export>))))
           (<name>-fsm-triple-set))
          :hints(("Goal" :in-theory '((svar->svex-override-triplelistlist)
                                      (base-fsm->values)
                                      (svtv-data-obj->cycle-fsm)
                                      (<export>)
                                      (svex-override-triple-subsetlist-p)
                                      (svar-override-triplelists-from-signal-names)
                                      (<name>-fsm-triple-set)
                                      (<name>-fsm-cycle-override-signals)))))



        (defthm svexlist-check-overridetriples-of-<name>-fsm-triple-set
          (and (not (svexlist-check-overridetriples
                     (svex-alist-vals
                      (base-fsm->values
                       (svtv-data-obj->cycle-fsm (<export>))))
                     (<name>-fsm-triple-set)))
               (not (svexlist-check-overridetriples
                     (svex-alist-vals
                      (base-fsm->nextstate
                       (svtv-data-obj->cycle-fsm (<export>))))
                     (<name>-fsm-triple-set))))
          :hints (("goal" :in-theory '((svexlist-check-overridetriples)
                                       (svex-alist-vals)
                                       (base-fsm->nextstate)
                                       (base-fsm->values)
                                       (svtv-data-obj->cycle-fsm)
                                       (<export>)
                                       (<name>-fsm-triple-set)))))
  
        (defthm base-fsm-eval-of-overrides-for-<name>
          (b* ((vars (svex-override-triplelist-vars triples))
               (varslist (svex-override-triplelistlist-vars triplelist))
               ((base-fsm fsm))
               (bad1 (svexlist-check-overridetriples (svex-alist-vals fsm.values) triples))
               (bad2 (svexlist-check-overridetriples (svex-alist-vals fsm.nextstate) triples)))
            (implies (and (bind-free '((triples . (<name>-fsm-triple-set))) (triples))
                          (svex-override-triplelist-fsm-inputs-ok* triplelist envs prev-envs initst fsm)
                          (not bad1)
                          (not bad2)
                          (equal (len envs) (len prev-envs))
                          (equal (len triplelist) (len prev-envs))
                          (svex-envlist-keys-no-1s*-p
                           (svex-override-triplelistlist-testvars triplelist)
                           prev-envs)
                          (svex-envlists-agree-except varslist envs prev-envs)
                          (svex-override-triple-subsetlist-p triplelist triples)
                          (no-duplicatesp-equal vars)
                          (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm)))))
                     (equal (base-fsm-eval envs initst fsm)
                            (base-fsm-eval prev-envs initst fsm))))
          :hints (("goal" :use base-fsm-eval-of-overrides)))


        (defthm <name>-initst-norm
          (b* ((triples (<NAME>-PIPELINE-OVERRIDE-TRIPLES))
               (override-vars (svar-override-triplelist-override-vars triples)))
            (implies (svex-envs-agree-except override-vars overrides-env spec-env)
                     (equal (svex-alist-eval
                             (pipeline-setup->initst
                              (svtv-data-obj->pipeline-setup (<export>)))
                             overrides-env)
                            (svex-alist-eval
                             (pipeline-setup->initst
                              (svtv-data-obj->pipeline-setup (<export>)))
                             spec-env))))
          :hints(("Goal" :in-theory '(<NAME>-pipeline-override-valvars-dont-intersect-initst-override-vars
                                      svarlist-fix-when-svarlist-p
                                      svarlist-p-of-svar-override-triplelist-override-vars
                                      svex-alist-eval-when-agree-except-non-intersecting))))

     
  
        (defthm probe-namemap-props-for-<name>
          (b* ((probes (pipeline-setup->probes
                        (svtv-data-obj->pipeline-setup (<export>))))
               (namemap (svtv-data-obj->namemap (<export>)))
               (fsm (svtv-data-obj->cycle-fsm (<export>))))
            (and (subsetp-equal (lhslist-vars (alist-vals
                                               (acl2::fal-extract
                                                (mergesort (svtv-probealist-all-outvars probes))
                                                namemap)))
                                (svex-alist-keys (base-fsm->values fsm)))
                 (subsetp-equal (svtv-probealist-all-outvars probes)
                                (alist-keys namemap))))
          :hints (("goal" :in-theory '(subsetp-equal-by-hons-subset
                                       (acl2::hons-subset)
                                       (lhslist-vars)
                                       (alist-vals)
                                       (alist-keys)
                                       (acl2::fal-extract)
                                       (mergesort)
                                       (svtv-probealist-all-outvars)
                                       (svtv-name-lhs-map-fix)
                                       (svex-alist-keys)
                                       (base-fsm->values)
                                       (pipeline-setup->probes)
                                       (svtv-data-obj->pipeline-setup)
                                       (svtv-data-obj->cycle-fsm)
                                       (svtv-data-obj->namemap)
                                       (<export>)))))))
  
  
     (defthm <NAME>-overrides-crux
       (b* ((spec-run (svtv-run  (<NAME>) spec-env))
            (triples (<NAME>-PIPELINE-OVERRIDE-TRIPLES))
            (testvars (svar-override-triplelist->testvars triples))
            (override-vars (svar-override-triplelist-override-vars triples))
            (valvars  (svar-override-triplelist->valvars triples))
            (overrides-run (svtv-run (<NAME>) overrides-env))
            (val-env (svtv-pipeline-override-triples-extract triples spec-run))
            )
         (implies (and
                   ;; none of these triples are overridden 
                   (svex-env-keys-no-1s-p testvars spec-env)
                   (svex-envs-agree-except override-vars overrides-env spec-env)
                   (svex-envs-agree valvars val-env overrides-env)
                   )
                  (svex-envs-equivalent overrides-run spec-run)))
       :hints(("Goal" :in-theory
               '(svex-envs-equivalent-is-an-equivalence
                 SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENVS-AGREE-2
                 SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENVS-AGREE-3
                 svex-envs-similar-is-an-equivalence
                 svex-envs-equivalent-refines-svex-envs-similar
                 SVEX-ENVS-EQUIVALENT-IMPLIES-SVEX-ENVS-EQUIVALENT-SVTV-PIPELINE-OVERRIDE-TRIPLES-EXTRACT-2
                 BASE-FSM-EVAL-BASE-FSM-EQUIV-CONGRUENCE-ON-X
                 BASE-FSM-EVAL-ENVS-BASE-FSM-EQUIV-CONGRUENCE-ON-X
                 BASE-FSM-EVAL-SVEX-ENVLIST-EQUIV-CONGRUENCE-ON-INS
                 ACL2::SET-EQUIV-IMPLIES-EQUAL-SUBSETP-1
                 SVEX-ENVS-EQUIVALENT-IMPLIES-SVEX-ENVS-EQUIVALENT-SVTV-PIPELINE-OVERRIDE-TRIPLES-EXTRACT-2
                 SVEX-OVERRIDE-TRIPLELIST-FSM-INPUTS-OK*-SVEX-ENV-EQUIV-CONGRUENCE-ON-INITST
                 SVTV-NAME-LHS-MAP-EVAL-LIST-SVTV-NAME-LHS-MAP-EQUIV-CONGRUENCE-ON-NAMEMAP
                 BASE-FSM-FINAL-STATE
                 BASE-FSM-RUN
                 HONS-COPY
                 MAKE-FAST-ALIST
                 NOT
                 ACL2::SVTV-RUN-FN
                 SYNP
                 (<)
                 (CONSP)
                 (EQUAL)
                 (NFIX)
                 (ZP)
                 ALIST-KEYS-OF-SVEX-ALIST-EVAL
                 BASE-FSM-EVAL-OF-OVERRIDES-FOR-<name>
                 BASE-FSM-EVAL-OF-SVTV-FSM->RENAMED-FSM
                 BASE-FSM-FIX-UNDER-BASE-FSM-EQUIV
                 EVAL-OF-SVTV-FSM-RUN-INPUT-SUBSTS
                 <EXPORT>-CORRECT
                 <NAME>-FSM-OVERRIDE-REFVARS-SUBSETP-VALUES
                 <NAME>-FSM-OVERRIDE-VARS-DONT-INTERSECT-STATES
                 <NAME>-INITST-NORM
                 <NAME>-IS-PIPELINE-RESULT
                 <NAME>-NO-DUPLICATE-STATES
                 FLATTEN-VALIDP-OF-<EXPORT>
                 LEN-OF-BASE-FSM-EVAL
                 LEN-OF-SVAR->SVEX-OVERRIDE-TRIPLELISTLIST
                 LEN-OF-SVAR-OVERRIDE-TRIPLELISTS-FROM-SIGNAL-NAMES
                 LEN-OF-SVEX-ALISTLIST-EVAL
                 LEN-OF-SVEX-ENVLISTS-APPEND-CORRESP
                 LEN-OF-SVTV-FSM-RUN-INPUT-ENVS
                 ACL2::LEN-OF-TAKE
                 ACL2::LIST-FIX-UNDER-LIST-EQUIV
                 MAKE-FAST-ALISTS-IS-IDENTITY
                 SET::MERGESORT-UNDER-SET-EQUIV
                 NCYCLES-OF-<NAME>
                 NCYCLES-OF-<NAME>-FSM-CYCLE-OVERRIDE-SIGNALS
                 NO-DUPLICATE-VARS-OF-<NAME>-FSM-TRIPLE-SET
                 NO-STATE-VARS-OF-<NAME>-FSM-TRIPLE-SET
                 nthcdr-0
                 PIPELINE-VALIDP-OF-<EXPORT>
                 PIPELINE-VALIDP-OF-SVTV-DATA-OBJ
                 PROBE-NAMEMAP-PROPS-FOR-<NAME>
                 RETURN-TYPE-OF-SVEX-ALIST-EVAL-FOR-SYMBOLIC
                 SVAR-OVERRIDE-TRIPLELIST-FSM-INPUTS-OK*-OF-FSM-EVAL-OF-APPEND-CORRESP
                 SVAR-OVERRIDE-TRIPLELIST-FSM-INPUTS-OK*-OF-FSM-EVAL-OF-BASE-FSM-EVAL
                 SVAR-OVERRIDE-TRIPLELISTLIST-REFVARS-BOUND-IN-ENVS-OF-BASE-FSM-EVAL
                 SVEX-ALIST-EVAL-OF-SVEX-ENV-FIX-ENV
                 SVEX-ENV-EXTRACT-WHEN-ALIST-KEYS-EQUAL
                 SVEX-ENV-FIX-UNDER-SVEX-ENV-EQUIV
                 SVEX-ENV-FIX-WHEN-SVEX-ENV-P
                 SVEX-ENV-P-OF-SVEX-ALIST-EVAL
                 SVEX-OVERRIDE-TRIPLE-SUBSETLIST-P-OF-<NAME>-FSM-TRIPLE-SET
                 SVEX-OVERRIDE-TRIPLELISTLIST-TESTVARS-OF-SVAR->SVEX-OVERRIDE-TRIPLELISTLIST
                 SVEX-OVERRIDE-TRIPLELISTLIST-VARS-OF-SVAR->SVEX-OVERRIDE-TRIPLELISTLIST
                 SVEXLIST-CHECK-OVERRIDETRIPLES-OF-<NAME>-FSM-TRIPLE-SET
                 SVTV-FSM->BASE-FSM-OF-SVTV-FSM
                 SVTV-FSM->NAMEMAP-OF-SVTV-FSM
                 SVTV-FSM-RUN-IS-BASE-FSM-RUN
                 SVTV-NAME-LHS-MAP-FIX-UNDER-SVTV-NAME-LHS-MAP-EQUIV
                 SVTV-NAME-LHS-MAP-FIX-WHEN-SVTV-NAME-LHS-MAP-P
                 SVTV-NAME-LHS-MAP-P-OF-SVTV-DATA-OBJ->NAMEMAP
                 SVTV-PIPELINE-OVERRIDE-TRIPLES-EXTRACT-VALUES-IN-TERMS-OF-SVTV-PROBEALIST-EXTRACT
                 SVTV-PROBEALIST-EXTRACT-OF-SVEX-ENVLIST-EXTRACT-OUTVARS
                 SVTV-PROBEALIST-EXTRACT-OF-SVTV-NAME-LHS-MAP-EVAL-OF-SVEX-ENVLISTS-APPEND-CORRESP-BASE-FSM-EVAL-WHEN-VARS-SUBSET-OF-VALUE-KEYS
                 ACL2::TAKE-OF-LEN-FREE
                 TAKE-OF-SVEX-ALISTLIST-EVAL
                 ACL2::TAKE-OF-ZERO
                 (:t SVEX-ENVLIST-KEYS-NO-1S*-P)
                 (:t SVEX-ENVLISTS-AGREE-EXCEPT)
                 (:t SVEX-ENVS-AGREE-EXCEPT)
                 (:t SVEX-ENVS-AGREE)
                 (:t SVEX-OVERRIDE-TRIPLELIST-FSM-INPUTS-OK*))
               :expand ((:free (st fsm) (base-fsm-final-state nil st fsm)))
               :use ((:instance <NAME>-fsm-override-inputs-ok
                      (spec-eval (b* (((pipeline-setup pipe)
                                       (SVTV-DATA-OBJ->PIPELINE-SETUP
                                        (<EXPORT>)))
                                      (cycle-fsm (SVTV-DATA-OBJ->CYCLE-FSM (<EXPORT>)))
                                      (svtv-fsm (SVTV-FSM
                                                 cycle-fsm
                                                 (SVTV-DATA-OBJ->NAMEMAP (<EXPORT>))))
                                      (ins (SVTV-FSM-RUN-INPUT-ENVS
                                            (TAKE
                                             (LEN
                                              (SVTV-PROBEALIST-OUTVARS pipe.probes))
                                             (SVEX-ALISTLIST-EVAL pipe.inputs
                                                                      SPEC-ENV))
                                            (SVEX-ALISTLIST-EVAL pipe.overrides
                                                                     SPEC-ENV)
                                            svtv-fsm))
                                      (initst (SVEX-ALIST-EVAL pipe.initst SPEC-ENV)))
                                   (svex-envlists-append-corresp
                                    (BASE-FSM-EVAL ins initst cycle-fsm)
                                    (base-fsm-eval-envs ins initst cycle-fsm))))
                      (user-env overrides-env
                                ;; (b* ((spec-run (svtv-run  (<NAME>) spec-env))
                                ;;      (triples (<NAME>-PIPELINE-OVERRIDE-TRIPLES))
                                ;;      (testvars (svar-override-triplelist->testvars triples))
                                ;;      ;; (valvars  (svar-override-triplelist->valvars triples))
                                ;;      )
                                ;;   (append
                                ;;    (svex-env-extract testvars tests-env)
                                ;;    (svtv-pipeline-override-triples-extract triples spec-run)
                                ;;    spec-env))
                                ))
                     (:instance <NAME>-fsm-envs-ok-when-pipeline-envs-ok
                      (env overrides-env) (prev-env spec-env)))
               :do-not-induct t))
       :otf-flg t)))

(defmacro def-svtv-overrides-crux (name export-name &key pkg-sym)
  (acl2::template-subst *overrides-crux-thm-template*
                        :atom-alist `((<export> . ,export-name))
                        :str-alist `(("<EXPORT>" . ,(symbol-name export-name))
                                     ("<NAME>" . ,(symbol-name name)))
                        :pkg-sym (or pkg-sym name)))
                        

(Defxdoc def-svtv-overrides-crux
  :parents (svtv-data)
  :short "Macro to prove a theorem showing that an SVTV's conditional overrides are \"correct\", i.e. can be eliminated."
  :long #{"""
<p>Usage:</p>
@({
 (def-svtv-overrides-crux <svtv-name> <export-name>)
 })

<p>Prerequisite: The SVTV must be defined with @(see defsvtv$) or @(see
defsvtv$-phasewise) (or otherwise result from populating a @(see svtv-data)
stobj), and the contents of the stobj thus populated must be exported into a
regular object @('<export-name>') using @('def-svtv-data-export').</p>

<p>This proves a theorem @('<svtv-name>-overrides-crux') showing that the
conditional overrides of the SVTV are correct, for cases where each conditional
override also corresponds to an output signal. E.g., if an SVTV has the
following outputs and overrides in some phase:</p>

@({
 :outputs (("foo" foo-ref))
 :overrides (("foo" (foo-ovr-val foo-ovr-test)))
 })

<p>then this theorem says (more or less) if the SVTV is run with any setting of
@('foo-ovr-test') and with @('foo-ovr-val') set to the same value that the
@('foo-ref') output produces, then this produces the same outputs of the SVTV
as if @('foo-ovr-test') were set to 0 (or X, or any value containing no 1-bits)
with any setting of @('foo-ovr-val').  That is, if you override a wire to its
own value, then it's just like not overriding it at all.</p>

<p>The overrides-crux theorem is stated in terms of a set of triples
relating the corresponding override test, override value, and reference
variable names, such as (in the above example) @('foo-ovr-test'),
@('foo-ovr-val'), @('foo-ref').  This is defined automatically by this macro,
exported as a 0-ary function named @('<svtv-name>-pipeline-override-triples').
The theorem says that if the following conditions are satisfied, then a run of
the SVTV on @('override-env') is equivalent to a run of the SVTV on @('spec-env'):</p>

<ol>

<li>In @('spec-env'), all the override-test variables of the triples are bound
to values containing no 1s (i.e., spec-env doesn't do any overrides).</li>

<li>@('spec-env') and @('override-env') agree on all variables except the
override-value and override-test variables of the triples (i.e. a lookup of any
other variable yields the same value in either env).</li>

<li>For each override triple, @('override-env') binds the triple's
override-value variable to the value of the triple's reference variable in the
the svtv-run on @('spec-env').  (Important distinction: its value in the
svtv-run on @('spec-env'), not its value in @('spec-env') itself.)</li>

</ol>

<p>Practically speaking, we want this theorem in order to generalize proofs
done using FGL with overrides. This requires a few further steps.  See @(see
def-svtv-overrides-correct) for a macro that helps with this.</p>

<h3>Notes on reasoning about overrides -- not necessary reading for most.</h3>

<p>In particular, a lot of this is described more simply here: @(see
def-svtv-overrides-correct).</p>

<p>For example, suppose we have proved the following lemma, where
@('opcode') is an input signal and @('partial-products') is a conditional
override with an output signal of the same name and test variable
@('override-partial-products'):</p>

@({
 (implies (and (equal opcode *mul-opcode*)
               (unsigned-byte-p 128 partial-products))
          (equal (svex-env-lookup 'product (svtv-run (multipler-svtv)
                                                     `((override-partial-products . -1)
                                                       (partial-products . ,partial-products)
                                                       (opcode . ,opcode))))
                 (sum-partial-products partial-products)))
 })

<p>We'd like to generalize this to:</p>

@({
 (let* ((spec-run (svtv-run (multipler-svtv) spec-env))
        (partial-products (svex-env-lookup 'partial-products spec-run)))
   (implies (and (no-override-tests-set spec-env)
                 (equal (svex-env-lookup 'opcode spec-env) *mul-opcode*)
                 (unsigned-byte-p 128 partial-products))
            (equal (svex-env-lookup 'product spec-run)
                   (sum-partial-products partial-products))))
 })

<p>We'd like to be able to use the overrides-crux theorem, setting
@('overrides-env') to the env used in the lemma.  But there are two potential
problems.</p>

<p>First, per hypothesis 2 of the
overrides-crux theorem, the two envs have to agree on all variables except
the override variables.  But in this case, variables that have nothing to do
with the theorem at hand are unbound (therefore X) in the override-env and
unspecified in the spec-env. (We don't want to assume them to be X in the
spec-env.  Why? Suppose partial-products is a function of inputs @('a'),
@('b'), and will be X if @('a') and @('b') are X -- then this would contradict
our assumption @('(unsigned-byte-p 128 partial-products)'), making our theorem
vacuous.)</p>

<p>Second, per hypothesis 3 of the overrides-crux theorem, the override-env
should bind each override value variable to the corresponding reference
variable's result from the spec run.  This is fine for
@('partial-products') (we can instantiate the lemma with partial-products set
to that value).  But if there are any other override triples besides the
partial-products one, they are not set in the env of the lemma.</p>

<p>Both of these can be fixed by appealing to the partial monotonicity of the
SVTV.  Generally, SVTVs created by the svtv-data process are known to be
monotonic in all variables except for override-tests, as long as the
@('monotonify') configuration option was set to @('t') (the default) in the
@('flatnorm') step. The @(see def-svtv-partial-monotonic) event can prove this
to be true for a given svtv.  This allows us to conclude:</p>

@({
 (implies (and (svex-env-<<= env1 env2)
               (svex-envs-agree (my-svtv-override-test-signals) env1 env2))
          (svex-env-<<= (svtv-run (my-svtv) env1)
                        (svtv-run (my-svtv) env2)))
 })

<p>The condition @('(svex-env-<<= a b)') means the value bound to a given
variable in @('a') is @('4vec-<<=') its value in @('b'), and @('(4vec-<<= v
w)') means that for every bit of @('v') that is non-X, the corresponding bit of
@('w') must have the same value. In particular, this means that if @('a') is a
2vec (integer) and @('(4vec-<<= a b)'), then @('b') equals @('a').  Since our
lemma says that the lookup of @('product') in our svtv-run is equal to
@('sum-partial-products') (an integer), this means if we look up @('product')
in a greater env we get the same value.  We can use this to construct an
@('override-env') that satisfies hypotheses 2 and 3 of the overrides-crux
theorem.</p>

<p>Note, however, the partial monotonicity theorem may specify a somewhat
different set of override test signals than the override-correct theorem.
Specifically, there could be conditional overrides that don't correspond to
reference outputs and therefore aren't among the triples referenced in
override-correct. Override-tests not in the triples will need to be restricted
to be the same in the envs used in the lemma and the generalized theorem.</p>

<p>So as an intermediate step in our generalization proof, we use partial
monotonicity of the SVTV to show that the lemma holds of an env
@('override-env') with the following properties relative to @('spec-env'),
@('spec-run') (the result of the svtv-run on @('spec-env'), and @('lemma-env')
-- the env from an instantiation of the lemma with all override value variables
set to their reference variables' values from spec-env:</p>

<ul>
<li>All override test variables are bound to the same values in @('override-env') as in @('lemma-env')</li>
<li>All override value variables are bound in @('override-env') to their corresponding reference variables' values from @('spec-run')</li>
<li>All other variables are bound in @('override-env') to the same values as in @('spec-env').</li>
</ul>

<p>Important facts about @('override-env'):</p>

<ul>

<li>@('(svex-env-<<= lemma-env override-env)') and they agree on the override
test signals, satisfying the hyps of the partial monotonicity theorem.
Therefore, the @('svtv-run') of @('lemma-env') is is @('<<=') the @('svtv-run')
of @('override-env').</li>

<li>It satisfies hyps 2 and 3 of override-correct by construction (it agrees
with spec-env on all variables except the override-tests and override-values,
and sets override-values to the reference variable values from @('spec-run')).
Therefore, we can apply @('override-correct') to show that its @('svtv-run')
equals @('spec-run').</li>
</ul>

<p>The above reasoning is formalized by the function
@('intermediate-override-env').  This function satisfies all the requirements
above provided the following technicalities are satisfied:</p>

<ul>

<li>The @('lemma-env'), omitting the override variable bindings, is
@('svex-env-<<=') the @('spec-env').  Effectively this means that at least
those input variables bound in the lemma-env are replicated in the
spec-env.</li>

<li>The reference variables of the override triples are a subset of the output
variables bound in @('spec-run').</li>

<li>The override value variable bindings of the @('lemma-env') are @('<<=') the
bindings of the respective reference vars in the @('spec-run').</li>

<li>The override-test variables referenced in the partial monotonicity theorem are a
superset of the test variables of the override triples referenced in the
override-correct theorem.</li>

<li>For any override-test variables from the monotonicity theorem that are not
test variables of the override triples, their bindings in @('lemma-env') and
@('spec-env') must be equal.</li>

<li>The override-test variables of the monotonicity theorem do not intersect
the override value variables of the triples.</li>

</ul>

"""}

)


(define intermediate-override-env ((triples svar-override-triplelist-p)
                                   (all-test-vars svarlist-p)
                                   (lemma-env svex-env-p)
                                   (spec-env svex-env-p)
                                   (spec-run svex-env-p))
  :returns (override-env svex-env-p)
  (append (svex-env-extract all-test-vars lemma-env)
          (svtv-pipeline-override-triples-extract triples spec-run)
          (svex-env-fix spec-env))
  ///
  (defret intermediate-override-env-agrees-with-lemma-env-on-test-vars
    (svex-envs-agree all-test-vars lemma-env override-env)
    :hints((and stable-under-simplificationp
                '(:in-theory (enable svex-envs-agree-by-witness)))))

  (local (defthm override-vars-under-set-equiv
           (acl2::set-equiv (svar-override-triplelist-override-vars x)
                            (append (svar-override-triplelist->valvars x)
                                    (svar-override-triplelist->testvars x)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist->valvars
                                             svar-override-triplelist->testvars
                                             svar-override-triplelist-override-vars)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable acl2::set-unequal-witness-rw))))))
  
  (defret intermediate-override-env-=>>-lemma-env
    (implies (and (svex-env-<<= (svex-env-removekeys
                                 (svar-override-triplelist-override-vars triples)
                                 lemma-env)
                                spec-env)
                  (subsetp-equal (svar-override-triplelist->refvars triples)
                                 (alist-keys (svex-env-fix spec-run)))
                  (svex-env-<<=
                   (svex-env-extract (svar-override-triplelist->valvars triples) lemma-env)
                   (svtv-pipeline-override-triples-extract triples spec-run))
                  (subsetp-equal (svar-override-triplelist->testvars triples)
                                 (svarlist-fix all-test-vars)))
             (svex-env-<<= lemma-env override-env))
    :hints ((and stable-under-simplificationp
                 (let* ((lit (car (last clause)))
                        (witness `(svex-env-<<=-witness . ,(cdr lit))))
                   `(:expand (,lit)
                     :use ((:instance svex-env-<<=-necc
                            (x (svex-env-removekeys
                                 (svar-override-triplelist-override-vars triples)
                                 lemma-env))
                            (y spec-env)
                            (var ,witness))
                           (:instance svex-env-<<=-necc
                            (x (svex-env-extract (svar-override-triplelist->valvars triples) lemma-env))
                            (y (svtv-pipeline-override-triples-extract triples spec-run))
                            (var ,witness))))))))

  (defret intermediate-override-env-agrees-with-spec-env-except-override-vars
    (implies (and (svex-envs-agree (set-difference-equal
                                    (svarlist-fix all-test-vars)
                                    (svar-override-triplelist->testvars triples))
                                   lemma-env spec-env)
                  (subsetp-equal (svar-override-triplelist->testvars triples)
                                 (svarlist-fix all-test-vars))
                  (subsetp-equal (svar-override-triplelist->refvars triples)
                                 (alist-keys (svex-env-fix spec-run))))
             (svex-envs-agree-except (svar-override-triplelist-override-vars triples)
                                     override-env spec-env))
    :hints ((and stable-under-simplificationp
                 (let* ((lit (car (last clause)))
                        (witness `(svex-envs-agree-except-witness . ,(cdr lit))))
                   `(:expand ((:with svex-envs-agree-except-by-witness ,lit))
                     :use ((:instance lookup-when-svex-envs-agree
                            (vars (set-difference-equal
                                    (svarlist-fix all-test-vars)
                                    (svar-override-triplelist->testvars triples)))
                            (x lemma-env) (y spec-env)
                            (v ,witness))))))))


  (defret intermediate-override-env-agrees-with-reference-vars
    (implies (and (not (intersectp-equal (svarlist-fix all-test-vars)
                                         (svar-override-triplelist->valvars triples)))
                  (subsetp-equal (svar-override-triplelist->refvars triples)
                                 (alist-keys (svex-env-fix spec-run))))
             (svex-envs-agree (svar-override-triplelist->valvars triples)
                              (svtv-pipeline-override-triples-extract triples spec-run)
                              override-env))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (car (last clause)))
                      (?witness `(svex-envs-disagree-witness . ,(cdr lit))))
                   `(:expand ((:with svex-envs-agree-by-witness ,lit))))))))


(defconst *svtv-overrides-correct-template*
  '(defsection <svtv>-full-overrides-thm

     (defthm <svtv>-refvars-subset-of-output-vars
       (subsetp-equal (svar-override-triplelist->refvars (<svtv>-pipeline-override-triples))
                      (svex-alist-keys (svtv->outexprs (<svtv>))))
       :hints(("Goal" :in-theory '(subsetp-svex-alist-keys-by-hons-subset1
                                   (acl2::hons-subset1)
                                   (svex-alist-fix)
                                   (svtv->outexprs)
                                   (<svtv>)
                                   (svar-override-triplelist->refvars)
                                   (<svtv>-pipeline-override-triples)))))

     (defthm <svtv>-pipeline-override-triple-testvars-subset-of-monotonicity-testvars
       (subsetp-equal (svar-override-triplelist->testvars (<svtv>-pipeline-override-triples))
                      (<svtv>-override-test-vars))
       :hints(("Goal" :in-theory '((svar-override-triplelist->testvars)
                                   (<svtv>-pipeline-override-triples)
                                   (<svtv>-override-test-vars)
                                   (acl2::hons-subset)
                                   subsetp-equal-by-hons-subset))))

     (make-event
      `(define <svtv>-non-triple-override-tests ()
         :returns (tests svarlist-p)
         ',(acl2::hons-set-diff (<svtv>-override-test-vars)
                                (svar-override-triplelist->testvars (<svtv>-pipeline-override-triples)))))

     (defthm <svtv>-non-triple-override-tests-is-set-difference
       (equal (<svtv>-non-triple-override-tests)
              (acl2::hons-set-diff (<svtv>-override-test-vars)
                                   (svar-override-triplelist->testvars (<svtv>-pipeline-override-triples))))
       :hints (("goal" :in-theory '((<svtv>-non-triple-override-tests)
                                    (acl2::hons-set-diff)
                                    (svar-override-triplelist->testvars)
                                    (<svtv>-pipeline-override-triples)
                                    (<svtv>-override-test-vars)))))

     (defthmd <svtv>-override-test-vars-under-set-equiv
       (acl2::set-equiv (<svtv>-override-test-vars)
                        (append (<svtv>-non-triple-override-tests)
                                (svar-override-triplelist->testvars (<svtv>-pipeline-override-triples))))
       :hints (("Goal" :in-theory '(append-set-diff-under-set-equiv
                                    acl2::set-equiv-is-an-equivalence
                                    <SVTV>-NON-TRIPLE-OVERRIDE-TESTS-IS-SET-DIFFERENCE
                                    <SVTV>-PIPELINE-OVERRIDE-TRIPLE-TESTVARS-SUBSET-OF-MONOTONICITY-TESTVARS
                                    acl2::hons-set-diff-is-set-difference$))))

     (defthm <svtv>-override-test-vars-not-intersect-valvars
       (not (intersectp-equal (<svtv>-override-test-vars)
                              (svar-override-triplelist->valvars (<svtv>-pipeline-override-triples))))
       :hints (("goal" :in-theory '(intersectp-by-hons-intersect-p
                                    (acl2::hons-intersect-p)
                                    (<svtv>-override-test-vars)
                                    (svar-override-triplelist->valvars)
                                    (<svtv>-pipeline-override-triples)))))
  
     (defthm <svtv>-overrides-correct
       (b* ((spec-run  (svtv-run (<svtv>) spec-env))
            (lemma-run (svtv-run (<svtv>) lemma-env))
            (triples (<svtv>-pipeline-override-triples)))
         (implies (and (svex-env-<<= (svex-env-removekeys
                                          (svar-override-triplelist-override-vars triples) lemma-env)
                                         spec-env)
                       (svex-env-<<=
                        (svex-env-extract (svar-override-triplelist->valvars triples) lemma-env)
                        (svtv-pipeline-override-triples-extract triples spec-run))
                       (svex-envs-agree (<svtv>-non-triple-override-tests)
                                            lemma-env spec-env)
                       (svex-env-keys-no-1s-p (svar-override-triplelist->testvars triples) spec-env))
                  (svex-env-<<= lemma-run spec-run)))
       :hints (("Goal" :use ((:instance <SVTV>-MONOTONICITY
                              (env1 lemma-env)
                              (env2 (intermediate-override-env
                                     (<svtv>-pipeline-override-triples)
                                     (<svtv>-override-test-vars)
                                     lemma-env spec-env
                                     (svtv-run (<svtv>) spec-env))))
                             (:instance <SVTV>-OVERRIDES-CRUX
                              (spec-env spec-env)
                              (overrides-env (intermediate-override-env
                                              (<svtv>-pipeline-override-triples)
                                              (<svtv>-override-test-vars)
                                              lemma-env spec-env
                                              (svtv-run (<svtv>) spec-env)))))
                :in-theory '(SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-2
                             ALIST-KEYS-OF-SVTV-RUN
                             <SVTV>-NON-TRIPLE-OVERRIDE-TESTS-IS-SET-DIFFERENCE
                             <SVTV>-REFVARS-SUBSET-OF-OUTPUT-VARS
                             <SVTV>-OVERRIDE-TEST-VARS-NOT-INTERSECT-VALVARS
                             <SVTV>-PIPELINE-OVERRIDE-TRIPLE-TESTVARS-SUBSET-OF-MONOTONICITY-TESTVARS
                             ACL2::HONS-SET-DIFF-IS-SET-DIFFERENCE$
                             INTERMEDIATE-OVERRIDE-ENV-=>>-LEMMA-ENV
                             INTERMEDIATE-OVERRIDE-ENV-AGREES-WITH-LEMMA-ENV-ON-TEST-VARS
                             INTERMEDIATE-OVERRIDE-ENV-AGREES-WITH-REFERENCE-VARS
                             INTERMEDIATE-OVERRIDE-ENV-AGREES-WITH-SPEC-ENV-EXCEPT-OVERRIDE-VARS
                             ACL2::SUBSETP-REFL
                             SVARLIST-FIX-WHEN-SVARLIST-P
                             SVARLIST-P-OF-<SVTV>-OVERRIDE-TEST-VARS
                             SVARLIST-P-OF-SET-DIFFERENCE
                             SVEX-ENV-FIX-WHEN-SVEX-ENV-P
                             ACL2::SVEX-ENV-P-OF-SVTV-RUN
                             SVEX-ENVS-AGREE-WHEN-SUBSET))))))

(defmacro def-svtv-overrides-correct (name &key pkg-sym)
  (acl2::template-subst *svtv-overrides-correct-template*
                        :atom-alist `((<svtv> . ,name))
                        :str-alist `(("<SVTV>" . ,(symbol-name name)))
                        :pkg-sym (or pkg-sym name)))



  

(Defxdoc def-svtv-overrides-correct
  :parents (svtv-data)
  :short "Macro to prove a theorem relating an SVTV run with overrides to a generalized one without them."
  :long #{"""
<p>Usage:</p>
@({
 (def-svtv-overrides-correct <svtv-name>)
 })

<p>Prerequisites: this requires the following two events to be done first.  See
@(see def-svtv-override-thms) which does all three:</p>
@({
 (def-svtv-partial-monotonic <svtv-name> <export-name>)
 (def-svtv-overrides-crux <svtv-name> <export-name>)
 })

<p>This proves a theorem giving sufficient conditions under which a lemma
involving an @(see svtv-run) using conditional overrides can be shown to imply
a more general theorem about an svtv-run without these overrides. The form of
the theorem is as follows:</p>

@({
 (b* ((spec-run  (svtv-run (<svtv>) spec-env))
      (lemma-run (svtv-run (<svtv>) lemma-env))
      (triples (<override-triples>)))
   (implies (and (svex-env-<<= (svex-env-removekeys
                                (svar-override-triplelist-override-vars triples) lemma-env)
                               spec-env)
                 (svex-env-<<=
                  (svex-env-extract (svar-override-triplelist->valvars triples) lemma-env)
                  (svtv-pipeline-override-triples-extract triples spec-run))
                 (svex-envs-agree (<non-triple-override-tests>)
                                  lemma-env spec-env)
                 (svex-env-keys-no-1s-p (svar-override-triplelist->testvars triples) spec-env))
            (svex-env-<<= lemma-run spec-run)))
 })

<p>We'll go through an example of how this might work.</p>


<p>Suppose that @('multiplier-svtv') is set up as follows:</p>
@({
 (defsvtv-phasewise multiplier-svtv
   :mod *multiplier-mod*
   :phases
    ((:label start
      :inputs (("clk" 0 :toggle 1)
               ("valid"  1)
               ("opcode" opcode)
               ("src1"   a)
               ("src2"   b)))

     (:label next :delay 2
      :outputs (("mul.part_prods" partial-products-ref))
      :overrides (("mul.part_prods" (partial-products override-partial-products))))

     (:label finish :delay 2
      :outputs (("mul_result" product)))))
 })

<p>Notice that #("mul.part_prods") is both an output and a conditional override
signal at the same phase. (It would be fine to name the output variable the
same as the override value variable; in this case we differentiate them for
clarity.)  As usual with multipliers, we'll prove the result correct by
splitting at the partial products.  In this case, suppose we prove the
following lemma:</p>

@({
 (def-fgl-thm partial-prods-to-product
   (implies (unsigned-byte-p 128 partial-products)
            (equal (svex-env-lookup 'product (svtv-run (multipler-svtv)
                                                       `((override-partial-products . -1)
                                                         (partial-products . ,partial-products)
                                                         (opcode . ,*mul-opcode*))))
                   (sum-partial-products partial-products))))
 })

<p>We'd like to generalize this so that we can compose it with a proof about
the partial product values.  A nice form of the generalized theorem would be
something like this:</p>

@({
 (defthm partial-prods-to-product-gen
    (let* ((run (svtv-run (multipler-svtv) env))
           (partial-products (svex-env-lookup 'partial-products run)))
      (implies (and (no-override-tests-set env)
                    (equal (svex-env-lookup 'opcode env) *mul-opcode*)
                    (unsigned-byte-p 128 partial-products))
               (equal (svex-env-lookup 'product run)
                      (sum-partial-products partial-products)))))
 })

<p>Our overrides-correct theorem can help prove something like this.  In
particular, we can instantiate our override theorem with @('spec-env') set to
@('env') and @('lemma-env') set to the following:</p>

@({
    `((override-partial-products . -1)
      (partial-products . ,(svex-env-lookup 'partial-products-ref (svtv-run (multipler-svtv) env)))
      (opcode . ,*mul-opcode*))
 })

<p>Here we've taken the env used in our lemma and instantiated the override
variable with the value of its reference variable from the run on the
generalized env.</p>

<p>The overrides-correct theorem refers to two additional 0-ary functions:
@('<override-triples>') and @('<non-triple-override-tests>'). The override
triples are defined by the @('def-svtv-overrides-crux') event and contain
triples of corresponding override test, override value, and reference output
variables.  We'll assume that @('override-partial-products'),
@('partial-products'), and @('partial-products-ref') is one such triple.  The
@('<non-triple-override-tests>') will often be @('nil'), but will otherwise
contain any override test variables not among the triples.</p>

<ul>
<li>The first hyp:
@({
   (svex-env-<<= (svex-env-removekeys
                  (svar-override-triplelist-override-vars triples) lemma-env)
                 spec-env)
 })
This says that for every variable other than the override-test and
override-value variables of the triples, lemma-env's binding is @('4vec-<<=') that of spec-env. This is satisfied because the only such variable bound in lemma-env is @('opcode'), and we've assumed its binding in spec-env to be the same.</li>

<li>The second hyp:
@({
  (svex-env-<<=
   (svex-env-extract (svar-override-triplelist->valvars triples) lemma-env)
   (svtv-pipeline-override-triples-extract triples spec-run))
 })
This says that for every override value variable of the triples, its binding in
@('lemma-env') is @('4vec-<<=') the value of its corresponding reference
variable from the @('svtv-run') with @('spec-env').  This is true because
@('partial-products') is bound to exactly that reference variable value in our
lemma-env, and no other override value variable of the triples is bound in
lemma-env, meaning they are all implicitly @('4vec-x') and therefore
@('4vec-<<=') any value.</li>

<li>The third hyp:
@({
  (svex-envs-agree (<non-triple-override-tests>)
                   lemma-env spec-env)
 })
says that any override test variables not among the triples must be bound to
the same value in @('lemma-env') and @('spec-env').  We don't have any that are
bound in @('lemma-env'), so if there were any such variables they would need to
be assumed to also be @('x') in spec-env.</li>

<li>The fourth hyp:
@({
  (svex-env-keys-no-1s-p (svar-override-triplelist->testvars triples) spec-env)
 })
should be assumed in the generalized theorem, instead of the placeholder hyp
@('(no-override-tests-set env)') above.</li>
</ul>

<p>Having satisfied the hyps of our override theorem, we then can assume that
the @('svtv-run') on the lemma-env is @('svex-env-<<=') the run of the
spec-env.  We can use this to prove our conclusion, since (presumably)
sum-of-partial-products returns an integer and this means any value greater in
the 4vec lattice must be equal.</p>

"""})


(defmacro def-svtv-override-thms (name export &key pkg-sym)
  `(progn
     (def-svtv-partial-monotonic ,name ,export :pkg-sym ,pkg-sym)
     (def-svtv-overrides-crux ,name ,export :pkg-sym ,pkg-sym)
     (def-svtv-overrides-correct ,name :pkg-sym ,pkg-sym)))

(defxdoc def-svtv-override-thms
  :parents (svtv-data)
  :short "Macro to prove several theorems about behavior of conditional overrides on an SVTV."
  :long "
<p>Usage:</p>
@({
 (def-svtv-override-thms <svtv-name> <export-name>)
 })

<p>Prerequisite: The SVTV must be defined with @(see defsvtv$) or @(see
defsvtv$-phasewise) (or otherwise result from populating a @(see svtv-data)
stobj), and the contents of the stobj thus populated must be exported into a
regular object @('<export-name>') using @('def-svtv-data-export').
Additionally, the setting for the @('monotonify') argument of the defsvtv$ form
must have been @('t') (the default).  The export object may be defined
locally.</p>

<p>This simply combines the @(see def-svtv-partial-monotonic), @(see
def-svtv-overrides-crux), and @(see def-svtv-overrides-correct) events.  See
@(see def-svtv-overrides-correct) for the highest-level theorem that is
proved.</p>")








#!sv
(defthmd 4vec-<<=-when-integerp
  (implies (integerp x)
           (equal (4vec-<<= x y)
                  (equal (4vec-fix y) x)))
  :hints(("Goal" :in-theory (e/d (4vec->upper 4vec->lower 4vec-fix)))))

#!sv
(defthmd svex-env-lookup-when-integerp-and-<<=
  (implies (and (svex-env-<<= env1 env2)
                (integerp (svex-env-lookup k env1)))
           (equal (svex-env-lookup k env2)
                  (svex-env-lookup k env1)))
  :hints (("goal" :use ((:instance svex-env-<<=-necc
                         (x env1) (y env2) (var k)))
           :in-theory (e/d (4vec-<<=-when-integerp)
                           (svex-env-<<=-necc)))))

#!sv
(defthmd svex-env-lookup-when-2vec-p-and-<<=
  (implies (and (svex-env-<<= env1 env2)
                (2vec-p (svex-env-lookup k env1)))
           (equal (svex-env-lookup k env2)
                  (svex-env-lookup k env1)))
  :hints (("goal" :use ((:instance svex-env-<<=-necc
                         (x env1) (y env2) (var k)))
           :in-theory (disable svex-env-<<=-necc))))

(encapsulate nil
  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
  (local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
  (local (defthm logbitp-of-logeqv
           (equal (logbitp n (logeqv x y))
                  (iff (logbitp n x) (logbitp n y)))))
  (local (in-theory (disable logeqv)))
  
  (local (defthm loghead-lemma
           (implies (and (equal -1 (logior (logand xu (lognot xl))
                                           (logand (logeqv xl yl)
                                                   (logeqv xu yu))))
                         (equal (loghead n xl)
                                (loghead n xu)))
                    (and (equal (loghead n yl) (loghead n xl))
                         (equal (loghead n yu) (loghead n xu))))
           :hints ((bitops::logbitp-reasoning))))
  
  (defthmd zero-ext-equal-when-4vec-<<=-and-2vec-p
    (implies (and (4vec-<<= x y)
                  (sv::2vec-p (sv::4vec-zero-ext n x)))
             (equal (sv::4vec-zero-ext n y)
                    (sv::4vec-zero-ext n x)))
    :hints(("Goal" :in-theory (e/d (sv::4vec-zero-ext 4vec-<<=))
            :do-not-induct t))
    :otf-flg t)

  (defthmd zero-ext-equal-when-4vec-<<=-and-integerp
    (implies (and (4vec-<<= x y)
                  (integerp (sv::4vec-zero-ext n x)))
             (equal (sv::4vec-zero-ext n y)
                    (sv::4vec-zero-ext n x)))
    :hints(("Goal" :in-theory (e/d (4vec->upper 4vec->lower 4vec-fix))
            :use zero-ext-equal-when-4vec-<<=-and-2vec-p)))


  (defthmd zero-ext-of-svex-env-lookup-when-integerp-and-<<=
    (implies (and (svex-env-<<= env1 env2)
                  (integerp (sv::4vec-zero-ext n (svex-env-lookup k env1))))
             (equal (sv::4vec-zero-ext n (svex-env-lookup k env2))
                    (sv::4vec-zero-ext n (svex-env-lookup k env1))))
    :hints (("goal" :use ((:instance svex-env-<<=-necc
                           (x env1) (y env2) (var k)))
             :in-theory (e/d (zero-ext-equal-when-4vec-<<=-and-integerp)
                             (svex-env-<<=-necc))))))


(encapsulate nil
  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
  (local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
  (local (defthm logbitp-of-logeqv
           (equal (logbitp n (logeqv x y))
                  (iff (logbitp n x) (logbitp n y)))))
  (local (in-theory (disable logeqv)))
  
  (local (defthm loghead-lemma
           (implies (and (equal -1 (logior (logand xu (lognot xl))
                                           (logand (logeqv xl yl)
                                                   (logeqv xu yu))))
                         (equal (loghead w (logtail lsb xl))
                                (loghead w (logtail lsb xu))))
                    (and (equal (loghead w (logtail lsb yl))
                                (loghead w (logtail lsb xl)))
                         (equal (loghead w (logtail lsb yu))
                                (loghead w (logtail lsb xu)))))
           :hints ((bitops::logbitp-reasoning :prune-examples nil))))

  (local (defthm loghead-logapp-vs-ash-lemma
           (implies (posp w2)
                    (equal (equal (loghead w (logapp w2 -1 x))
                                  (loghead w (ash y w2)))
                           (zp w)))
           :hints (("goal" :expand ((:free (x) (loghead w x)))))))
  
  (defthmd part-select-equal-when-4vec-<<=-and-2vec-p
    (implies (and (4vec-<<= x y)
                  (sv::2vec-p (sv::4vec-part-select lsb w x)))
             (equal (sv::4vec-part-select lsb w y)
                    (sv::4vec-part-select lsb w x)))
    :hints(("Goal" :in-theory (e/d (sv::4vec-part-select 4vec-zero-ext 4vec-rsh 4vec-shift-core 4vec-concat 4vec-<<=))
            :do-not-induct t))
    :otf-flg t)

  (defthmd part-select-equal-when-4vec-<<=-and-integerp
    (implies (and (4vec-<<= x y)
                  (integerp (sv::4vec-part-select lsb w x)))
             (equal (sv::4vec-part-select lsb w y)
                    (sv::4vec-part-select lsb w x)))
    :hints(("Goal" :in-theory (e/d (4vec->upper 4vec->lower 4vec-fix))
            :use part-select-equal-when-4vec-<<=-and-2vec-p)))


  (defthmd part-select-of-svex-env-lookup-when-integerp-and-<<=
    (implies (and (svex-env-<<= env1 env2)
                  (integerp (sv::4vec-part-select lsb w (svex-env-lookup k env1))))
             (equal (sv::4vec-part-select lsb w (svex-env-lookup k env2))
                    (sv::4vec-part-select lsb w (svex-env-lookup k env1))))
    :hints (("goal" :use ((:instance svex-env-<<=-necc
                           (x env1) (y env2) (var k)))
             :in-theory (e/d (part-select-equal-when-4vec-<<=-and-integerp)
                             (svex-env-<<=-necc))))))



#!sv
(cmr::def-force-execute member-equal-force-execute
  member-equal)

#!sv
(cmr::def-force-execute svar-override-triple->refvar-force-execute
  svar-override-triple->refvar)


#!sv
(cmr::def-force-execute hons-intersection-force-execute
  acl2::hons-intersection)

#!sv
(cmr::def-force-execute hons-set-diff-force-execute
  acl2::hons-set-diff)

#!sv
(cmr::def-force-execute svar-override-triplelist-lookup-valvar-force-execute
  svar-override-triplelist-lookup-valvar)

#!sv
(defthm svex-env-removekeys-of-nil-env
  (equal (svex-env-removekeys keys nil) nil)
  :hints(("Goal" :in-theory (enable svex-env-removekeys))))


#!sv
(define svex-env-<<=-each ((x svex-env-p)
                           (y svex-env-p))
  ;; Like svex-env-<<=, but iterates over the pairs in x rather than
  ;; quantifying over the keys.  So it's the same as svex-env-<<= as long as x
  ;; has no duplicate keys (or at least no duplicated keys bound to different
  ;; values).
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (svar-p (caar x)))))
             (4vec-<<= (cdar x) (svex-env-lookup (caar x) y)))
         (svex-env-<<=-each (cdr x) y)))
  ///
  (local (defthm svex-env-<<=-each-implies-4vec-<<=
           (implies (svex-env-<<=-each x y)
                    (4vec-<<= (svex-env-lookup k x)
                              (svex-env-lookup k y)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  (local (defthm svex-env-<<=-each-implies-svex-env-<<=
           (implies (svex-env-<<=-each x y)
                    (svex-env-<<= x y))
           :hints(("Goal" :expand ((svex-env-<<= x y))))))

  (local (defthm svex-env-<<=-cdr-when-first-key-not-repeated
           (implies (and (or (not (consp (car x)))
                             (not (svar-p (caar x)))
                             (not (svex-env-boundp (caar x) (cdr x))))
                         (svex-env-<<= x y))
                    (svex-env-<<= (cdr x) y))
           :hints (("Goal" :expand ((svex-env-<<= (cdr x) y))
                    :use ((:instance svex-env-<<=-necc
                           (var (svex-env-<<=-witness (cdr x) y))))
                    :in-theory (e/d (svex-env-lookup
                                     svex-env-boundp)
                                    (svex-env-<<=-necc))))))
  
  (local (defthm svex-env-<<=-and-no-duplicate-keys-implies-svex-env-<<=-each
           (implies (and (svex-env-<<= x y)
                         (no-duplicatesp-equal (alist-keys (svex-env-fix x))))
                    (svex-env-<<=-each x y))
           :hints(("Goal" :in-theory (e/d (svex-env-lookup
                                           svex-env-boundp
                                           acl2::alist-keys-member-hons-assoc-equal
                                           svex-env-fix)
                                          (svex-env-<<=-necc))
                   :induct t)
                  (and stable-under-simplificationp
                       '(:use ((:instance svex-env-<<=-necc
                                (var (caar x)))))))))

  (defthm svex-env-<<=-each-of-cons
    (equal (svex-env-<<=-each (cons pair x) y)
           (and (or (not (consp pair))
                    (not (svar-p (car pair)))
                    (4vec-<<= (cdr pair) (svex-env-lookup (car pair) y)))
                (svex-env-<<=-each x y))))

  (defthm svex-env-<<=-each-of-nil
    (equal (svex-env-<<=-each nil y) t))

  (local (defthm svarlist-filter-of-alist-keys
           (equal (svarlist-filter (alist-keys x))
                  (alist-keys (svex-env-fix x)))
           :hints(("Goal" :in-theory (enable svarlist-filter alist-keys svex-env-fix)))))
  
  (defthmd svex-env-<<=-is-svex-env-<<=-each-when-no-duplicate-keys
    (implies (and (equal keys (alist-keys x))
                  (syntaxp (quotep keys))
                  (not (acl2::hons-dups-p (svarlist-filter keys))))
             (equal (svex-env-<<= x y)
                    (svex-env-<<=-each x y)))
    :hints(("Goal" :in-theory (disable acl2::hons-dups-p
                                       svex-env-<<=-and-no-duplicate-keys-implies-svex-env-<<=-each)
            :use (svex-env-<<=-and-no-duplicate-keys-implies-svex-env-<<=-each)
            :do-not-induct t)))

  (local (in-theory (enable svex-env-fix))))
        
             
(define svex-env-keys-no-1s-p-badguy ((keys svarlist-p)
                                      (env svex-env-p))
  :returns (key svar-p)
  (if (atom keys)
      (make-svar)
    (if (4vec-no-1s-p (svex-env-lookup (car keys) env))
        (svex-env-keys-no-1s-p-badguy (cdr keys) env)
      (svar-fix (car keys))))
  ///
  (defthmd svex-env-keys-no-1s-p-by-badguy
    (equal (svex-env-keys-no-1s-p keys env)
           (let* ((key (svex-env-keys-no-1s-p-badguy keys env)))
             (implies (member-equal key (svarlist-fix keys))
                      (4vec-no-1s-p (svex-env-lookup key env)))))
    :hints(("Goal" :in-theory (enable svex-env-keys-no-1s-p)))
    :rule-classes ((:definition :install-body nil))))
    

#!sv
(encapsulate nil
  (local (defthm svex-env-lookup-of-cons-pair
           (equal (svex-env-lookup key (cons pair rest))
                  (if (and (consp pair)
                           (equal (svar-fix key) (car pair)))
                      (4vec-fix (cdr pair))
                    (svex-env-lookup key rest)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  
  ;; (defthmd svex-env-<<=-of-cons-first
  ;;   (equal (svex-env-<<= (cons pair env1) env2)
  ;;          (if (and (consp pair)
  ;;                   (svar-p (car pair)))
  ;;              (and (4vec-<<= (cdr pair) (svex-env-lookup (car pair) env2))
  ;;                   (svex-env-<<= (svex-env-removekeys (list (car pair)) env1) env2))
  ;;            (svex-env-<<= env1 env2)))
  ;;   :hints (("goal" :cases ((svex-env-<<= (cons pair env1) env2)))
  ;;           (and stable-under-simplificationp
  ;;                (b* ((lit (assoc 'svex-env-<<= clause))
  ;;                     (other-env1 (if (equal (cadr lit) '(cons pair env1))
  ;;                                     '(if (and (consp pair)
  ;;                                               (svar-p (car pair)))
  ;;                                          (svex-env-removekeys (list (car pair)) env1)
  ;;                                        env1)
  ;;                                   '(cons pair env1)))
  ;;                     (witness (cons 'svex-env-<<=-witness (cdr lit))))
  ;;                  (if lit
  ;;                      `(:expand (,lit)
  ;;                        :use ((:instance svex-env-<<=-necc
  ;;                               (x ,other-env1)
  ;;                               (y env2)
  ;;                               (var ,witness)))
  ;;                        :in-theory (e/d (svex-env-lookup-of-cons-pair)
  ;;                                        (svex-env-<<=-necc)))
  ;;                    '(:use ((:instance svex-env-<<=-necc
  ;;                             (x (cons pair env1)) (y env2)
  ;;                             (var (car pair))))
                       
  ;;                      :in-theory (e/d (svex-env-lookup-of-cons-pair)
  ;;                                      (svex-env-<<=-necc))))))))


  (defthmd svex-env-keys-no-1s-p-of-variable-free-term
    (implies (and (syntaxp (and (not (quotep keys))
                                (cmr::term-variable-free-p keys)))
                  (equal env-keys (alist-keys env))
                  (syntaxp (quotep env-keys))
                  (equal new-keys (acl2::hons-intersection env-keys (svarlist-fix keys)))
                  (syntaxp (quotep new-keys)))
             (equal (svex-env-keys-no-1s-p keys env)
                    (svex-env-keys-no-1s-p new-keys env)))
    :hints (("goal" :cases ((svex-env-keys-no-1s-p keys env)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'svex-env-keys-no-1s-p clause))
                      (other (if (eq (cadr lit) 'keys)
                                 '(intersection-equal (alist-keys env) (svarlist-fix keys))
                               'keys)))
                   (and lit
                        `(:expand ((:with svex-env-keys-no-1s-p-by-badguy ,lit))
                          :use ((:instance 4vec-no-1s-p-lookup-when-svex-env-keys-no-1s-p
                                 (keys ,other)
                                 (env env)
                                 (var (svex-env-keys-no-1s-p-badguy . ,(cdr lit)))))
                          :in-theory (e/d (svex-env-lookup)
                                          (4vec-no-1s-p-lookup-when-svex-env-keys-no-1s-p))))))))

  (defthm svex-env-keys-no-1s-p-of-nil
    (svex-env-keys-no-1s-p nil x)
    :hints(("Goal" :in-theory (enable svex-env-keys-no-1s-p))))

  (defthmd svex-env-keys-no-1s-p-of-cons
    (equal (svex-env-keys-no-1s-p (cons var rest) x)
           (and (4vec-no-1s-p (svex-env-lookup var x))
                (svex-env-keys-no-1s-p rest x)))
    :hints(("Goal" :in-theory (enable svex-env-keys-no-1s-p))))

  (defthmd svex-env-extract-of-variable-free-term
    (implies (and (syntaxp (and (not (quotep keys))
                                (cmr::term-variable-free-p keys)))
                  (equal env-keys (alist-keys env))
                  (syntaxp (quotep env-keys))
                  (equal new-keys (acl2::hons-intersection env-keys (svarlist-fix keys)))
                  (syntaxp (quotep new-keys)))
             (svex-envs-similar (svex-env-extract keys env)
                                (svex-env-extract new-keys env)))
    :hints (("goal" :in-theory (enable svex-envs-similar))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-lookup
                                      acl2::alist-keys-member-hons-assoc-equal)))))


  (local (defthm member-of-svarlist-filter
           (implies (svar-p v)
                    (iff (member-equal v (svarlist-filter x))
                         (member-equal v x)))
           :hints(("Goal" :in-theory (enable svarlist-filter)))))
  
  (defthmd svex-env-removekeys-of-variable-free-term
    (implies (and (syntaxp (and (not (quotep keys))
                                (cmr::term-variable-free-p keys)))
                  (equal env-keys (svarlist-filter (alist-keys env)))
                  (syntaxp (quotep env-keys))
                  (equal new-keys (acl2::hons-set-diff env-keys (svarlist-fix keys)))
                  (syntaxp (quotep new-keys)))
             (svex-envs-similar (svex-env-removekeys keys env)
                                (svex-env-extract new-keys env)))
    :hints(("Goal" :in-theory (enable svex-envs-similar))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-lookup
                                     acl2::alist-keys-member-hons-assoc-equal)))))

  (defthmd svex-env-extract-of-cons
    (equal (svex-env-extract (cons key keys) env)
           (cons (cons (svar-fix key) (svex-env-lookup key env))
                 (svex-env-extract keys env)))
    :hints(("Goal" :in-theory (enable svex-env-extract))))

  (defthm svex-env-extract-of-nil
    (equal (svex-env-extract nil env) nil)
    :hints(("Goal" :in-theory (enable svex-env-extract))))
  
  (defthm svex-env-extract-nil-under-svex-envs-similar
    (svex-envs-similar (svex-env-extract keys nil) nil)
    :hints(("Goal" :in-theory (enable svex-envs-similar))))

  (defthm svex-envs-agree-of-nil
    (equal (svex-envs-agree nil env1 env2) t)
    :hints(("Goal" :in-theory (enable svex-envs-agree)))))








;; <p>Suppose we prove:</p>
;; @({
;;  (implies (and (input-signal-hyps inputs)
;;                (override-signal-hyps override-vals))
;;           (output-signal-props (svtv-run (my-svtv) (append override-tests override-vals inputs))
;;                                inputs override-vals))
;;  })

;; <p>where inputs, override-vals, and override-tests are some particular alists.
;; For ease of presentation, suppose the names of the override-value variables are
;; all the same as the corresponding reference variables.  We might then want to
;; conclude:</p>
;; @({
;;  (let ((result (svtv-run (my-svtv) env)))
;;     (implies (and (no-override-tests-set env)
;;                   (input-signal-hyps env)
;;                   (override-signal-hyps result))
;;              (output-signal-props result inputs result)))
;;  })







(define svtv-probealist-sufficient-varlists ((x svtv-probealist-p)
                                             (vars svarlist-list-p))
  :prepwork ((local (defthm true-listp-when-svarlist-p-rw
                      (implies (svarlist-p x)
                               (true-listp x))))
             (local (defthm svarlist-p-nth-of-svarlist-list
                      (implies (svarlist-list-p x)
                               (svarlist-p (nth n x))))))
  (if (atom x)
      t
    (if (mbt (consp (car x)))
        (b* (((svtv-probe x1) (cdar x)))
          (and (member-equal x1.signal (svarlist-fix (nth x1.time vars)))
               (svtv-probealist-sufficient-varlists (cdr x) vars)))
      (svtv-probealist-sufficient-varlists (cdr x) vars)))
  ///
  (defthm add-preserves-sufficient-varlists
    (implies (svtv-probealist-sufficient-varlists x vars)
             (svtv-probealist-sufficient-varlists x (update-nth n (cons v (nth n vars)) vars)))
    :hints(("Goal" :in-theory (disable nth))))
  
  (defthm svtv-probealist-sufficient-of-outvars
    (svtv-probealist-sufficient-varlists x
                                         (svtv-probealist-outvars x))
    :hints(("Goal" :in-theory (enable svtv-probealist-outvars))))

  ;; (local (defthm nth-of-svex-envlist-extract
  ;;          (Equal (nth n (svex-envlist-extract vars envs))
  ;;                 (svex-env-extract (nth n vars)
  ;;                                   (nth n envs)))
  ;;          :hints(("Goal" :in-theory (enable svex-envlist-extract)))))
  
  (defthm svtv-probealist-extract-of-svex-envlist-extract-when-sufficient
    (implies (svtv-probealist-sufficient-varlists x vars)
             (equal (svtv-probealist-extract x (svex-envlist-extract vars envs))
                    (svtv-probealist-extract x envs)))
    :hints(("Goal" :in-theory (enable svtv-probealist-extract))))

  (local (in-theory (enable svtv-probealist-fix)))

  (local (defthm nth-out-of-bounds
           (implies (<= (len x) (nfix n))
                    (equal (nth n x) nil)))))

(defthm svtv-probealist-extract-of-svex-envlist-extract-outvars
  (equal (svtv-probealist-extract probes (svex-envlist-extract (svtv-probealist-outvars probes) envs))
         (svtv-probealist-extract probes envs))
  :hints(("Goal" :in-theory (enable svtv-probealist-outvars svtv-probealist-extract))))


(define svtv-probealist-all-outvars ((x svtv-probealist-p))
  :returns (outvars svarlist-p)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (svtv-probe->signal (cdar x))
              (svtv-probealist-all-outvars (cdr x)))
      (svtv-probealist-all-outvars (cdr x))))
  ///
  (local (defthm svtv-probealist-sufficient-varlists-of-repeat-cons
           (implies (svtv-probealist-sufficient-varlists x (repeat n y))
                    (svtv-probealist-sufficient-varlists x (repeat n (cons z y))))
           :hints(("Goal" :in-theory (enable svtv-probealist-sufficient-varlists)))))

  (defret svtv-probealist-sufficient-varlists-of-<fn>
    (implies (<= (len (svtv-probealist-outvars x)) (nfix n))
             (svtv-probealist-sufficient-varlists x (repeat n outvars)))
    :hints(("Goal" :in-theory (enable svtv-probealist-sufficient-varlists
                                      svtv-probealist-outvars)
            :induct t
            :do-not-induct t)))
  
  (local (defthm svtv-probealist-sufficient-varlists-of-repeat-mergesort
           (iff (svtv-probealist-sufficient-varlists x (repeat n (mergesort y)))
                (svtv-probealist-sufficient-varlists x (repeat n y)))
           :hints(("Goal" :in-theory (enable svtv-probealist-sufficient-varlists)))))

  (defret svtv-probealist-sufficient-varlists-of-<fn>-mergesort
    (implies (<= (len (svtv-probealist-outvars x)) (nfix n))
             (svtv-probealist-sufficient-varlists x (repeat n (mergesort outvars)))))
  (local (in-theory (enable svtv-probealist-fix))))

(defthm svtv-probealist-extract-of-repeat-all-outvars-mergesort
  (implies (<= (len (Svtv-probealist-outvars x)) (nfix n))
           (equal (svtv-probealist-extract x (svex-envlist-extract (repeat n (mergesort (svtv-probealist-all-outvars x))) envs))
                  (svtv-probealist-extract x envs))))


(defthm svex-env-extract-of-svtv-name-lhs-map-eval
  (implies (subsetp-equal (Svarlist-fix vars) (alist-keys (svtv-name-lhs-map-fix namemap)))
           (equal (svex-env-extract vars (svtv-name-lhs-map-eval namemap env))
                  (svtv-name-lhs-map-eval (acl2::fal-extract (svarlist-fix vars)
                                                             (svtv-name-lhs-map-fix namemap))
                                          env)))
  :hints(("Goal" 
          :induct (len vars)
          :in-theory (enable acl2::alist-keys-member-hons-assoc-equal
                             fal-extract)
          :expand ((:free (env) (svex-env-extract vars env))
                   (svarlist-fix vars)
                   (:free (a b c) (acl2::fal-extract (cons a b) c))
                   (:free (a b) (svtv-name-lhs-map-eval (cons a b) env))
                   (svtv-name-lhs-map-eval nil env)))))

(defthm svex-envlist-extract-repeat-of-svtv-name-lhs-map-eval-list
  (implies (subsetp-equal (svarlist-fix vars)
                          (alist-keys (svtv-name-lhs-map-fix namemap)))
           (equal (svex-envlist-extract
                   (repeat (len envs) vars)
                   (svtv-name-lhs-map-eval-list namemap envs))
                  (svtv-name-lhs-map-eval-list
                   (acl2::fal-extract (svarlist-fix vars)
                                      (svtv-name-lhs-map-fix namemap))
                   envs)))
  :hints (("goal"
           :in-theory (enable repeat
                              len
                              svex-envlist-extract
                              svtv-name-lhs-map-eval-list))))


(defthmd svtv-probealist-extract-of-fal-extract-all-outvars
  (implies (and (equal outvars (mergesort (svtv-probealist-all-outvars probes)))
                (svtv-name-lhs-map-p namemap)
                (subsetp-equal outvars
                               (alist-keys namemap))
                (<= (len (svtv-probealist-outvars probes)) (len envs)))
           (equal (svtv-probealist-extract
                   probes
                   (svtv-name-lhs-map-eval-list
                    (acl2::fal-extract outvars namemap) envs))
                  (svtv-probealist-extract probes (svtv-name-lhs-map-eval-list namemap envs))))
  :hints (("goal" :use ((:instance svtv-probealist-extract-of-repeat-all-outvars-mergesort
                         (n (len envs))
                         (x probes)
                         (envs (svtv-name-lhs-map-eval-list namemap envs))))
           :in-theory (disable svtv-probealist-extract-of-repeat-all-outvars-mergesort
                               svtv-probealist-sufficient-varlists-of-svtv-probealist-all-outvars-mergesort)
           :do-not-induct t)))


(encapsulate nil
  (local (defun ind (ins initst fsm other-envs)
           (if (atom ins)
               (list initst other-envs)
             (ind (cdr ins)
                  (base-fsm-step (car ins) initst fsm)
                  fsm
                  (cdr other-envs)))))
  (defthm lhs-eval-zero-of-append-when-vars-subset-of-first-keys
    (implies (subsetp-equal (lhs-vars x)
                            (alist-keys (svex-env-fix env1)))
             (equal (lhs-eval-zero x (append env1 env2))
                    (lhs-eval-zero x env1)))
    :hints(("Goal" :in-theory (enable lhs-eval-zero
                                      lhs-vars
                                      lhrange-eval
                                      lhatom-eval
                                      lhatom-vars
                                      svex-env-boundp))))
  (defthm svtv-name-lhs-map-eval-of-append-envs-when-vars-subset-of-first-keys
    (implies (subsetp-equal (lhslist-vars (alist-vals (svtv-name-lhs-map-fix namemap)))
                            (alist-keys (svex-env-fix env1)))
             (equal (svtv-name-lhs-map-eval namemap (append env1 env2))
                    (svtv-name-lhs-map-eval namemap env1)))
    :hints(("Goal" :in-theory (enable lhslist-vars alist-vals svtv-name-lhs-map-fix svtv-name-lhs-map-eval))))
  
  (defthm svtv-name-lhs-map-eval-of-svex-envlists-append-corresp-base-fsm-eval-when-vars-subset-of-value-keys
    (implies (subsetp-equal (lhslist-vars (alist-vals (svtv-name-lhs-map-fix namemap)))
                            (svex-alist-keys (base-fsm->values fsm)))
             (equal (svtv-name-lhs-map-eval-list
                     namemap
                     (svex-envlists-append-corresp
                      (base-fsm-eval ins initst fsm)
                      other-envs))
                    (svtv-name-lhs-map-eval-list
                     namemap
                     (base-fsm-eval ins initst fsm))))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-list
                                      base-fsm-eval
                                      base-fsm-step-outs
                                      svex-envlists-append-corresp)
            :induct (ind ins initst fsm other-envs))))

  (defthm svtv-probealist-extract-of-svtv-name-lhs-map-eval-of-svex-envlists-append-corresp-base-fsm-eval-when-vars-subset-of-value-keys
    (implies (and (subsetp-equal (lhslist-vars (alist-vals
                                                (acl2::fal-extract
                                                 (mergesort (svtv-probealist-all-outvars probes))
                                                 (svtv-name-lhs-map-fix namemap))))
                                 (svex-alist-keys (base-fsm->values fsm)))
                  (subsetp-equal (mergesort (svtv-probealist-all-outvars probes))
                                 (alist-keys (svtv-name-lhs-map-fix namemap)))
                  (<= (len (svtv-probealist-outvars probes)) (len ins)))
             (equal (svtv-probealist-extract
                     probes
                     (svtv-name-lhs-map-eval-list
                      namemap
                      (svex-envlists-append-corresp
                       (base-fsm-eval ins initst fsm)
                       other-envs)))
                    (svtv-probealist-extract
                     probes
                     (svtv-name-lhs-map-eval-list
                      namemap
                      (base-fsm-eval ins initst fsm)))))
    :hints (("goal" :use ((:instance svtv-probealist-extract-of-fal-extract-all-outvars
                           (namemap (svtv-name-lhs-map-fix namemap))
                           (envs (svex-envlists-append-corresp
                                  (base-fsm-eval ins initst fsm)
                                  other-envs))
                           (outvars (mergesort (svtv-probealist-all-outvars probes))))
                          (:instance svtv-probealist-extract-of-fal-extract-all-outvars
                           (namemap (svtv-name-lhs-map-fix namemap))
                           (envs (base-fsm-eval ins initst fsm))
                           (outvars (mergesort (svtv-probealist-all-outvars probes)))))
             :in-theory (disable svtv-probealist-extract-of-fal-extract-all-outvars)
             :do-not-induct t))))
                   




(defcong svex-envs-similar equal (svex-envs-agree vars x y) 2
  :hints(("Goal" :in-theory (enable svex-envs-agree))))

(defcong svex-envs-similar equal (svex-envs-agree vars x y) 3
  :hints(("Goal" :in-theory (enable svex-envs-agree))))


(defthm base-fsm-final-state-of-svtv-fsm->renamed-fsm
  (equal (base-fsm-final-state ins initst (svtv-fsm->renamed-fsm fsm))
         (base-fsm-final-state ins initst (svtv-fsm->base-fsm fsm)))
  :hints(("Goal" :in-theory (enable base-fsm-final-state
                                    svtv-fsm->renamed-fsm
                                    base-fsm-step
                                    base-fsm-step-env))))

(defthm base-fsm-step-outs-of-svtv-fsm->renamed-fsm
  (equal (base-fsm-step-outs in prev-st (svtv-fsm->renamed-fsm fsm))
         (svtv-name-lhs-map-eval
          (svtv-fsm->namemap fsm)
          (append (base-fsm-step-outs in prev-st (svtv-fsm->base-fsm fsm))
                  (base-fsm-step-env in prev-st (svtv-fsm->base-fsm fsm)))))
  :hints(("Goal" :in-theory (enable base-fsm-step-outs
                                    svtv-fsm->renamed-fsm
                                    base-fsm-step-env))))





(defthmd base-fsm->nextstate-of-svtv-fsm->renamed-fsm
  (equal (base-fsm->nextstate (svtv-fsm->renamed-fsm svtv-fsm))
         (base-fsm->nextstate (svtv-fsm->base-fsm svtv-fsm)))
  :hints(("Goal" :in-theory (enable svtv-fsm->renamed-fsm))))

(define base-fsm-eval-envs ((ins svex-envlist-p)
                            (prev-st svex-env-p)
                            (x base-fsm-p))
  :guard (and (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x))))
              (equal (alist-keys prev-st)
                     (svex-alist-keys (base-fsm->nextstate x))))
  (b* (((when (Atom ins)) nil))
    (cons (base-fsm-step-env (car ins) prev-st x)
          (base-fsm-eval-envs (cdr ins)
                              (base-fsm-step (car ins) prev-st x)
                              x)))
  ///
  (defthmd base-fsm-eval-of-svtv-fsm->renamed-fsm
    (equal (base-fsm-eval ins prev-st (svtv-fsm->renamed-fsm x))
           (svtv-name-lhs-map-eval-list
            (svtv-fsm->namemap x)
            (svex-envlists-append-corresp
             (base-fsm-eval ins prev-st (svtv-fsm->base-fsm x))
             (base-fsm-eval-envs ins prev-st (svtv-fsm->base-fsm x)))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      base-fsm-step
                                      base-fsm-step-env
                                      svex-envlists-append-corresp
                                      svtv-name-lhs-map-eval-list
                                      base-fsm->nextstate-of-svtv-fsm->renamed-fsm)
            :induct (base-fsm-eval ins prev-st (svtv-fsm->base-fsm x))
            :expand ((:free (x) (base-fsm-eval ins prev-st x))
                     (base-fsm-eval-envs ins prev-st (svtv-fsm->base-fsm x)))))))



(define svar-override-triplelistlist->all-refvars ((x svar-override-triplelistlist-p))
  :returns (refvars svarlist-p)
  (if (atom x)
      nil
    (append (svar-override-triplelist->refvars (car x))
            (svar-override-triplelistlist->all-refvars (cdr x)))))

(define svar-override-triplelistlist-refvars-bound-in-envs ((x svar-override-triplelistlist-p)
                                                            (envs svex-envlist-p))
  :prepwork ((local (defthm hons-subset1-is-subsetp-alist-kes
                      (iff (acl2::hons-subset1 x y)
                           (subsetp-equal x (alist-keys y)))
                      :hints(("Goal" :in-theory (enable hons-assoc-equal-member-alist-keys))))))
  :measure (len envs)
  (if (atom envs)
      t
    (and (mbe :logic (subsetp-equal (svar-override-triplelist->refvars (car x))
                                    (alist-keys (svex-env-fix (car envs))))
              :exec (acl2::hons-subset1 (svar-override-triplelist->refvars (car x))
                                        (car envs)))
         (svar-override-triplelistlist-refvars-bound-in-envs (cdr x) (cdr envs))))

  ///

  (local (defun refvars-bound-of-base-fsm-eval-ind (x ins prev-st fsm)
           (if (atom ins)
               (list x prev-st fsm)
             (refvars-bound-of-base-fsm-eval-ind (cdr x) (cdr ins)
                                                 (base-fsm-step (car ins) prev-st fsm)
                                                 fsm))))
  
  (defthm svar-override-triplelistlist-refvars-bound-in-envs-of-base-fsm-eval
    (implies (<= (len x) (len ins))
             (equal (svar-override-triplelistlist-refvars-bound-in-envs x (base-fsm-eval ins prev-st fsm))
                    (subsetp-equal (svar-override-triplelistlist->all-refvars x)
                                   (svex-alist-keys (base-fsm->values fsm)))))
    :hints(("Goal" :in-theory (enable svar-override-triplelistlist->all-refvars
                                      base-fsm-eval
                                      base-fsm-step-outs)
            :induct (refvars-bound-of-base-fsm-eval-ind x ins prev-st fsm)))))

(defthm svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval-of-append-corresp
  (implies (svar-override-triplelistlist-refvars-bound-in-envs triples (nthcdr cycle ref-envs1))
           (equal (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                   cycle triples envs (svex-envlists-append-corresp ref-envs1 ref-envs2))
                  (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                   cycle triples envs ref-envs1)))
  :hints(("Goal" :in-theory (enable svar-override-triplelistlist-refvars-bound-in-envs
                                    svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                                    svex-envlists-append-corresp
                                    acl2::and* nthcdr)
          :expand ((svar-override-triplelistlist-refvars-bound-in-envs triples (nthcdr cycle ref-envs1))
                   (:free (env ref-env) (SVAR-OVERRIDE-TRIPLELIST-ENV-OK NIL env ref-env)))
          :induct (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                   cycle triples envs ref-envs1))))
           



(local (defthmd alist-keys-member-hons-assoc-equal
         (iff (member-equal v (alist-keys x))
              (hons-assoc-equal v x))
         :hints(("Goal" :in-theory (enable hons-assoc-equal-member-alist-keys)))))

(defthm svex-envs-agree-of-append-when-no-intersect
  (implies (not (intersectp-equal (svarlist-fix vars) (alist-keys (svex-env-fix b))))
           (equal (svex-envs-agree vars a (append b c))
                  (svex-envs-agree vars a c)))
  :hints(("Goal" :in-theory (e/d (svex-envs-agree
                                  svex-env-boundp
                                  intersectp-equal
                                  alist-keys-member-hons-assoc-equal)
                                 (hons-assoc-equal-member-alist-keys))
          :induct t
          :expand ((svarlist-fix vars)))))

(defthm svex-envs-agree-of-append-when-subset
  (implies (subsetp-equal (svarlist-fix vars) (alist-keys (svex-env-fix b)))
           (equal (svex-envs-agree vars a (append b c))
                  (svex-envs-agree vars a b)))
  :hints(("Goal" :in-theory (e/d (svex-envs-agree
                                  svex-env-boundp
                                  intersectp-equal
                                  alist-keys-member-hons-assoc-equal)
                                 (hons-assoc-equal-member-alist-keys))
          :induct t
          :expand ((svarlist-fix vars)))))


(defthm alist-keys-of-svtv-probealist-extract
  (equal (alist-keys (svtv-probealist-extract probes vals))
         (alist-keys (svtv-probealist-fix probes)))
  :hints(("Goal" :in-theory (enable svtv-probealist-fix
                                    svtv-probealist-extract
                                    alist-keys))))


(defthm-svex-eval-flag
  (defthm svex-eval-of-append-first-non-intersecting
    (implies (not (intersectp-equal (svex-vars x) (alist-keys (svex-env-fix a))))
             (equal (svex-eval x (append a b))
                    (svex-eval x b)))
    :hints ('(:expand ((:free (env) (svex-eval x env))
                       (svex-vars x)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-boundp))))
    :flag expr)
  (defthm svexlist-eval-of-append-first-non-intersecting
    (implies (not (intersectp-equal (svexlist-vars x) (alist-keys (svex-env-fix a))))
             (equal (svexlist-eval x (append a b))
                    (svexlist-eval x b)))
    :hints ('(:expand ((:free (env) (svexlist-eval x env))
                       (svexlist-vars x))))
    :flag list))

(defthm svex-alist-eval-of-append-first-non-intersecting
  (implies (not (intersectp-equal (svex-alist-vars x) (alist-keys (svex-env-fix a))))
           (equal (svex-alist-eval x (append a b))
                  (svex-alist-eval x b)))
  :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars))))

(defthm-svex-eval-flag
  (defthm svex-eval-of-append-superset
    (implies (subsetp-equal (svex-vars x) (alist-keys (svex-env-fix a)))
             (equal (svex-eval x (append a b))
                    (svex-eval x a)))
    :hints ('(:expand ((:free (env) (svex-eval x env))
                       (svex-vars x)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-boundp))))
    :flag expr)
  (defthm svexlist-eval-of-append-superset
    (implies (subsetp-equal (svexlist-vars x) (alist-keys (svex-env-fix a)))
             (equal (svexlist-eval x (append a b))
                    (svexlist-eval x a)))
    :hints ('(:expand ((:free (env) (svexlist-eval x env))
                       (svexlist-vars x))))
    :flag list))


(defthm svex-alist-eval-of-append-superset
  (implies (subsetp-equal (svex-alist-vars x) (alist-keys (svex-env-fix a)))
           (equal (svex-alist-eval x (append a b))
                  (svex-alist-eval x a)))
  :hints(("Goal" :in-theory (enable svex-alist-eval
                                    svex-alist-vars))))


#!sv
(defthm take-of-svex-alistlist-eval
  (equal (take n (svex-alistlist-eval x env))
         (svex-alistlist-eval (take n x) env))
  :hints(("Goal" :in-theory (e/d (svex-alistlist-eval
                                    take
                                    svex-alist-eval)
                                 (acl2::take-of-too-many
                                  acl2::take-when-atom)))))



































;;; -----------------------------------------------------
;;; All the rest of this is maybe unnecessary


















;; Svex-override-triplelist-fsm-inputs-ok* will be true if, for the set portion
;; of each override test variable, the corresponding override value variable is
;; set to the signal's current value.

(local (defthm cdr-hons-assoc-when-svex-alist-p
         (implies (svex-alist-p x)
                  (iff (cdr (hons-assoc-equal k x))
                       (hons-assoc-equal k x)))))
(local (defthm hons-subset1-of-svex-alist
         (implies (and (svex-alist-p y)
                       (svarlist-p x))
                  (equal (acl2::hons-subset1 x y)
                         (subsetp-equal x (svex-alist-keys y))))
         :hints(("Goal" :in-theory (enable acl2::hons-subset1
                                           subsetp-equal
                                           svex-lookup)))))

(local (defthmd member-alist-keys
         (iff (member-equal v (alist-keys x))
              (hons-assoc-equal v x))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(local (defthmd hons-subset1-is-alist-keys
         (equal (acl2::hons-subset1 x y)
                (subsetp-equal x (alist-keys y)))
         :hints(("Goal" :in-theory (enable acl2::hons-subset1
                                           subsetp-equal
                                           member-alist-keys
                                           alist-keys)))))


(define svex-override-triples-from-signal-names ((x svarlist-p)
                                                 (values svex-alist-p)) ;; values of the FSM
  :returns (triples svex-override-triplelist-p)
  :guard (mbe :logic (subsetp-equal x (svex-alist-keys values))
              :exec (acl2::hons-subset1 x values))
  :prepwork ()
  (if (atom x)
      nil
    (cons (make-svex-override-triple :testvar (change-svar (car x) :override-test t)
                                     :valvar (change-svar (car x) :override-val t)
                                     :valexpr (svex-fastlookup (car x) values))
          (svex-override-triples-from-signal-names (cdr x) values))))



(define svex-override-triplelists-from-signal-names ((x svarlist-list-p)
                                                     (values svex-alist-p)) ;; values of the FSM
  :returns (triples svex-override-triplelistlist-p)
  :guard (mbe :logic (subsetp-equal (append-svarlists x) (svex-alist-keys values))
              :exec (acl2::hons-subset1 (append-svarlists x) values))
  :guard-hints (("goal" :in-theory (enable append-svarlists)))
  (if (atom x)
      nil
    (cons (svex-override-triples-from-signal-names (car x) values)
          (svex-override-triplelists-from-signal-names (cdr x) values))))






;; One way of creating an env with correct overrides -- append this to the original env.
(define svex-alist-collect-override-env ((test-env svex-env-p) ;; Maps variables to their override test values
                                         (eval-result-env svex-env-p))
  ;; :guard  (mbe :logic (subsetp-equal (alist-keys test-env) (alist-keys eval-result-env))
  ;;              :exec (acl2::hons-subset1 (alist-keys test-env) eval-result-env))
  ;; :guard-hints (("goal" :in-theory (enable alist-keys hons-subset1-is-alist-keys)))
  :returns (override-env svex-env-p)
  (if (atom test-env)
      nil
    (if (mbt (and (consp (car test-env))
                  (svar-p (caar test-env))))
        (b* (((cons var testval) (car test-env))
             (testval (4vec-fix testval)))
          (cons (cons (change-svar var :override-test t) testval)
                (cons (cons (change-svar var :override-val t)
                            ;; could be 4vec-bit?! masked with the testval
                            (svex-env-lookup var eval-result-env))
                      (svex-alist-collect-override-env (cdr test-env) eval-result-env))))
      (svex-alist-collect-override-env (cdr test-env) eval-result-env)))
  ///
  (defret lookup-override-test-in-<fn>
    (implies (and (svarlist-non-override-p (alist-keys (svex-env-fix test-env)))
                  (svar->override-test var))
             (and (equal (svex-env-boundp var override-env)
                         (svex-env-boundp (change-svar var :override-test nil) test-env))
                  (equal (svex-env-lookup var override-env)
                         (svex-env-lookup (change-svar var :override-test nil) test-env))))
    :hints(("Goal" :in-theory (enable svarlist-non-override-p
                                      svex-env-boundp
                                      svex-env-lookup
                                      svex-env-fix
                                      alist-keys))))
  
  (local (defthm change-svar-when-not-test/val
           (implies (and (not (svar->override-test x))
                         (not (svar->override-val x)))
                    (equal (change-svar x :override-test nil :override-val nil)
                           (svar-fix x)))
           :hints (("goal" :in-theory (enable svar-fix-redef)))))
  
  (defret lookup-override-val-in-<fn>
    (implies (and (svarlist-non-override-p (alist-keys (svex-env-fix test-env)))
                  (svar->override-val var)
                  (not (svar->override-test var)))
             (and (equal (svex-env-boundp var override-env)
                         (svex-env-boundp (change-svar var :override-val nil) test-env))
                  (equal (svex-env-lookup var override-env)
                         (if (svex-env-boundp (change-svar var :override-val nil) test-env)
                             (svex-env-lookup (change-svar var :override-val nil) eval-result-env)
                           (4vec-x)))))
    :hints(("Goal" :in-theory (enable svarlist-non-override-p
                                      svex-env-boundp
                                      svex-env-lookup
                                      svex-env-fix
                                      alist-keys))))
  
  (local (defthm svex-override->test-and-val-when-member
           (implies (and (svarlist-non-override-p x)
                         (member-equal (svar-fix v) (svarlist-fix x)))
                    (and (not (svar->override-test v))
                         (not (svar->override-val v))))
           :hints(("Goal" :in-theory (enable svarlist-non-override-p)))))

  
  
  (defret svex-override-triplelist-env-ok-of-<fn>
    :pre-bind ((eval-result-env (svex-alist-eval values eval-env)))
    (implies (and (subsetp-equal (alist-keys (svex-env-fix test-env)) (svex-alist-keys values))
                  (subsetp-equal (svarlist-fix signals) (alist-keys (svex-env-fix test-env)))
                  ;; (no-duplicatesp-equal (alist-keys (svex-env-fix test-env)))
                  (svarlist-non-override-p (alist-keys (svex-env-fix test-env))))
             (svex-override-triplelist-env-ok (svex-override-triples-from-signal-names signals values)
                                              (append override-env any-env)
                                              eval-env))
    :hints(("Goal" :in-theory (e/d (svex-override-triples-from-signal-names
                                      svex-override-triplelist-env-ok
                                      subsetp-equal
                                      svarlist-fix
                                      svarlist-non-override-p)
                                   (<fn>))
            :induct (svex-override-triples-from-signal-names signals values))))


  (defret svex-env-removekeys-of-<fn>
    (equal (svex-env-removekeys (svex-override-triplelist-vars
                                 (svex-override-triples-from-signal-names
                                  (alist-keys (svex-env-fix test-env))
                                  any-values))
                                override-env)
           nil)
    :hints(("Goal" :in-theory (enable svex-env-removekeys
                                      svex-env-fix
                                      alist-keys
                                      svex-override-triplelist-vars
                                      svex-override-triples-from-signal-names))))
  
  (local (in-theory (enable svex-env-fix))))


(define append-corresp-svex-envs ((envs1 svex-envlist-p)
                                  (envs2 svex-envlist-p))
  :returns (appended svex-envlist-p)
  :measure (+ (len envs1) (len envs2))
  (if (and (atom envs1) (atom envs2))
      nil
    (cons (append (svex-env-fix (car envs1))
                  (svex-env-fix (car envs2)))
          (append-corresp-svex-envs (cdr envs1) (cdr envs2)))))


(define svex-envlist-all-keys ((x svex-envlist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (alist-keys (svex-env-fix (car x)))
            (svex-envlist-all-keys (cdr x)))))

(define svex-envlist-keys-list ((x svex-envlist-p))
  :returns (vars svarlist-list-p)
  (if (atom x)
      nil
    (cons (alist-keys (svex-env-fix (car x)))
          (svex-envlist-keys-list (cdr x)))))

;; Similarly, one way of creating an envlist with correct overrides for base-fsm-eval -- append these to the original input envs.

(define base-fsm-collect-override-envs ((test-envs svex-envlist-p) ;; maps variables for each cycle to their override tests
                                        (eval-ins svex-envlist-p)
                                        (prev-st svex-env-p)
                                        (fsm base-fsm-p))
  :guard  (and (mbe :logic (subsetp-equal (svex-envlist-all-keys test-envs) (svex-alist-keys (base-fsm->values fsm)))
                    :exec (acl2::hons-subset1 (svex-envlist-all-keys test-envs) (base-fsm->values fsm)))
               (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate fsm)))
               (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate fsm)))))
  :guard-hints (("goal" :in-theory (enable svex-envlist-all-keys)))
  :returns (override-envs svex-envlist-p)
  (if (atom eval-ins)
      nil
    (cons (svex-alist-collect-override-env
           (car test-envs)
           (base-fsm-step-outs (car eval-ins) prev-st fsm))
          (base-fsm-collect-override-envs
           (cdr test-envs)
           (cdr eval-ins)
           (base-fsm-step (car eval-ins) prev-st fsm)
           fsm)))
  ///

  (local (defun base-fsm-collect-override-envs-env-ind (test-envs eval-ins prev-st fsm other-ins)
           (if (Atom eval-ins)
               (list test-envs  prev-st other-ins)
             (base-fsm-collect-override-envs-env-ind
              (cdr test-envs)
              (cdr eval-ins)
              (base-fsm-step (car eval-ins) prev-st fsm)
              fsm
              (cdr other-ins)))))

  (local (defthm svex-env-lookup-of-cons2
           (equal (svex-env-lookup v (cons x y))
                  (if (and (consp x)
                           (svar-p (car x))
                           (equal (car x) (svar-fix v)))
                      (4vec-fix (cdr x))
                    (svex-env-lookup v y)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
  
  (local (defcong svex-envs-similar svex-envs-similar (cons x y) 2
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))

  (local (defthm svex-envs-similar-append-cons
           (implies (not (svex-env-boundp (car y) x))
                    (svex-envs-similar (append x (cons y z))
                                       (cons y (append x z))))
           :hints(("Goal" :in-theory (enable svex-envs-similar)))))

  (local (defthm svex-env-boundp-when-keys-non-override-p
           (implies (and (svarlist-non-override-p (alist-keys (svex-env-fix env)))
                         (or (svar->override-test x)
                             (svar->override-val x)))
                    (not (svex-env-boundp x env)))
           :hints(("Goal" :in-theory (enable svex-env-fix svex-env-boundp svarlist-non-override-p alist-keys)))))
           
  
  (local (defthm base-fsm-step-env-of-append-override-env
           (implies (svarlist-non-override-p (svex-alist-keys (base-fsm->nextstate fsm)))
                    (svex-envs-similar
                     (base-fsm-step-env
                      (append (svex-alist-collect-override-env test-env res-env)
                              env2)
                      prev-st fsm)
                     (append (svex-alist-collect-override-env test-env res-env)
                             (base-fsm-step-env env2 prev-st fsm))))
           :hints(("Goal" :in-theory (enable base-fsm-step-env
                                             svex-alist-collect-override-env)
                   :induct (svex-alist-collect-override-env test-env res-env)))))


  (local (defthm len-equal-0
           (equal (equal (len x) 0)
                  (atom x))))
  
  (defret svex-override-triplelist-fsm-inputs-ok*-of-<fn>
    (implies (and (subsetp-equal (svex-envlist-all-keys test-envs) (svex-alist-keys (base-fsm->values fsm)))
                  (svarlist-non-override-p (svex-envlist-all-keys test-envs))
                  (svarlist-non-override-p (svex-alist-keys (base-fsm->nextstate fsm)))
                  (equal (len any-envs) (len eval-ins)))
             (svex-override-triplelist-fsm-inputs-ok*
              (svex-override-triplelists-from-signal-names 
               (svex-envlist-keys-list test-envs)
               (base-fsm->values fsm))
              (append-corresp-svex-envs override-envs any-envs)
              eval-ins prev-st fsm))
    :hints(("Goal" :in-theory (enable svex-envlist-all-keys
                                      svex-envlist-keys-list
                                      svex-override-triplelist-fsm-inputs-ok*
                                      svex-override-triplelists-from-signal-names
                                      append-corresp-svex-envs
                                      base-fsm-step-outs)
            :induct (base-fsm-collect-override-envs-env-ind test-envs eval-ins prev-st fsm any-envs))))

  (defcong svex-envs-similar equal (base-fsm-collect-override-envs
                                    test-envs eval-ins prev-st fsm)
    3
    :hints(("Goal" :in-theory (enable base-fsm-step-outs
                                      base-fsm-step
                                      base-fsm-step-env)))))


;; (local
;;  (defsection nth-of-base-fsm-eval
;;    (local (defun nth-of-base-fsm-eval-ind (n ins st fsm)
;;             (if (zp n)
;;                 (list ins st fsm)
;;               (nth-of-base-fsm-eval-ind (1- n) (cdr ins)
;;                                         (base-fsm-step (car ins) st fsm)
;;                                         fsm))))

;;    (defthmd nth-of-base-fsm-eval
;;      (equal (nth n (base-fsm-eval eval-ins prev-st fsm))
;;             (base-fsm-step-outs (nth n eval-ins)
;;                                 (nth n (cons prev-st (base-fsm-eval-states eval-ins prev-st fsm)))
;;                                 fsm))
;;      :hints(("Goal" :in-theory (enable base-fsm-eval base-fsm-eval-states)
;;              :induct (nth-of-base-fsm-eval n eval-ins prev-st fsm))))))

(define base-fsm-collect-override-envs-alt ((cycle natp)
                                            (test-envs svex-envlist-p) ;; the rest of them starting with cycle
                                            (fsm-eval svex-envlist-p)
                                            ;; (eval-ins svex-envlist-p) ;; full, starting with cycle=0
                                            ;; (prev-st svex-env-p)    ;; starting with cycle=0
                                            ;; (fsm base-fsm-p)
                                            )
  :guard  (and (mbe :logic (subsetp-equal (svex-envlist-all-keys test-envs) (alist-keys fsm-eval))
                    :exec (acl2::hons-subset1 (svex-envlist-all-keys test-envs) fsm-eval))
               (<= cycle (len fsm-eval)))
  :guard-hints(("Goal" :in-theory (enable nth-of-base-fsm-eval
                                          hons-subset1-is-alist-keys
                                          svex-envlist-all-keys)))
  :measure (nfix (- (len fsm-eval) (nfix cycle)))
  :returns (override-envs svex-envlist-p)
  (if (zp (- (len fsm-eval) (nfix cycle)))
      nil
    (cons (svex-alist-collect-override-env
           (car test-envs)
           (nth cycle fsm-eval))
          (base-fsm-collect-override-envs-alt
           (+ 1 (lnfix cycle))
           (cdr test-envs)
           fsm-eval)))

  :prepwork ((defthm svex-env-p-nth-of-svex-envlist
               (implies (svex-envlist-p x)
                        (svex-env-p (nth n x)))))
  ///

  
  (defret base-fsm-collect-override-envs-alt-redef
    :pre-bind ((fsm-eval (base-fsm-eval eval-ins prev-st fsm)))
    (equal override-envs
           (base-fsm-collect-override-envs test-envs (nthcdr cycle eval-ins)
                                           (base-fsm-final-state (take cycle eval-ins) prev-st fsm)
                                           fsm))
    :hints(("Goal" :in-theory (e/d (nth-of-base-fsm-eval)
                                   (take))
            :induct (base-fsm-collect-override-envs-alt cycle test-envs eval-ins) ;; bit of a hack but it works
            :expand ((:free (eval-ins prev-st) (base-fsm-collect-override-envs test-envs eval-ins prev-st fsm))
                     (:free (fsm-eval) <call>))))))






;; For a given pipeline 
