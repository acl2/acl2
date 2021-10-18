; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")

(include-book "svtv-stobj-pipeline-thm")
(include-book "centaur/meta/variable-free" :dir :system)
(include-book "../svex/override")
(include-book "process")
(include-book "misc/hons-help" :dir :system)
(local (std::add-default-post-define-hook :fix))

(defthm svex-lookup-when-variable-free
  (implies (syntaxp (and (cmr::term-variable-free-p key)
                         (cmr::term-variable-free-p alist)))
           (iff (svex-lookup key alist)
                (svex-fastlookup key (hide (make-fast-alist alist)))))
  :hints (("goal" :expand ((hide (make-fast-alist alist))))))

(cmr::def-force-execute svtv-fsm-run-input-substs-execute-term-when-variable-free
  svtv-fsm-run-input-substs)

(cmr::def-force-execute svex-fastlookup-execute-term-when-variable-free
  svex-fastlookup)

(cmr::def-force-execute svex-alist-keys-execute-term-when-variable-free
  svex-alist-keys)

(cmr::def-force-execute svex-override-triplelist-vars-execute-term-when-variable-free
  svex-override-triplelist-vars)

(cmr::def-force-execute svexlist-check-overridetriples-execute-term-when-variable-free
  (svexlist-check-overridetriples
   svex-check-overridetriples))



(define svex-env-override-test-vars ((x svex-env-p))
  :returns (test-vars svarlist-p)
  (b* (((when (atom x)) nil)
       ((unless (and (mbt (and (consp (car x))
                               (svar-p (caar x))))
                     (svar->override-test (caar x))))
        (svex-env-override-test-vars (cdr x))))
    (cons (caar x)
          (svex-env-override-test-vars (cdr x))))
  ///
  (defthm svex-env-override-test-vars-of-cons
    (equal (svex-env-override-test-vars (cons a b))
           (let ((rest (svex-env-override-test-vars b)))
             (if (and (consp a)
                      (svar-p (car a))
                      (svar->override-test (car a)))
                 (cons (car a) rest)
               rest))))

  (defthm svex-env-override-test-vars-of-append
    (equal (svex-env-override-test-vars (append a b))
           (append (svex-env-override-test-vars a)
                   (svex-env-override-test-vars b))))

  (local (in-theory (enable svex-env-fix))))

(define collect-known-members-from-list-term ((x pseudo-termp))
  :measure (acl2::pseudo-term-count x)
  (acl2::pseudo-term-case x
    :const x.val
    :var nil
    :call (case x.fn
            (cons
             (and (eql (len x.args) 2)
                  (b* (((list arg1 arg2) x.args)
                       (rest (collect-known-members-from-list-term arg2)))
                    (acl2::pseudo-term-case arg1
                      :const (cons arg1.val rest)
                      :otherwise rest))))
            (binary-append
             (and (eql (len x.args) 2)
                  (b* (((list arg1 arg2) x.args))
                    (append-without-guard
                     (collect-known-members-from-list-term arg1)
                     (collect-known-members-from-list-term arg2)))))
            (otherwise nil))))

(define override-tests-to-svex-override-triplelist ((x svarlist-p) (al svex-alist-p))
  :returns (trips svex-override-triplelist-p)
  (if (atom x)
      nil
    (let ((look (svex-fastlookup (change-svar (car x) :override-test nil) al))
          (rest (override-tests-to-svex-override-triplelist (cdr x) al)))
      (if (and look
               (svar->override-test (car x))
               (not (svar->override-val (car x))))
          (cons (make-svex-override-triple
                 :testvar (car x)
                 :valvar (change-svar (car x) :override-test nil :override-val t)
                 :valexpr look)
                rest)
        rest)))
  ///
  (defthm override-tests-to-svex-override-triplelist-of-cons
    (equal (override-tests-to-svex-override-triplelist (cons a b) al)
           (let ((look (svex-lookup (change-svar a :override-test nil) al))
                 (rest (override-tests-to-svex-override-triplelist b al)))
             (if (and look
                      (svar->override-test a)
                      (not (svar->override-val a)))
                 (cons (make-svex-override-triple
                        :testvar a
                        :valvar (change-svar a :override-test nil :override-val t)
                        :valexpr look)
                       rest)
               rest))))

  (defthm override-tests-to-svex-override-triplelist-of-nil
    (equal (override-tests-to-svex-override-triplelist nil al) nil))

  (defret member-of-<fn>
    (iff (member-equal var (svex-override-triplelist-vars trips))
         (and (svar-p var)
              (cond ((svar->override-test var)
                     (and (member-equal var (svarlist-fix x))
                          (not (svar->override-val var))
                          (svex-lookup (change-svar var :override-test nil) al)))
                    ((svar->override-val var)
                     (and (member-equal (change-svar var :override-test t :override-val nil) (svarlist-fix x))
                          (svex-lookup (change-svar var :override-val nil) al)))
                    (t nil))))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars))))
                     
  (local (defthm svar-when-equal-x
           (implies (and (equal test (svar->override-test x))
                         (equal val (svar->override-val x)))
                    (equal (change-svar x :override-test test :override-val val)
                           (svar-fix x)))))

  (defret no-duplicate-vars-of-<FN>
    (implies (no-duplicatesp-equal (svarlist-fix x))
             (no-duplicatesp-equal
              (svex-override-triplelist-vars trips)))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                      svarlist-fix)))))

(define override-tests-to-svex-override-triplelist-exec ((x svarlist-p) (al svex-alist-p))
  :enabled t
  (hons-copy (override-tests-to-svex-override-triplelist x (make-fast-alist al))))
 

(define svarlist-update-override-tests ((val booleanp)
                                        (x svarlist-p))
  (if (atom x)
      nil
    (cons (change-svar (car x) :override-test val)
          (svarlist-update-override-tests val (cdr x)))))

(define svtv-override-parameter-bindings (mfc state)
  (declare (ignore mfc))
  :mode :program
  (and (boundp-global 'remove-override-vars-value-lookup-term state)
       (list (cons 'values (f-get-global 'remove-override-vars-value-lookup-term state))
             (if (boundp-global 'svtv-non-composable-override-vars state)
                 (cons 'non-composable-vars
                       (list 'quote (svarlist-update-override-tests
                                     t (f-get-global 'svtv-non-composable-override-vars state))))
               '(non-composable-vars . 'nil)))))

(defmacro set-svtv-decomp-main-fsm (fsm-name)
  `(make-event
    (pprogn (f-put-global 'remove-override-vars-value-lookup-term
                          '(base-fsm->values$inline (,fsm-name))
                          state)
            (value '(value-triple ',fsm-name)))))

(defmacro set-svtv-non-composable-override-vars (varlist)
  `(make-event
    (pprogn (f-put-global 'svtv-non-composable-override-vars
                          ',varlist
                          state)
            (value '(value-triple 'svtv-non-composable-override-vars)))))

(defun diagnose-overridetriple-check-result (check trips)
  (progn$ (cw "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!~%")
          (cw "SVTV-DECOMP override syntactic check failed.~%")
          (cw "Diagnostic info sneaky-pushed onto :svtv-decomp-overridetriple-errors.~%")
          (acl2::sneaky-push :svtv-decomp-overridetriple-errors (list check trips))))

(local (in-theory (disable SVEX-ENV-REMOVEKEYS-UNDER-SVEX-ENVS-SIMILAR)))

(defthmd svtv-decomp-remove-override-vars-from-svex-alist-eval-when-svexlist-check-overridetriples
  (implies (and (syntaxp (cmr::term-variable-free-p al))
                (equal testvars (svex-env-override-test-vars env))
                (bind-free ;; (prog2$ (cw "testvars: ~x0~%" testvars)
                 `((known-tests . ,(acl2::pseudo-term-quote (collect-known-members-from-list-term testvars))))
                 (known-tests))
                (syntaxp (not (equal known-tests ''nil)))
                (bind-free (svtv-override-parameter-bindings mfc state)
                           (values non-composable-vars))
                (equal known-tests2 (set-difference-equal known-tests non-composable-vars))
                (syntaxp (not (equal known-tests2 ''nil)))
                (no-duplicatesp-equal (svarlist-fix known-tests2))
                (equal trips-exec (override-tests-to-svex-override-triplelist-exec known-tests2 values))
                (equal check (svexlist-check-overridetriples (svex-alist-vals al) trips-exec))
                (equal trips (override-tests-to-svex-override-triplelist known-tests2 values))
                (syntaxp (or (equal check ''nil)
                             (diagnose-overridetriple-check-result check trips)))
                (not check)
                (equal trips-vars (svex-override-triplelist-vars trips))
                (equal new-env (svex-env-removekeys trips-vars env))
                (force (svex-override-triplelist-env-ok trips env new-env)))
           (equal (svex-alist-eval al env)
                  (svex-alist-eval al new-env))))


(defthmd svtv-decomp-remove-override-vars-from-svex-eval-when-svexlist-check-overridetriples
  (implies (and (syntaxp (cmr::term-variable-free-p svex))
                (equal testvars (svex-env-override-test-vars env))
                (bind-free `((known-tests . ,(acl2::pseudo-term-quote (collect-known-members-from-list-term testvars))))
                           (known-tests))
                (syntaxp (not (equal known-tests ''nil)))
                (bind-free (svtv-override-parameter-bindings mfc state)
                           (values non-composable-vars))
                (equal known-tests2 (set-difference-equal known-tests non-composable-vars))
                (syntaxp (not (equal known-tests2 ''nil)))
                (no-duplicatesp-equal (svarlist-fix known-tests2))
                (equal trips-exec (override-tests-to-svex-override-triplelist-exec known-tests2 values))
                (equal check (svex-check-overridetriples svex trips-exec))
                (equal trips (override-tests-to-svex-override-triplelist known-tests2 values))
                (syntaxp (or (equal check ''nil)
                             (diagnose-overridetriple-check-result check trips)))
                (not check)
                (equal trips-vars (svex-override-triplelist-vars trips))
                (equal new-env (svex-env-removekeys trips-vars env))
                (force (svex-override-triplelist-env-ok trips env new-env)))
           (equal (svex-eval svex env)
                  (svex-eval svex new-env))))

(defthmd svtv-decomp-remove-override-vars-from-svexlist-eval-when-svexlist-check-overridetriples
  (implies (and (syntaxp (cmr::term-variable-free-p list))
                (equal testvars (svex-env-override-test-vars env))
                (bind-free `((known-tests . ,(acl2::pseudo-term-quote (collect-known-members-from-list-term testvars))))
                           (known-tests))
                (syntaxp (not (equal known-tests ''nil)))
                (no-duplicatesp-equal (svarlist-fix known-tests))
                (bind-free (svtv-override-parameter-bindings mfc state)
                           (values non-composable-vars))
                (equal known-tests2 (set-difference-equal known-tests non-composable-vars))
                (syntaxp (not (equal known-tests2 ''nil)))
                (no-duplicatesp-equal (svarlist-fix known-tests2))
                (equal trips-exec (override-tests-to-svex-override-triplelist-exec known-tests2 values))
                (equal check (svexlist-check-overridetriples list trips-exec))
                (equal trips (override-tests-to-svex-override-triplelist known-tests2 values))
                (syntaxp (or (equal check ''nil)
                             (diagnose-overridetriple-check-result check trips)))
                (not check)
                (equal trips-vars (svex-override-triplelist-vars trips))
                (equal new-env (svex-env-removekeys trips-vars env))
                (force (svex-override-triplelist-env-ok trips env new-env)))
           (equal (svexlist-eval list env)
                  (svexlist-eval list new-env))))


(defthmd svex-alist-eval-when-svexlist-variable-free-p
  (implies (and (syntaxp (and (quotep a)
                              (not (quotep env))))
                (svexlist-variable-free-p (svex-alist-vals a)))
           (equal (svex-alist-eval a env)
                  (svex-alist-eval a nil)))
  :hints(("Goal" :in-theory (enable svex-alist-eval
                                    svexlist-variable-free-p
                                    svex-alist-vals
                                    eval-when-svex-variable-free-p))))


(define svex-env-lookup-exec ((k svar-p) (x svex-env-p))
  :enabled t
  (svex-env-lookup k (make-fast-alist x))
  ///
  (defthm svex-env-lookup-use-exec
    (implies (and (syntaxp (quotep k))
                  (syntaxp (quotep x)))
             (equal (svex-env-lookup k x)
                    (svex-env-lookup-exec k x)))))

(encapsulate nil
  (local (defthm hons-assoc-equal-of-svex-alist-eval
           (equal (hons-assoc-equal v (svex-alist-eval al env))
                  (and (svar-p v)
                       (hons-assoc-equal v al)
                       (cons v (svex-eval (cdr (hons-assoc-equal v al)) env))))
           :hints(("Goal" :in-theory (enable svex-alist-eval)))))

  (local (defthm car-of-hons-assoc-equal
           (equal (car (hons-assoc-equal k x))
                  (and (hons-assoc-equal k x) k))))

  ;; ugh, need this for svtv-run's non-typesafe use of fal-extract etc
  (defthm svex-alist-eval-of-fal-extract
    (implies (svarlist-p vars)
             (equal (svex-alist-eval (fal-extract vars al) env)
                    (svex-env-reduce vars (svex-alist-eval al env))))
    :hints(("Goal" :in-theory (enable fal-extract svex-env-reduce svex-alist-eval svarlist-p)))))

(encapsulate nil
  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
  (local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
  (defthm 4vec-concat-of-rsh
    (implies (and (syntaxp (and (quotep w)
                                (quotep w1)))
                  (2vec-p w)
                  (<= 0 (2vec->val w))
                  (2vec-p w1)
                  (<= 0 (2vec->val w1)))
             (equal (4vec-concat w x (4vec-concat w1 (4vec-rsh w x) y))
                    (4vec-concat (2vec (+ (2vec->val w) (2vec->val w1))) x y)))
    :hints(("Goal" :in-theory (enable 4vec-concat 4vec-rsh 4vec-shift-core))
           (bitops::logbitp-reasoning)))

  (defthm 4vec-bit?!-of-4vec-concat
    (implies (and (syntaxp (and (quotep mask)
                                (quotep w)))
                  (2vec-p w)
                  (<= 0 (2vec->val w))
                  (4vec-no-1s-p (4vec-rsh w mask)))
             (equal (4vec-bit?! mask (4vec-concat w x y) z)
                    (4vec-bit?! mask x z)))
    :hints(("Goal" :in-theory (enable 4vec-concat 4vec-rsh 4vec-shift-core 4vec-bit?! 4vec-no-1s-p))
           (bitops::logbitp-reasoning :prune-examples nil)))

  (defthm 4vec-res-of-concat-zs-1
    (equal (4vec-res (4vec-concat w x (4vec-z))
                     (4vec-concat w (4vec-z) y))
           (4vec-concat w x y))
    :hints(("Goal" :in-theory (enable 4vec-res 4vec-concat))
           (bitops::logbitp-reasoning)))

  (defthm 4vec-res-of-concat-zs-2
    (equal (4vec-res (4vec-concat w (4vec-z) y)
                     (4vec-concat w x (4vec-z)))
           (4vec-concat w x y))
    :hints(("Goal" :in-theory (enable 4vec-res 4vec-concat))
           (bitops::logbitp-reasoning)))

  (defthm 4vec-res-z-1
    (equal (4vec-res (4vec-z) x)
           (4vec-fix x))
    :hints(("Goal" :in-theory (enable 4vec-res))))

  (defthm 4vec-res-z-2
    (equal (4vec-res x (4vec-z))
           (4vec-fix x))
    :hints(("Goal" :in-theory (enable 4vec-res)))))


(defthmd if-svex-lookup
  (implies (and (iff look (double-rewrite (svex-lookup k x)))
                (syntaxp (quotep look)))
           (equal (if (svex-lookup k x) y z)
                  (if look y z))))

(defthm nth-of-svex-envlist-extract
  (implies (< (nfix n) (len envs))
           (equal (nth n (svex-envlist-extract vars envs))
                  (svex-env-extract (nth n vars) (nth n envs))))
  :hints(("Goal" :in-theory (enable svex-envlist-extract nth svex-env-extract))))


(defthmd svex-alist-eval-of-cons
  (equal (svex-alist-eval (cons a b) env)
         (if (and (Consp a)
                  (svar-p (car a)))
             (cons (cons (car a) (svex-eval (cdr a) env))
                   (svex-alist-eval b env))
           (svex-alist-eval b env)))
  :hints(("Goal" :in-theory (enable svex-alist-eval))))

(defthm svex-alist-eval-of-nil
  (equal (svex-alist-eval nil env) nil)
  :hints(("Goal" :in-theory (enable svex-alist-eval))))



         

(defcong svex-envs-similar equal (svex-env-extract keys x) 2
  :hints(("Goal" :in-theory (enable svex-env-extract))))

(defcong svex-envs-equivalent equal (svex-env-reduce keys x) 2
  :hints(("Goal" :in-theory (enable svex-env-reduce-redef)
          :induct (len keys))))



                                    



(defthmd svex-env-lookup-of-svtv-name-lhs-map-eval
  (equal (svex-env-lookup key (svtv-name-lhs-map-eval namemap env))
         (let ((look (hons-assoc-equal (svar-fix key) namemap)))
           (if look
               (lhs-eval-zero (cdr look) env)
             (4vec-x))))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval
                                    svex-env-lookup))))

(defthm svex-env-removekeys-of-cons
  (equal (svex-env-removekeys keys (cons a b))
         (if (or (atom a)
                 (not (svar-p (car a)))
                 (member-equal (car a) (svarlist-fix keys)))
             (svex-env-removekeys keys b)
           (cons (cons (car a) (4vec-fix (cdr a)))
                 (svex-env-removekeys keys b))))
  :hints(("Goal" :in-theory (e/d (svex-env-removekeys)
                                 (member-equal)))))

(defthmd svex-env-removekeys-when-no-intersection
  (implies (not (intersectp-equal (svarlist-fix keys) (alist-keys (svex-env-fix env))))
           (equal (svex-env-removekeys keys env)
                  (svex-env-fix env)))
  :hints(("Goal" :in-theory (enable svex-env-removekeys alist-keys svex-env-fix))))

(defthmd svex-eval-of-var
  (implies (svex-case x :var)
           (equal (svex-eval x env)
                  (svex-env-lookup (svex-var->name x) env)))
  :hints(("Goal" :in-theory (enable svex-eval))))

(local (in-theory (disable acl2::hons-dups-p)))

(defthmd no-duplicatesp-equal-run-hons-dups-p
  (implies (syntaxp (quotep x))
           (equal (no-duplicatesp-equal x)
                  (not (acl2::hons-dups-p x)))))

(defthmd base-fsm->nextstate-of-svtv-fsm->renamed-fsm
  (equal (base-fsm->nextstate (svtv-fsm->renamed-fsm svtv-fsm))
         (base-fsm->nextstate (svtv-fsm->base-fsm svtv-fsm)))
  :hints(("Goal" :in-theory (enable svtv-fsm->renamed-fsm))))


(add-to-ruleset! svtv-env-autoins-in-terms-of-svex-env-extract nil)
(add-to-ruleset! svtv-pipeline-thms nil)
(add-to-ruleset! svtv-pipeline-thm-constants nil)

(acl2::set-ruleset! svtv-decomp-phase0-rules
  '((:DEFINITION HONS-COPY)
    (:DEFINITION MAKE-FAST-ALIST)
    (:DEFINITION ACL2::SVTV-RUN-FN)
    (:EXECUTABLE-COUNTERPART SVARLIST-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART svarlist-p)
    (:executable-counterpart binary-append)
    (:REWRITE ALIST-KEYS-OF-SVEX-ENV-EXTRACT)
    (:REWRITE RETURN-TYPE-OF-SVEX-ALIST-EVAL-FOR-SYMBOLIC)
    (:REWRITE SVEX-ALIST-EVAL-OF-SVEX-ENV-FIX-ENV)
    (:REWRITE SVEX-ENV-FIX-WHEN-SVEX-ENV-P)
    (:REWRITE SVEX-ENV-P-OF-SVEX-ENV-EXTRACT)
    (:REWRITE svex-alist-eval-of-fal-extract)
    (:rewrite svex-env-p-of-svex-env-reduce)
    (:ruleset svtv-env-autoins-in-terms-of-svex-env-extract)))

(acl2::set-ruleset! svtv-decomp-phase1-rules
  '((:CONGRUENCE SVEX-ENVS-EQUIVALENT-IMPLIES-SVEX-ENVS-EQUIVALENT-APPEND-1)
    (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-LOOKUP-2)
    (:CONGRUENCE svex-envs-similar-implies-equal-svex-env-extract-2)
    (:congruence SVEX-ENVS-EQUIVALENT-IMPLIES-EQUAL-SVEX-ENV-REDUCE-2)
    (:DEFINITION SYNP)
    (:EXECUTABLE-COUNTERPART LEN)
    (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->INITST$INLINE)
    (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->INPUTS$INLINE)
    (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->OVERRIDES$INLINE)
    (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->PROBES$INLINE)
    (:EXECUTABLE-COUNTERPART SVEX-ALIST-EVAL)
    (:EXECUTABLE-COUNTERPART SVEX-ALIST-VALS)
    (:EXECUTABLE-COUNTERPART SVEXLIST-VARIABLE-FREE-P)
    (:EXECUTABLE-COUNTERPART SVTV-PROBEALIST-OUTVARS)
    (:EXECUTABLE-COUNTERPART TAKE)
    (:META SVTV-FSM-RUN-INPUT-SUBSTS-EXECUTE-TERM-WHEN-VARIABLE-FREE)
    (:REWRITE SVEX-ALIST-EVAL-WHEN-SVEXLIST-VARIABLE-FREE-P)
    (:ruleset svtv-pipeline-thms)
    (:ruleset svtv-pipeline-thm-constants)))

(acl2::set-ruleset! svtv-decomp-phase2-rules
  '((:CONGRUENCE 4VEC-CONCAT-4VEC-EQUIV-CONGRUENCE-ON-HIGH)
    (:CONGRUENCE 4VEC-CONCAT-4VEC-EQUIV-CONGRUENCE-ON-LOW)
    (:CONGRUENCE 4VEC-RES-4VEC-EQUIV-CONGRUENCE-ON-A)
    (:CONGRUENCE 4VEC-RES-4VEC-EQUIV-CONGRUENCE-ON-B)
    (:CONGRUENCE BASE-FSM->NEXTSTATE$INLINE-BASE-FSM-EQUIV-CONGRUENCE-ON-X)
    (:CONGRUENCE BASE-FSM->VALUES$INLINE-BASE-FSM-EQUIV-CONGRUENCE-ON-X)
    (:CONGRUENCE BASE-FSM-EVAL-SVEX-ENVLIST-EQUIV-CONGRUENCE-ON-INS)
    (:CONGRUENCE SVAR-IFF-CONGRUENCE-ON-OVERRIDE-VAL)
    (:DEFINITION BASE-FSM-RUN)
    (:DEFINITION BASE-FSM-STEP)
    (:DEFINITION BASE-FSM-STEP-ENV)
    (:DEFINITION BASE-FSM-STEP-OUTS)
    (:DEFINITION DOUBLE-REWRITE)
    (:DEFINITION LHATOM-EVAL)
    (:DEFINITION LHRANGE-EVAL)
    (:DEFINITION MAKE-FAST-ALIST)
    (:DEFINITION SVEX-APPLY)
    (:DEFINITION SVEX-ENV-FASTLOOKUP)
    ;; (:DEFINITION SVEX-OVERRIDE-TRIPLELIST-ENV-OK)
    (:DEFINITION SVTV-FSM->NEXTSTATE)
    (:definition SVTV-FSM->RENAMED-FSM)
    (:DEFINITION SVTV-FSM->VALUES)
    (:DEFINITION SYNP)
    (:EQUIVALENCE IFF-IS-AN-EQUIVALENCE)
    (:EXECUTABLE-COUNTERPART 2VEC$INLINE)
    (:EXECUTABLE-COUNTERPART 2VEC->VAL$INLINE)
    (:EXECUTABLE-COUNTERPART 2VEC-P$INLINE)
    (:EXECUTABLE-COUNTERPART 4VEC-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART 4VEC-NO-1S-P)
    (:EXECUTABLE-COUNTERPART 4VEC-RSH)
    (:EXECUTABLE-COUNTERPART 4VECLIST-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART 4VECLIST-NTH-SAFE)
    (:EXECUTABLE-COUNTERPART <)
    (:EXECUTABLE-COUNTERPART ATOM)
    (:EXECUTABLE-COUNTERPART BINARY-+)
    (:EXECUTABLE-COUNTERPART CAR)
    (:EXECUTABLE-COUNTERPART CDR)
    (:EXECUTABLE-COUNTERPART CONS)
    (:EXECUTABLE-COUNTERPART CONSP)
    (:EXECUTABLE-COUNTERPART EQ)
    (:EXECUTABLE-COUNTERPART EQL)
    (:EXECUTABLE-COUNTERPART EQUAL)
    (:EXECUTABLE-COUNTERPART FNSYM-FIX)
    (:EXECUTABLE-COUNTERPART HONS-ASSOC-EQUAL)
    (:EXECUTABLE-COUNTERPART INTERSECTP-EQUAL)
    (:EXECUTABLE-COUNTERPART LEN)
    (:EXECUTABLE-COUNTERPART LHATOM-KIND$INLINE)
    (:EXECUTABLE-COUNTERPART LHATOM-VAR->NAME$INLINE)
    (:EXECUTABLE-COUNTERPART LHATOM-VAR->RSH$INLINE)
    (:EXECUTABLE-COUNTERPART LHRANGE->ATOM$INLINE)
    (:EXECUTABLE-COUNTERPART LHRANGE->W$INLINE)
    (:EXECUTABLE-COUNTERPART MEMBER-EQUAL)
    (:EXECUTABLE-COUNTERPART NFIX)
    (:EXECUTABLE-COUNTERPART acl2::hons-dups-p)
    (:EXECUTABLE-COUNTERPART NOT)
    (:EXECUTABLE-COUNTERPART NTH)
    (:EXECUTABLE-COUNTERPART SUBSETP-EQUAL)
    (:EXECUTABLE-COUNTERPART SVAR)
    (:EXECUTABLE-COUNTERPART SVAR->DELAY$INLINE)
    (:EXECUTABLE-COUNTERPART SVAR->NAME$INLINE)
    (:EXECUTABLE-COUNTERPART SVAR->NONBLOCKING$INLINE)
    (:EXECUTABLE-COUNTERPART SVAR->OVERRIDE-TEST$INLINE)
    (:EXECUTABLE-COUNTERPART SVAR->OVERRIDE-VAL$INLINE)
    (:EXECUTABLE-COUNTERPART SVAR-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART SVAR-P)
    (:EXECUTABLE-COUNTERPART SVARLIST-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART SVEX-CALL->ARGS$INLINE)
    (:EXECUTABLE-COUNTERPART SVEX-CALL->FN$INLINE)
    (:EXECUTABLE-COUNTERPART SVEX-ENV-EXTRACT)
    (:EXECUTABLE-COUNTERPART SVEX-ENV-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART SVEX-ENV-LOOKUP-EXEC)
    (:EXECUTABLE-COUNTERPART SVEX-ENV-OVERRIDE-TEST-VARS)
    (:EXECUTABLE-COUNTERPART SVEX-ENV-REMOVEKEYS)
    (:EXECUTABLE-COUNTERPART SVEX-KIND$INLINE)
    (:EXECUTABLE-COUNTERPART SVEX-QUOTE->VAL$INLINE)
    (:EXECUTABLE-COUNTERPART SVEX-VAR->NAME$INLINE)
    (:EXECUTABLE-COUNTERPART SVEX-VARS)
    (:EXECUTABLE-COUNTERPART SVEXLIST-QUOTESP)
    (:EXECUTABLE-COUNTERPART SVEXLIST-UNQUOTE)
    (:EXECUTABLE-COUNTERPART SVTV-NAME-LHS-MAP-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART SVTV-PROBE->SIGNAL$INLINE)
    (:EXECUTABLE-COUNTERPART SVTV-PROBE->TIME$INLINE)
    (:EXECUTABLE-COUNTERPART SVTV-PROBEALIST-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART ZP)
    (:EXECUTABLE-COUNTERPART set-difference-equal)
    (:EXECUTABLE-COUNTERPART binary-append)
    (:META SVEX-ALIST-KEYS-EXECUTE-TERM-WHEN-VARIABLE-FREE)
    (:META SVEX-FASTLOOKUP-EXECUTE-TERM-WHEN-VARIABLE-FREE)
    (:META SVEX-OVERRIDE-TRIPLELIST-VARS-EXECUTE-TERM-WHEN-VARIABLE-FREE)
    (:META SVEXLIST-CHECK-OVERRIDETRIPLES-EXECUTE-TERM-WHEN-VARIABLE-FREE)
    (:rewrite svex-lookup-when-variable-free)
    (:rewrite lhs-eval-zero-of-cons)
    (:rewrite lhs-eval-zero-of-nil)
    (:rewrite svex-override-triplelist-env-ok-of-cons)
    (:rewrite svex-override-triplelist-env-ok-of-nil)
    (:REWRITE 4VEC-BIT?!-OF-4VEC-CONCAT)
    (:REWRITE 4VEC-CONCAT-ASSOCIATIVE)
    (:REWRITE 4VEC-CONCAT-OF-RSH)
    (:REWRITE 4VEC-FIX-OF-4VEC)
    (:REWRITE 4VEC-FIX-UNDER-4VEC-EQUIV)
    (:REWRITE 4VEC-P-OF-4VEC-CONCAT)
    (:REWRITE 4VEC-P-OF-SVEX-ENV-LOOKUP)
    (:REWRITE 4VEC-RES-OF-CONCAT-ZS-1)
    (:REWRITE 4VEC-RES-OF-CONCAT-ZS-2)
    (:REWRITE 4VEC-RSH-0)
    (:REWRITE 4VECLIST-FIX-OF-CONS)
    (:REWRITE 4VECLIST-NTH-SAFE-OF-CONS)
    (:REWRITE ALIST-KEYS-OF-SVEX-ALIST-EVAL)
    (:REWRITE ACL2::APPEND-OF-CONS)
    (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
    (:REWRITE BASE-FSM->NEXTSTATE-OF-BASE-FSM)
    (:REWRITE BASE-FSM->VALUES-OF-BASE-FSM)
    (:REWRITE BASE-FSM-EVAL-OF-CONS)
    (:REWRITE BASE-FSM-FIX-UNDER-BASE-FSM-EQUIV)
    (:REWRITE BOUNDP-OF-SVTV-PROBEALIST-EXTRACT)
    (:REWRITE CAR-CONS)
    (:REWRITE CDR-CONS)
    (:REWRITE EVAL-OF-SVTV-NAME-LHS-MAP-COMPOSE)
    (:REWRITE IF-SVEX-LOOKUP)
    (:REWRITE LEN-OF-BASE-FSM-EVAL)
    (:REWRITE fty::LEN-OF-CONS)
    (:REWRITE ACL2::LIST-FIX-UNDER-LIST-EQUIV)
    (:REWRITE LOOKUP-OF-SVTV-PROBEALIST-EXTRACT)
    (:REWRITE NTH-0-CONS)
    (:REWRITE NTH-ADD1)
    (:REWRITE NTH-OF-SVEX-ENVLIST-EXTRACT)
    (:REWRITE OVERRIDE-TESTS-TO-SVEX-OVERRIDE-TRIPLELIST-OF-CONS)
    (:REWRITE OVERRIDE-TESTS-TO-SVEX-OVERRIDE-TRIPLELIST-OF-NIL)
    (:REWRITE
     SVTV-DECOMP-REMOVE-OVERRIDE-VARS-FROM-SVEX-ALIST-EVAL-WHEN-SVEXLIST-CHECK-OVERRIDETRIPLES)
    (:REWRITE
     SVTV-DECOMP-REMOVE-OVERRIDE-VARS-FROM-SVEXLIST-EVAL-WHEN-SVEXLIST-CHECK-OVERRIDETRIPLES)
    (:REWRITE
     SVTV-DECOMP-REMOVE-OVERRIDE-VARS-FROM-SVEX-EVAL-WHEN-SVEXLIST-CHECK-OVERRIDETRIPLES)
    (:REWRITE RETURN-TYPE-OF-SVEX-LOOKUP)
    (:REWRITE SVEX-ALIST-EVAL-OF-CONS)
    (:REWRITE SVEX-ALIST-EVAL-OF-NIL)
    (:REWRITE SVEX-ALIST-FIX-WHEN-SVEX-ALIST-P)
    (:REWRITE SVEX-ALIST-P-OF-BASE-FSM->NEXTSTATE)
    (:REWRITE SVEX-ALIST-P-OF-SVTV-NAME-LHS-MAP-COMPOSE)
    (:REWRITE SVEX-ALISTLIST-EVAL-OF-CONS)
    (:REWRITE SVEX-ALISTLIST-EVAL-OF-NIL)
    (:REWRITE SVEX-ENV-BOUNDP-OF-SVEX-ALIST-EVAL)
    (:REWRITE SVEX-ENV-EXTRACT-WHEN-ALIST-KEYS-EQUAL)
    (:REWRITE SVEX-ENV-FIX-OF-ACONS)
    (:REWRITE SVEX-ENV-FIX-WHEN-SVEX-ENV-P)
    (:REWRITE SVEX-ENV-LOOKUP-OF-APPEND)
    (:REWRITE SVEX-ENV-LOOKUP-OF-CONS)
    (:REWRITE SVEX-ENV-LOOKUP-OF-SVEX-ALIST-EVAL)
    (:REWRITE SVEX-ENV-LOOKUP-OF-SVEX-ENV-EXTRACT)
    (:REWRITE SVEX-ENV-LOOKUP-OF-SVTV-NAME-LHS-MAP-EVAL)
    (:REWRITE SVEX-ENV-LOOKUP-USE-EXEC)
    (:REWRITE SVEX-ENV-OVERRIDE-TEST-VARS-OF-APPEND)
    (:REWRITE SVEX-ENV-OVERRIDE-TEST-VARS-OF-CONS)
    (:REWRITE SVEX-ENV-P-OF-SVEX-ALIST-EVAL)
    (:REWRITE SVEX-ENV-REMOVEKEYS-OF-APPEND)
    (:REWRITE SVEX-ENV-REMOVEKEYS-OF-CONS)
    (:REWRITE SVEX-ENV-REMOVEKEYS-WHEN-NO-INTERSECTION)
    (:REWRITE SVEX-EVAL-EXTRACT-VAR-SUPERSET)
    (:REWRITE SVEX-EVAL-OF-QUOTED)
    (:REWRITE SVEX-EVAL-OF-VAR)
    (:REWRITE SVEX-EVAL-WHEN-QUOTE)
    (:REWRITE SVEX-FIX-WHEN-SVEX-P)
    (:rewrite svex-env-boundp-of-svex-env-reduce)
    (:rewrite svex-env-lookup-of-svex-env-reduce)
    (:REWRITE SVEX-OVERRIDE-TRIPLE->TESTVAR-OF-SVEX-OVERRIDE-TRIPLE)
    (:REWRITE SVEX-OVERRIDE-TRIPLE->VALEXPR-OF-SVEX-OVERRIDE-TRIPLE)
    (:REWRITE SVEX-OVERRIDE-TRIPLE->VALVAR-OF-SVEX-OVERRIDE-TRIPLE)
    (:REWRITE SVEXLIST-EVAL-OF-CONS)
    (:REWRITE SVEXLIST-UNQUOTE-CORRECT)
    (:REWRITE SVTV-FSM->BASE-FSM-OF-SVTV-FSM)
    (:REWRITE SVTV-FSM->NAMEMAP-OF-SVTV-FSM)
    (:REWRITE ACL2::TAKE-OF-LEN-FREE)
    ;; (:rewrite base-fsm->nextstate-of-svtv-fsm->renamed-fsm)
    (:rewrite no-duplicatesp-equal-run-hons-dups-p)
    (:TYPE-PRESCRIPTION 4VEC-CONCAT)))




(defun svtv-decomp-hints-fn (enables disables forcep)
  `'(:computed-hint-replacement
     ((and stable-under-simplificationp
           '(:in-theory (e/d** (svtv-decomp-phase1-rules))))
      (and stable-under-simplificationp
           '(:in-theory (e/d** (svtv-decomp-phase2-rules
                                . ,(and forcep '((force))))))))
     :in-theory (e/d** (svtv-decomp-phase0-rules
                        . ,enables)
                       ,disables)))


(defmacro svtv-decomp-hints (&key enables disables forcep)
  (svtv-decomp-hints-fn enables disables forcep))
