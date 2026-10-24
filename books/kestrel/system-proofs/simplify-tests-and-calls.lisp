; Correctness of the ACL2 system function that simplifies the cases of an
; induction machine
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The induction machine of a recursive function (see induction-machine-for-fn
;; in induct.lisp) is a list of TESTS-AND-CALLS records, one for each case: the
;; tests that govern the case, and the recursive calls made in it.
;; SIMPLIFY-TESTS-AND-CALLS-LST cleans up each record with
;; SIMPLIFY-TESTS-AND-CALLS, which removes guard holders from the tests and
;; calls and then, if some test equates a term with a constant, drops the
;; negated tests that equate that term with other constants.  This book proves
;; that the simplified tests are true exactly when the original ones are, and
;; that the simplified calls have the same values as the original ones, so
;; the induction schemes ACL2 builds from the machine are unaffected.

; cert_param: (non-acl2r)

(include-book "add-literal-smart")
(include-book "remove-guard-holders1")
(include-book "remove-guard-holders1-properties")

;; These functions are in :program mode in the sources.  We put them in
;; :logic mode here.
(verify-termination remove-guard-holders-weak-lst) ; and guards
(verify-termination simplify-tests-and-calls)
(verify-termination simplify-tests-and-calls-lst)

;; An evaluator that knows the functions that remove-guard-holders1 treats
;; specially (and the primitives that cons-term may evaluate), and those that
;; the functions in add-literal-smart.lisp treat specially:
(defevaluator+ tests-eval
  acl2-numberp binary-* binary-+ unary-- unary-/ < car cdr char-code characterp code-char
  complex complex-rationalp coerce cons consp denominator equal imagpart integerp
  intern-in-package-of-symbol numerator rationalp realpart stringp symbol-name
  symbol-package-name symbolp if not
  return-last mv-list the-check cons-with-hint to-df from-df df0 df1 do$
  iff hard-error eq eql =)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The results of remove-guard-holders1.lisp and add-literal-smart.lisp, for
;;; this evaluator

(defthm remove-guard-holders-weak-lst-correct-for-tests-eval
  (implies (and (term-listp lst w)
                (remove-guard-holders1-arities-okp w))
           (equal (tests-eval-list (remove-guard-holders-weak-lst lst lamp) a)
                  (tests-eval-list lst a)))
  :hints (("Goal" :in-theory (e/d (tests-eval-of-fncall-args
                                   remove-guard-holders-weak-lst
                                   remove-guard-holders1-arities-okp)
                                  (tests-eval-of-fncall-args-back))
           :use (:functional-instance remove-guard-holders1-lst-correct
                                      (remove-guard-holders-eval tests-eval)
                                      (remove-guard-holders-eval-list tests-eval-list)))))

(defthm simplify-tests-of-term-equated-to-constant-in-termlist-correct-for-tests-eval
  (implies (pseudo-term-listp tests)
           (iff (tests-eval
                 (conjoin (mv-let (var const)
                            (term-equated-to-constant-in-termlist tests)
                            (if var
                                (mv-nth 1 (simplify-tests var const tests))
                              tests)))
                 a)
                (tests-eval (conjoin tests) a)))
  :hints (("Goal" :in-theory (e/d (tests-eval-of-fncall-args)
                                  (tests-eval-of-fncall-args-back
                                   tests-eval-of-conjoin))
           :use (:functional-instance simplify-tests-of-term-equated-to-constant-in-termlist-correct
                                      (smart-eval tests-eval)
                                      (smart-eval-list tests-eval-list)))))

(defthm term-listp-of-remove-guard-holders-weak-lst
  (implies (and (term-listp lst w)
                (remove-guard-holders1-arities-okp w))
           (term-listp (remove-guard-holders-weak-lst lst lamp) w))
  :hints (("Goal" :in-theory (enable remove-guard-holders-weak-lst))))

(local
 (defthm pseudo-term-listp-of-remove-guard-holders-weak-lst
   (implies (and (term-listp lst w)
                 (remove-guard-holders1-arities-okp w))
            (pseudo-term-listp (remove-guard-holders-weak-lst lst lamp)))
   :hints (("Goal" :use (term-listp-of-remove-guard-holders-weak-lst
                         (:instance term-listp-implies-pseudo-term-listp
                                    (x (remove-guard-holders-weak-lst lst lamp))))
            :in-theory (disable term-listp-of-remove-guard-holders-weak-lst
                                term-listp-implies-pseudo-term-listp
                                remove-guard-holders-weak-lst)))))

;; Lists of terms with the same values are all true together.
(local
 (defun cdr-cdr-induct (x y)
   (if (or (endp x) (endp y))
       (list x y)
     (cdr-cdr-induct (cdr x) (cdr y)))))

(defthm all-eval-to-true-with-tests-eval-when-equal-of-tests-eval-list
  (implies (equal (tests-eval-list x a)
                  (tests-eval-list y a))
           (equal (all-eval-to-true-with-tests-eval x a)
                  (all-eval-to-true-with-tests-eval y a)))
  :rule-classes nil
  :hints (("Goal" :induct (cdr-cdr-induct x y)
           :in-theory (enable all-eval-to-true-with-tests-eval))
          ("Subgoal *1/2" :use ((:instance car-of-tests-eval-list (terms x))
                                (:instance car-of-tests-eval-list (terms y))
                                (:instance cdr-of-tests-eval-list (terms x))
                                (:instance cdr-of-tests-eval-list (terms y))
                                (:instance len-of-tests-eval-list (terms x))
                                (:instance len-of-tests-eval-list (terms y)))
           :in-theory (e/d (all-eval-to-true-with-tests-eval)
                           (car-of-tests-eval-list cdr-of-tests-eval-list
                            len-of-tests-eval-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; SIMPLIFY-TESTS-AND-CALLS

;; The simplified tests are true exactly when the original tests are, and the
;; simplified calls have the values of the original calls.
(defthm simplify-tests-and-calls-correct
  (implies (and (term-listp (access tests-and-calls tc :tests) w)
                (term-listp (access tests-and-calls tc :calls) w)
                (remove-guard-holders1-arities-okp w))
           (and (iff (tests-eval (conjoin (access tests-and-calls (simplify-tests-and-calls tc) :tests)) a)
                     (tests-eval (conjoin (access tests-and-calls tc :tests)) a))
                (equal (tests-eval-list (access tests-and-calls (simplify-tests-and-calls tc) :calls) a)
                       (tests-eval-list (access tests-and-calls tc :calls) a))))
  :hints (("Goal" :in-theory (e/d (simplify-tests-and-calls)
                                  (simplify-tests-of-term-equated-to-constant-in-termlist-correct-for-tests-eval
                                   remove-guard-holders-weak-lst
                                   term-equated-to-constant-in-termlist-becomes-term-equated-to-constant))
           :use ((:instance simplify-tests-of-term-equated-to-constant-in-termlist-correct-for-tests-eval
                            (tests (remove-guard-holders-weak-lst (access tests-and-calls tc :tests) nil)))
                 (:instance all-eval-to-true-with-tests-eval-when-equal-of-tests-eval-list
                            (x (remove-guard-holders-weak-lst (access tests-and-calls tc :tests) nil))
                            (y (access tests-and-calls tc :tests)))))))

;; SIMPLIFY-TESTS-AND-CALLS-LST applies simplify-tests-and-calls to each
;; record.
(defthm len-of-simplify-tests-and-calls-lst
  (equal (len (simplify-tests-and-calls-lst tc-list))
         (len tc-list))
  :hints (("Goal" :in-theory (enable simplify-tests-and-calls-lst))))

(defthm nth-of-simplify-tests-and-calls-lst
  (implies (< (nfix n) (len tc-list))
           (equal (nth n (simplify-tests-and-calls-lst tc-list))
                  (simplify-tests-and-calls (nth n tc-list))))
  :hints (("Goal" :in-theory (e/d (simplify-tests-and-calls-lst nth)
                                  (simplify-tests-and-calls)))))

;; The simplified tests and calls are terms.
(defthm term-listp-of-simplify-tests-and-calls
  (implies (and (term-listp (access tests-and-calls tc :tests) w)
                (term-listp (access tests-and-calls tc :calls) w)
                (remove-guard-holders1-arities-okp w))
           (and (term-listp (access tests-and-calls (simplify-tests-and-calls tc) :tests) w)
                (term-listp (access tests-and-calls (simplify-tests-and-calls tc) :calls) w)))
  :hints (("Goal" :in-theory (e/d (simplify-tests-and-calls)
                                  (remove-guard-holders-weak-lst
                                   term-equated-to-constant-in-termlist-becomes-term-equated-to-constant)))))
