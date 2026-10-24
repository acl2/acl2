; Tests and examples for add-literal-smart.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Counterexamples and examples for the theorems in add-literal-smart.lisp.
;; This book is not included by top.lisp.

(include-book "add-literal-smart")

;;; The literals and tests must be pseudo-terms

;; Adding (NOT (EQUAL X '1)) to a clause containing the malformed literal
;; (EQUAL X (QUOTE 1 2)), whose value is that of (EQUAL X '1), drops that
;; literal, because (QUOTE 1 2) differs from '1.  So a clause that is true
;; becomes one that is false when X is 1.
(defthm add-literal-smart-needs-pseudo-term-listp
  (let ((lit '(not (equal x '1)))
        (cl '((equal x (quote 1 2))))
        (a '((x . 1))))
    (and (pseudo-termp lit)
         (not (pseudo-term-listp cl))
         (equal (add-literal-smart lit cl nil)
                '((not (equal x '1))))
         (smart-eval (disjoin (cons lit cl)) a)
         (not (smart-eval (disjoin (add-literal-smart lit cl nil)) a))))
  :hints (("Goal" :in-theory (enable add-literal-smart smart-eval-of-disjoin)))
  :rule-classes nil)

;; Likewise, adding the test (EQUAL X '1) to the malformed test
;; (NOT (EQUAL X (QUOTE 1 2))) drops that test, so tests that are
;; contradictory become tests that are true when X is 1.
(defthm add-test-smart-needs-pseudo-term-listp
  (let ((test '(equal x '1))
        (tests '((not (equal x (quote 1 2)))))
        (a '((x . 1))))
    (and (pseudo-termp test)
         (not (pseudo-term-listp tests))
         (equal (add-test-smart test tests)
                '((equal x '1)))
         (not (smart-eval (conjoin (cons test tests)) a))
         (smart-eval (conjoin (add-test-smart test tests)) a)))
  :hints (("Goal" :in-theory (enable add-test-smart)))
  :rule-classes nil)
