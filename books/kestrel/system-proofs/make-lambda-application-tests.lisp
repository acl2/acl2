; Tests and examples for make-lambda-application.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Counterexamples and examples for the theorems in
;; make-lambda-application.lisp.  This book is not included by top.lisp.

(include-book "make-lambda-application")

;; The NO-DUPLICATESP-EQUAL hypotheses of the theorems in
;; make-lambda-application.lisp about the lambda it makes are needed: with
;; duplicate formals, the lambda has duplicate formals.
(defthm make-lambda-application-can-make-duplicate-formals
  (let ((formals '(x x)))
    (and (not (no-duplicatesp-equal formals))
         (equal (make-lambda-application formals '(f x) '(a b))
                '((lambda (x x) (f x)) a b))))
  :rule-classes nil)
