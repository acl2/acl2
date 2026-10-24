; Tests and examples for remove-lambdas.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; Counterexamples and examples for the theorems in remove-lambdas.lisp.  This
;; book is not included by top.lisp.

(include-book "remove-lambdas")

;; Counterexamples showing that the hyps of remove-lambdas-correct (other than
;; pseudo-termp) cannot be dropped:

;; Without closed lambdas, remove-lambdas can capture a variable that the
;; lambda body could not see:
(defthm remove-lambdas-incorrect-without-lambdas-closed
  (let ((term '((lambda (x) y) '1))
        (a '((y . 5))))
    (and (pseudo-termp term)
         (no-nils-in-termp term)
         (not (lambdas-closed-in-termp term))
         (equal (remove-lambdas term) 'y)
         (not (equal (cterm-ev (remove-lambdas term) a)
                     (cterm-ev term a)))))
  :rule-classes nil)

;; The "variable" NIL always evaluates to NIL, even when it is a lambda formal,
;; but remove-lambdas can replace it with something else:
(defthm remove-lambdas-incorrect-without-no-nils
  (let ((term '((lambda (nil) nil) '5))
        (a nil))
    (and (pseudo-termp term)
         (lambdas-closed-in-termp term)
         (not (no-nils-in-termp term))
         (equal (remove-lambdas term) ''5)
         (not (equal (cterm-ev (remove-lambdas term) a)
                     (cterm-ev term a)))))
  :rule-classes nil)
