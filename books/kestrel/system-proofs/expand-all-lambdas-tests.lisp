; Tests and examples for expand-all-lambdas.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; Counterexamples and examples for the theorems in expand-all-lambdas.lisp.
;; This book is not included by top.lisp.

(include-book "expand-all-lambdas")

;; Counterexamples showing that the hyps of expand-all-lambdas-correct (other
;; than pseudo-termp) cannot be dropped (the same terms work for remove-lambdas):

(defthm expand-all-lambdas-incorrect-without-lambdas-closed
  (let ((term '((lambda (x) y) '1))
        (a '((y . 5))))
    (and (pseudo-termp term)
         (no-nils-in-termp term)
         (not (lambdas-closed-in-termp term))
         (equal (expand-all-lambdas term) 'y)
         (not (equal (cterm-ev (expand-all-lambdas term) a)
                     (cterm-ev term a)))))
  :rule-classes nil)

(defthm expand-all-lambdas-incorrect-without-no-nils
  (let ((term '((lambda (nil) nil) '5))
        (a nil))
    (and (pseudo-termp term)
         (lambdas-closed-in-termp term)
         (not (no-nils-in-termp term))
         (equal (expand-all-lambdas term) ''5)
         (not (equal (cterm-ev (expand-all-lambdas term) a)
                     (cterm-ev term a)))))
  :rule-classes nil)
