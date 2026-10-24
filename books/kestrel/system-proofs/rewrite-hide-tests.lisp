; Tests and examples for rewrite-hide.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; Counterexamples and examples for the theorems in rewrite-hide.lisp.  This
;; book is not included by top.lisp.

(include-book "rewrite-hide")

;; The lambdas must be closed (as they are in a TERMP).  Otherwise, a free
;; variable of a lambda body, which always evaluates to NIL there, can be
;; captured from the outside:
(defthm lambda-nest-unhide-needs-closed-lambdas
  (let ((term '((lambda (x) (hide y)) a))
        (a '((y . 1))))
    (and (lambda-nest-hidep term)
         (pseudo-termp term)
         (no-nils-in-termp term)
         (not (lambdas-closed-in-termp term))
         (equal (lambda-nest-unhide term) '((lambda (y) y) y))
         (equal (hide-eval (lambda-nest-unhide term) a) 1)
         (equal (hide-eval term a) nil)))
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes nil)

;; The theorems in rewrite-hide.lisp about the free variables of the result of
;; lambda-nest-unhide and about no-nils-in-termp need more than the hyps of
;; the other theorems (here, that the HIDE has an argument, which TERMP
;; ensures): when the HIDE has no argument, NIL appears as a variable in the
;; result.
(defthm lambda-nest-unhide-when-hide-has-no-argument
  (let ((term '((lambda (x) (hide)) a)))
    (and (lambda-nest-hidep term)
         (pseudo-termp term)
         (lambdas-closed-in-termp term)
         (no-nils-in-termp term)
         (equal (free-vars-in-term term) '(a))
         (equal (lambda-nest-unhide term)
                '((lambda (nil) nil) nil))
         (not (no-nils-in-termp (lambda-nest-unhide term)))
         (equal (free-vars-in-term (lambda-nest-unhide term)) '(nil))))
  :rule-classes nil)
