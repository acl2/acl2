; Tests and examples for clause-sets.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Counterexamples and examples for the theorems in clause-sets.lisp.  This
;; book is not included by top.lisp.

(include-book "clause-sets")

;; The literal must be a pseudo-term, because a malformed quoted constant such
;; as (QUOTE NIL NIL), whose value is NIL, is treated as a true literal:
(defthm add-literal-needs-pseudo-termp
  (let ((lit '(quote nil nil)))
    (and (not (pseudo-termp lit))
         (equal (add-literal lit nil nil) *true-clause*)
         (not (clause-set-eval lit a))
         (clause-set-eval (disjoin (add-literal lit nil nil)) a)))
  :hints (("Goal" :in-theory (enable add-literal)))
  :rule-classes nil)
