; Tests and examples for termify-clause-set.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Counterexamples and examples for the theorems in termify-clause-set.lisp.
;; This book is not included by top.lisp.

(include-book "termify-clause-set")

;; Without the true-listp hypothesis, the result can be false when
;; CONJOIN-CLAUSES is true, since termify-clause-set tests for the end of the
;; list with NULL but disjoin-lst uses ENDP:
(defthm termify-clause-set-incorrect-without-true-listp
  (let ((clauses 'a))
    (and (equal (termify-clause-set clauses) *nil*)
         (equal (conjoin-clauses clauses) *t*)))
  :rule-classes nil)
