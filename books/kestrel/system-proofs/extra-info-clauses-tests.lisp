; Tests and examples for extra-info-clauses.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Counterexamples and examples for the theorems in extra-info-clauses.lisp.
;; This book is not included by top.lisp.

(include-book "extra-info-clauses")

;; Conjoin-clause-sets-extra-info tests for the end of CL-SET1 with NULL, so
;; for a CL-SET1 that is a non-NIL atom, it adds the empty (false) clause:
(defthm conjoin-clause-sets-extra-info-needs-true-listp
  (and (equal (conjoin-clause-sets-extra-info 'foo nil)
              '(nil))
       (extra-info-clause-set-true 'foo a)
       (not (extra-info-clause-set-true (conjoin-clause-sets-extra-info 'foo nil) a)))
  :rule-classes nil)
