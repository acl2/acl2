; Tests and examples for flatten-ands-in-lit.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Counterexamples and examples for the theorems in flatten-ands-in-lit.lisp.
;; This book is not included by top.lisp.

(include-book "flatten-ands-in-lit")

;; No-nils-in-termp is not preserved for malformed terms, but it is implied by
;; termp:
(defthm dumb-negate-lit-can-introduce-nil
  (equal (dumb-negate-lit '(not)) nil)
  :rule-classes nil)
