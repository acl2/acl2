; Top file for axe/risc-v/ directory
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Rules about risc-v:
(include-book "risc-v-rules")
(include-book "read-and-write")
(include-book "read-over-write-rules")
(include-book "write-over-write-rules")
(include-book "clear-writes")
(include-book "pc")
(include-book "registers")
(include-book "support")

;; Support for proofs using the ACL2 rewriter rather than Axe's rewriter/lifter:
(include-book "support-non-axe")

;; Support files:
(include-book "assumptions")
(include-book "run-until-return")
(include-book "rule-lists")
;(include-book "tester-rules")
;(include-book "tester-rules-bv")
(include-book "evaluator")
(include-book "syntax-functions")
(include-book "syntaxp-evaluator")
;(include-book "bind-free-evaluator")
(include-book "rewriter")

;;Lifters:
(include-book "lifter-rules")
(include-book "unroller")
;(include-book "loop-lifter")

;; Formal Unit Tester:
;(include-book "tester")

;; Equivalence checker for risc-v binary functions
;(include-book "prove-equivalence")

;; (include-book "examples/top") ; not including examples in top.lisp files

;; Documentation:
(include-book "doc")
