; Top file for axe/x86 directory
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Support files:
(include-book "rule-lists")
(include-book "x86-rules")
(include-book "tester-rules")
(include-book "tester-rules-bv")
(include-book "evaluator-x86")
(include-book "syntaxp-evaluator-x86")
(include-book "bind-free-evaluator-x86")
(include-book "rewriter-x86")

;;Lifters:
(include-book "unroll-x86-code")
(include-book "loop-lifter")

;; Formal Unit Tester:
(include-book "tester")

;; Equivalence checker for x86 binary functions
(include-book "prove-equivalence")

;; (include-book "examples/top") ; not including examples in top.lisp files
