; Top file for the JVM-related Axe tools
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Axe syntax stuff:
(include-book "axe-syntax-functions-jvm")
(include-book "axe-syntax-functions-jvm2")

;; Evaluators:
(include-book "evaluator-jvm")
(include-book "axe-syntaxp-evaluator-jvm")
(include-book "axe-bind-free-evaluator-jvm")

;; Axe-specific rules:
(include-book "jvm-rules-axe")
(include-book "jvm-rules-axe2")

;; Lists of rules
(include-book "rule-lists-jvm")

;; Collect up JVM rules:
(include-book "rules-in-rule-lists-jvm")

(include-book "rewriter-jvm") ; newest JVM-aware rewriter

;; Utilities:
(include-book "output-indicators")
(include-book "nice-output-indicators")

;; JVM lifters:
(include-book "lifter-utilities")
(include-book "lifter-utilities2")
(include-book "lifter-utilities3")
(include-book "unroll-java-code-common")
(include-book "unroll-java-code")
(include-book "unroll-java-code2")
(include-book "lifter")
(include-book "lifter2")

(include-book "formal-unit-tester")
