; Top file for the JVM-related Axe tools
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Axe syntax stuff:
(include-book "axe-syntax-functions-jvm")
(include-book "axe-syntax-functions-jvm2")

;; Evaluators for axe-syntaxp and axe-bind-free functions:
(include-book "axe-syntaxp-evaluator-jvm")
(include-book "axe-bind-free-evaluator-jvm")
