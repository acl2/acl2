; Top file for terms-light library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-quotep")
(include-book "bound-vars-in-term")
(include-book "let-vars-in-term")
(include-book "free-vars-in-term")
(include-book "sublis-var-simple")
(include-book "sublis-var-and-magic-eval")
(include-book "expr-calls-fn")
(include-book "unary-lambdap")
(include-book "wrap-pattern-around-term")
(include-book "lambda-free-termp")
(include-book "lambdas-closed-in-termp")
(include-book "expand-lambdas-in-term")
(include-book "expand-lambdas-in-term-proof")
(include-book "add-param-to-calls-in-term")
