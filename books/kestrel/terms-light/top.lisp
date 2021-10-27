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
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "expand-lambdas-in-term")
(include-book "expand-lambdas-in-term-proof")
(include-book "add-param-to-calls-in-term")
(include-book "rename-vars-in-term")
(include-book "count-ifs-in-term")
(include-book "count-ifs-in-then-and-else-branches")
(include-book "combine-ifs-in-then-and-else-branches")
(include-book "restore-mv-in-branches")
(include-book "logic-termp")
(include-book "negate-term")
(include-book "negate-term-proof")
(include-book "negate-terms")
(include-book "simplify-conjunction")
(include-book "term-is-conjunctionp")
(include-book "clearly-implies-for-disjunctionp")
(include-book "make-if-term")
(include-book "make-if-term-proof")
(include-book "strengthen-conjuncts")
