; Top file for terms-light library
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Books about built-in functions:
(include-book "termp")
(include-book "logic-fnsp")
(include-book "logic-termp")
(include-book "all-fnnames1")
(include-book "arglistp1")

;; Utilities:
(include-book "filter-formals-and-actuals")
(include-book "filter-formals-and-actuals-proofs")
(include-book "termp-simple")
(include-book "all-quotep")
(include-book "trivial-formals")
(include-book "non-trivial-formals")
(include-book "non-trivial-formals-and-args")
(include-book "bound-vars-in-term")
(include-book "let-vars-in-term")
(include-book "free-vars-in-term")
(include-book "expr-calls-fn")
(include-book "unary-lambdap")
(include-book "wrap-pattern-around-term")
(include-book "lambda-free-termp")
(include-book "lambdas-closed-in-termp")
(include-book "all-lambdas-serialized-in-termp")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "count-ifs-in-term")
(include-book "count-ifs-in-then-and-else-branches")
(include-book "negate-term")
(include-book "negate-term-proof")
(include-book "negate-terms")
(include-book "drop-clearly-implied-conjuncts")
(include-book "term-is-conjunctionp")
(include-book "clearly-implies-for-disjunctionp")
(include-book "make-if-term")
(include-book "make-if-term-proof")
(include-book "strengthen-conjuncts")
(include-book "make-lambda-term-simple")
(include-book "make-lambda-terms-simple")
(include-book "make-lambda-application-simple")
(include-book "make-lambda-application-simple-proof")
(include-book "function-call-subterms")
(include-book "count-occurrences-in-term")
(include-book "no-nils-in-termp")
(include-book "get-conjuncts")
(include-book "get-hyps-and-conc")
(include-book "replace-corresponding-arg")
(include-book "substitute-lambda-formals")
(include-book "classify-lambda-formals")
(include-book "count-vars")
(include-book "make-lambda-with-hint")

(include-book "helpers")
(include-book "empty-eval-helpers")

(include-book "sublis-var-simple")
(include-book "sublis-var-simple-proofs")
(include-book "subst-var-alt")
(include-book "subst-var-alt-proofs")
(include-book "subst-var-deep")
(include-book "subst-var-deep-proofs")
(include-book "sublis-var-and-magic-eval")

;; Template transformation:
(include-book "copy-term")
(include-book "copy-term-proofs")

;; Transformations (and their proofs):
(include-book "combine-ifs-in-then-and-else-branches")
(include-book "add-param-to-calls-in-term")
(include-book "let-bind-formals-in-calls")
(include-book "rename-vars-in-term")
(include-book "restore-mv-in-branches")
(include-book "restore-mv-lets-in-term")
(include-book "reconstruct-lets-in-term")
(include-book "simplify-ors")
(include-book "simplify-ors-proofs")
(include-book "replace-term-with-term")

;; Transformations about lambdas (and their proofs):
(include-book "serialize-lambdas-in-term")
(include-book "serialize-lambdas-in-term-proofs") ; incomplete
(include-book "expand-lambdas-in-term")
(include-book "expand-lambdas-in-term-proofs")
;; Deal with lambda vars that are only used once:
(include-book "substitute-unnecessary-lambda-vars")
(include-book "substitute-unnecessary-lambda-vars2")
(include-book "substitute-unnecessary-lambda-vars2-proofs")
;; Drop unused lambda bindings:
(include-book "drop-unused-lambda-bindings") ; todo rename file
(include-book "drop-unused-lambda-bindings-proofs") ; todo rename file
;; Handle lambda vars bound to constants:
(include-book "substitute-constants-in-lambdas")
(include-book "substitute-constants-in-lambdas-proofs")
;; For lambdas whose formals are the same as their args:
(include-book "drop-trivial-lambdas")
(include-book "drop-trivial-lambdas-proofs")
;; Combines several transformations on lambdas:
(include-book "pre-simplify-term")
(include-book "pre-simplify-term-proofs")
