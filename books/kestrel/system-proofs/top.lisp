; Correctness proofs about ACL2 system functions
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; This directory contains proofs that term-transforming functions in the ACL2
;; sources preserve the meanings of terms, as stated using evaluators.  The
;; sources are not changed: most of the functions proved about are already in
;; :logic mode, with guards verified (see *system-verify-guards-alist*), and
;; the books put the others in :logic mode with verify-termination.  See
;; README.md.

(include-book "cterm-ev-helpers")
(include-book "cons-term-helpers")
(include-book "helpers")
(include-book "subst-var")
(include-book "subst-expr")
(include-book "subcor-var")
(include-book "fsubcor-var")
(include-book "remove-lambdas")
(include-book "expand-all-lambdas")
(include-book "flatten-ands-in-lit")
(include-book "implicate")
(include-book "termify-clause-set")
(include-book "unmake-true-list-cons-nest")
(include-book "make-lambda-application")
(include-book "one-way-unify")
(include-book "remove-guard-holders1")
(include-book "remove-guard-holders1-properties")
(include-book "type-set-quote")
(include-book "genvar")
(include-book "sublis-expr")
(include-book "cnf-dnf")
(include-book "all-picks")
(include-book "rewrite-hide")
(include-book "clause-sets")
(include-book "subsumes")
(include-book "add-literal-smart")
(include-book "extra-info-clauses")
(include-book "built-in-clauses")
(include-book "simplify-tests-and-calls")
(include-book "clean-up-conjunction")
(include-book "irrelevance/top")
(include-book "generalize/top")
