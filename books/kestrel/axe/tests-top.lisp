; Tests for the Axe toolkit
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We don't actually need to include the tests together here, so we put the
;; includes in a comment, but the dependency scanner should still find them:
#|
(include-book "dag-tests")
(include-book "dag-size-sparse-tests")
(include-book "known-booleans-tests")
(include-book "unroll-spec-basic-tests")
(include-book "def-simplified-tests")
(include-book "check-equivs-tests")
(include-book "get-disjuncts-tests")
(include-book "normalize-xors-tests")
(include-book "defthm-axe-basic-tests")
(include-book "make-axe-rules-tests")
(include-book "make-evaluator-simple-tests")
(include-book "prover-basic-tests")
(include-book "rewriter-basic-tests")
(include-book "make-axe-syntaxp-evaluator-tests")
(include-book "make-evaluator-tests")
(include-book "evaluator-tests")
(include-book "make-term-into-dag-basic-tests")
(include-book "prune-with-contexts-tests")
(include-book "unroller-tests")
(include-book "pure-dags-tests")

(include-book "rewriter-tests")
(include-book "rewriter-alt-tests")
(include-book "prune-term-tests")
(include-book "unroll-spec-tests")

(include-book "query-tests")

(include-book "utilities-tests")
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "build/ifdef" :dir :system)

(ifdef "OS_HAS_STP"
       (include-book "stp-clause-processor-tests")
       (include-book "defthm-stp-tests")
       (include-book "prove-with-stp-tests")
       (include-book "tactic-prover-tests")
       :endif)
