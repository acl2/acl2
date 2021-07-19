; Tests for the Axe toolkit
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "build/ifdef" :dir :system)
(include-book "dag-tests")
(include-book "known-booleans-tests")
(include-book "unroll-spec-basic-tests")
(include-book "def-simplified-tests")
(include-book "check-equivs-tests")
(include-book "get-disjuncts-tests")
(include-book "simplify-xors-tests")
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

(include-book "rewriter-tests")
(include-book "prune-tests")

(ifdef "OS_HAS_STP"
       (include-book "stp-clause-processor-tests")
       (include-book "defthm-stp-tests")
       (include-book "prove-with-stp-tests")
       (include-book "tactic-prover-tests")
       :endif)
