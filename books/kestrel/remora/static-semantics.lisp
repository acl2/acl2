; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-validity")
(include-book "ispace-validity-derived-rules")
(include-book "ispace-equivalence")
(include-book "ispace-equivalence-derived-rules")
(include-book "ispace-equivalence-normalizations")
(include-book "ispace-equivalence-rewriting")
(include-book "shape-ordering")
(include-book "type-validity")
(include-book "type-equivalence")
(include-book "type-equivalence-derived-rules")
(include-book "type-equivalence-normalizations")
(include-book "expression-validity")
(include-book "static-environments")
(include-book "validator")
(include-book "ispace-validator-correctness")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-semantics
  :parents (remora)
  :short "Static semantics of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "The static semantics of Remora is defined via inference rules,
     in the Remora publications [thesis] [arxiv] [esop].
     While we are working on formalizing those inference rules,
     we also provide an executable validator,
     that is meant to be equivalent to those inference rules;
     we plan to prove this equivalence."))
  :order-subtopics (ispace-validity
                    ispace-validity-derived-rules
                    ispace-equivalence
                    ispace-equivalence-derived-rules
                    ispace-equivalence-normalizations
                    ispace-equivalence-rewriting
                    shape-ordering
                    type-validity
                    type-equivalence
                    type-equivalence-derived-rules
                    type-equivalence-normalizations
                    expression-validity
                    static-environments
                    validator
                    ispace-validator-correctness))
