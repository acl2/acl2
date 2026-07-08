; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-values-and-environments")
(include-book "type-values-and-environments")
(include-book "values")
(include-book "type-value-equivalence")
(include-book "dynamic-environments")
(include-book "primitives-evaluation")
(include-book "evaluation")
(include-book "evaluation-rules")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-semantics
  :parents (remora)
  :short "Dynamic semantics of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "The dynamic semantics of Remora is defined via inference rules,
     in the Remora publications [thesis] [arxiv] [esop].
     We plan to formalize those inference rules as directly as possible,
     but we start with an executable interpreter.")
   (xdoc::p
    "[thesis], [arxiv], and [esop],
     in line with much programming language literature,
     define values as subsets of ASTs,
     namely the ones that cannot be further reduced.
     In our interpreter, in contrast,
     we define separate fixtypes for values.
     This separation seems a bit cleaner,
     also given the higher level of detail of our formalization of ASTs
     (compared to the aforementioned publications).
     For instance, base literals in @(tsee base-lit)
     contain syntactic information that is semantically irrelevant.
     We normally think of integer values as mathematical integers,
     not as ASTs with optional signs and sequences of digits
     (although the mapping from the latter to the former
     is fairly straightforward).
     The difference is even more pronounced for floats."))
  :order-subtopics (ispace-values-and-environments
                    type-values-and-environments
                    values
                    type-value-equivalence
                    dynamic-environments
                    primitives-evaluation
                    evaluation
                    evaluation-rules))
