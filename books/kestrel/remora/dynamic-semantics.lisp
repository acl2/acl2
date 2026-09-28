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
(include-book "ispace-evaluation")
(include-book "type-values-and-environments")
(include-book "type-evaluation")
(include-book "expression-values-and-environments")
(include-book "type-value-equivalence")
(include-book "primitives-evaluation-on-types")
(include-book "primitives-evaluation-on-ispaces")
(include-book "primitives-evaluation-first-order")
(include-book "expression-evaluation")
(include-book "evaluation")
(include-book "evaluation-rules")
(include-book "values-to-abstract-syntax")

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
     The difference is even more pronounced for floats.")
   (xdoc::p
    "Along with values,
     we introduce and use dynamic environments,
     which consist of the contextual information needed to execute ASTs.
     They are the dynamic counterpart of "
    (xdoc::seetopic "static-environments" "static environments")
    ". Our dynamic environments have no direct counterpart
     in [thesis], [arxiv], and [esop],
     which use beta reduction rules to substitute variables
     (for expressions, types, and ispaces).
     Our dynamic environments are needed
     to express conveniently an interpretive dynamic semantics;
     they may be also needed or convenient
     for a rule-based small-step operational semantics,
     which we plan to do at some point.
     They may also facilitate expressing and proving type soundness."))
  :order-subtopics (ispace-values-and-environments
                    ispace-evaluation
                    type-values-and-environments
                    type-evaluation
                    expression-values-and-environments
                    type-value-equivalence
                    primitives-evaluation-on-types
                    primitives-evaluation-on-ispaces
                    primitives-evaluation-first-order
                    expression-evaluation
                    evaluation
                    evaluation-rules
                    values-to-abstract-syntax))
