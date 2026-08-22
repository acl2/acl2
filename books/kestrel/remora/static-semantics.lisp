; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "static-environments")
(include-book "ispace-equivalence-checker")
(include-book "type-equivalence-checker")
(include-book "type-checker")
(include-book "ispace-equivalence")
(include-book "ispace-equivalence-derived-rules")
(include-book "ispace-equivalence-normalizations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-semantics
  :parents (remora)
  :short "Static semantics of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "The static semantics of Remora is defined via inference rules,
     in the Remora publications [thesis] [arxiv] [esop].
     While we are woking on formalizing those inference rules,
     we also provide an executable type checker,
     that is meant to be equivalent to those inference rules;
     we plan to prove this equivalence."))
  :order-subtopics (static-environments
                    ispace-equivalence-checker
                    type-equivalence-checker
                    type-checker
                    ispace-equivalence
                    ispace-equivalence-derived-rules
                    ispace-equivalence-properties))
