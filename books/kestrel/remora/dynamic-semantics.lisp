; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "values")
(include-book "type-value-equivalence")
(include-book "dynamic-environments")
(include-book "primitives-evaluation")
(include-book "evaluation")

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
     but we will start by providing an executable interpreter."))
  :order-subtopics (values
                    type-value-equivalence
                    dynamic-environments
                    primitives-evaluation
                    evaluation))
