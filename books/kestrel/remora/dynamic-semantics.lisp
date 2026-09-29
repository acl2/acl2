; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "values-and-environments")
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
     but we start with an executable interpreter."))
  :order-subtopics (values-and-environments
                    evaluation
                    evaluation-rules
                    values-to-abstract-syntax))
