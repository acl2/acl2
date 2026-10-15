; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "expression-validator")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-checker
  :parents (static-semantics)
  :short "A type checker for Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a high-level executable type checker
     that is meant to enforce exactly the inference rules
     that define the static semantics of Remora
     in [thesis] and [arxiv].")
   (xdoc::p
    "This type checker is not designed for efficiency
     or to provide informative error messages.
     It is designed for simplicity.")
   (xdoc::p
    "Besides checking, this type checker performs
     a limited form of type inference:
     when a function with a universal or product type
     is applied to an argument
     without explicit type and ispace applications,
     the type and ispace arguments are inferred from the argument type,
     and the corresponding applications are added to the expression
     (see @(tsee check/infer-app)).
     We plan to extend this inference."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-top-expr ((expr exprp))
  :returns (type+expr type+expr-resultp)
  :short "Check a standalone (top-level) expression,
          returning its type and the expression if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the expression, using the initial static environments.
     We return its type, together with the expression, if successful."))
  (check-expr expr (init-ispace-senv) (init-type-senv) (init-expr-senv)))
