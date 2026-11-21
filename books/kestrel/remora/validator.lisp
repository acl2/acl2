; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-validator")
(include-book "type-validator")
(include-book "dimension-polynomials")
(include-book "ispace-equivalence-checker")
(include-book "type-equivalence-checker")
(include-book "ispace-matcher")
(include-book "type-matcher")
(include-book "expression-validator")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validator
  :parents (static-semantics)
  :short "A validator for Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a high-level executable validator
     that is meant to enforce exactly the inference rules
     that define the static semantics of Remora.
     This validator is not designed for efficiency
     or to provide informative error messages;
     it is designed for simplicity, at least for now.")
   (xdoc::p
    "In typical programming language terminology,
     this validator performs type checking,
     but also a limited form of type inference.
     We plan to extend the power of this type inference."))
  :order-subtopics (ispace-validator
                    type-validator
                    dimension-polynomials
                    ispace-equivalence-checker
                    type-equivalence-checker
                    ispace-matcher
                    type-matcher
                    expression-validator
                    t)
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
