; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-evaluation")
(include-book "type-evaluation")
(include-book "primitives-evaluation-on-types")
(include-book "primitives-evaluation-on-ispaces")
(include-book "primitives-evaluation-first-order")
(include-book "expression-evaluation")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ evaluation
  :parents (dynamic-semantics)
  :short "Evaluation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define an interpretive operational semantics of Remora
     in terms of evaluation of ASTs with respect to dynamic environments."))
  :order-subtopics (ispace-evaluation
                    type-evaluation
                    expression-evaluation)
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-top-expr ((expr exprp) (limit natp))
  :returns (val expr-value-resultp)
  :short "Evaluate a standalone (top-level) expression
          to an expression value."
  :long
  (xdoc::topstring
   (xdoc::p
    "We evaluate the expression via @(tsee eval-expr)
     in the initial dynamic environment (see @(tsee init-expr-denv)),
     which contains just the primitive operations in scope.")
   (xdoc::p
    "The @('limit') input bounds the depth of the evaluation recursion,
     as explained in @(see eval-exprs/atoms/binds);
     its exhaustion causes an error result."))
  (eval-expr expr (init-expr-denv) limit)

  ///

  (defret expr-value-wfp-of-eval-top-expr
    (implies (not (reserrp val))
             (expr-value-wfp val))))
