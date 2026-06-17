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

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable int-valuep-when-result-not-error
                          float-valuep-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitives-evaluation
  :parents (dynamic-semantics)
  :short "Evaluation of the Remora primitives."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Remora primitives are built-in functions
     whose definition is not written in Remora.
     Here we provide a definition of them in ACL2,
     as ACL2 functions that take and return Remora expression values.
     The functions defensively check that
     the expression values have the correct types,
     returning an error if they do not;
     the functions also return errors if
     the operation is not well-defined on the type-correct expression values
     (e.g. division by zero).")
   (xdoc::p
    "We will connect these with our formalization of @(see evaluation).
     Most likely, we will extend our ASTs with nodes for the primitives,
     similar to the Remora publications [thesis] [arxiv] [esop],
     and we will extend our evaluator to call the functions defined here
     when evaluating the application of a primitive AST.")
   (xdoc::p
    "The primitives are defined in [impl], as the Remora `prelude'.
     This is work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-value-int ((val expr-valuep))
  :returns (ival int-value-resultp)
  :short "Check if an expression value is an integer value, returning it if so."
  (b* (((unless (expr-value-case val :base)) (reserr nil))
       (bval (expr-value-base->val val))
       ((unless (base-value-case bval :int)) (reserr nil))
       (ival (base-value-int->val bval)))
    ival))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-value-float ((val expr-valuep))
  :returns (fval float-value-resultp)
  :short "Check if an expression value is a float value, returning it if so."
  (b* (((unless (expr-value-case val :base)) (reserr nil))
       (bval (expr-value-base->val val))
       ((unless (base-value-case bval :float)) (reserr nil))
       (fval (base-value-float->val bval)))
    fval))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-int-add ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer addition."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (+ i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

; TODO: add others
