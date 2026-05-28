; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "dynamic-environments")
(include-book "nat-list-operations")
(include-book "integer-list-operations")

(include-book "kestrel/fty/integer-result" :dir :system)
(include-book "kestrel/fty/integer-list-result" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable acl2::integerp-when-result-not-error
                          acl2::integer-listp-when-result-not-error
                          acl2::nat-listp-when-result-not-error
                          acl2::nat-list-listp-when-result-not-error
                          ispace-valuep-when-result-not-error
                          ispace-value-listp-when-result-not-error
                          type-valuep-when-result-not-error
                          type-value-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ evaluation
  :parents (dynamic-semantics)
  :short "Evaluation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define an interpretive operational semantics of Remora
     in terms of evaluation of ASTs with respect to dynamic environments."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines eval-dims
  :short "Evaluate dimensions and lists of dimensions."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-dim ((dim dimp) (denv denvp))
    :returns (int integer-resultp)
    :parents (evaluation eval-dims)
    :short "Evaluate a dimension to an integer."
    :long
    (xdoc::topstring
     (xdoc::p
      "The integer result may be negative,
       which we allow in intermediate calculations over dimensions,
       but not as top-level dimensions, which must be non-negative.")
     (xdoc::p
      "A variable is looked up in the environment:
       it must be present and have an associated ispace dimension value.
       We plan to introduce a notion of well-formed dynamic environments,
       which will include the fact that ispace dimension variables
       have ispace dimension values associated to them
       (the plain map just associates ispace values to ispace variables);
       we plan to use well-formedness as a guard of this function,
       which will obviate the need for that check on the ispace value.")
     (xdoc::p
      "A constant evaluates to itself.")
     (xdoc::p
      "For arithmetic expressions, first we evaluate the operands,
       then we combine the integers according to the operation.
       This is obvious for addition and multiplication,
       where the result is 0 or 1 if there are no operands.
       For subtraction, Remora follows Common Lisp:
       there must be at least one operand;
       if there is one operand, it is negated;
       if there are two or more operands,
       we subtract all the ones after the first from the first."))
    (dim-case
     dim
     :var (b* ((var+val (omap::assoc (ispace-var-dim dim.name)
                                     (denv->ispace-vars denv)))
               ((unless var+val) (reserr nil))
               (val (cdr var+val))
               ((unless (ispace-value-case val :dim)) (reserr nil)))
            (ispace-value-dim->val val))
     :const dim.val
     :add (b* (((ok ints) (eval-dim-list dim.dims denv)))
            (integer-list-sum ints))
     :mul (b* (((ok ints) (eval-dim-list dim.dims denv)))
            (integer-list-product ints))
     :sub (b* (((ok ints) (eval-dim-list dim.dims denv))
               ((unless (consp ints)) (reserr nil))
               (sub (integer-list-subtraction ints)))
            sub))
    :measure (dim-count dim))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-dim-list ((dims dim-listp) (denv denvp))
    :returns (ints integer-list-resultp)
    :parents (evaluation eval-dims)
    :short "Evaluate a list of dimensions to a list of integers."
    :long
    (xdoc::topstring
     (xdoc::p
      "We evaluate each dimension in turn
       and return the list of results in the same order."))
    (b* (((when (endp dims)) nil)
         ((ok int) (eval-dim (car dims) denv))
         ((ok ints) (eval-dim-list (cdr dims) denv)))
      (cons int ints))
    :measure (dim-list-count dims))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual eval-dims))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines eval-shapes
  :short "Evaluate shapes and lists of shapes."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-shape ((shape shapep) (denv denvp))
    :returns (nats nat-list-resultp)
    :parents (evaluation eval-shapes)
    :short "Evaluate a shape to a list of naturals."
    :long
    (xdoc::topstring
     (xdoc::p
      "The resulting naturals are the dimensions that form the shape.")
     (xdoc::p
      "A variable is looked up in the environment:
       it must be present and have an associated ispace shape value.
       We plan to introduce a notion of well-formed dynamic environments,
       which will include the fact that ispace shape variables
       have ispace shape values associated to them
       (the plain map just associates ispace values to ispace variables);
       we plan to use well-formedness as a guard of this function,
       which will obviate the need for that check on the ispace value.")
     (xdoc::p
      "For a shape consisting of a single dimension,
       we evaluate the dimension,
       we ensure it is non-negative,
       and we return a singleton list with it.")
     (xdoc::p
      "For a shape consisting of a list of dimensions,
       we evaluate the dimensions,
       we ensure that they are non-negative,
       and we return their list.")
     (xdoc::p
      "For a concatenation,
       we recursively evaluate the sub-shapes,
       obtaining a list of lists of naturals,
       and then we concatenate all the lists.")
     (xdoc::p
      "A splice is treated the same as a concatenation,
       since the two constructs are in fact equivalent."))
    (shape-case
     shape
     :var (b* ((var+val (omap::assoc (ispace-var-shape shape.name)
                                     (denv->ispace-vars denv)))
               ((unless var+val) (reserr nil))
               (val (cdr var+val))
               ((unless (ispace-value-case val :shape)) (reserr nil)))
            (ispace-value-shape->val val))
     :dim (b* (((ok int) (eval-dim shape.dim denv))
               ((unless (natp int)) (reserr nil)))
            (list int))
     :dims (b* (((ok ints) (eval-dim-list shape.dims denv))
                ((unless (nat-listp ints)) (reserr nil)))
             ints)
     :append (b* (((ok natss) (eval-shape-list shape.shapes denv)))
               (nat-append-all natss))
     :splice (b* (((ok natss) (eval-shape-list shape.shapes denv)))
               (nat-append-all natss)))
    :measure (shape-count shape))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-shape-list ((shapes shape-listp) (denv denvp))
    :returns (natss nat-list-list-resultp)
    :parents (evaluation eval-shapes)
    :short "Evaluate a list of shapes to a list of lists of naturals."
    :long
    (xdoc::topstring
     (xdoc::p
      "We evaluate each shape in turn
       and return the list of results in the same order."))
    (b* (((when (endp shapes)) nil)
         ((ok nats) (eval-shape (car shapes) denv))
         ((ok natss) (eval-shape-list (cdr shapes) denv)))
      (cons nats natss))
    :measure (shape-list-count shapes))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual eval-shapes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-ispace ((ispace ispacep) (denv denvp))
  :returns (ival ispace-value-resultp)
  :short "Evaluate an ispace to an ispace value."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a dimension, we ensure that the integer is non-negative,
     and we embed it into an ispace value.")
   (xdoc::p
    "For a shape, we embed the list of naturals into an ispace value."))
  (ispace-case
   ispace
   :dim (b* (((ok int) (eval-dim ispace.dim denv))
             ((unless (natp int)) (reserr nil)))
          (ispace-value-dim int))
   :shape (b* (((ok nats) (eval-shape ispace.shape denv)))
            (ispace-value-shape nats))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-ispace-list ((ispaces ispace-listp) (denv denvp))
  :returns (ivals ispace-value-list-resultp)
  :short "Evaluate a list of ispaces to a list of ispace values."
  (b* (((when (endp ispaces)) nil)
       ((ok ival) (eval-ispace (car ispaces) denv))
       ((ok ivals) (eval-ispace-list (cdr ispaces) denv)))
    (cons ival ivals)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines eval-types
  :short "Evaluate types and lists of types."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-type ((type typep) (denv denvp))
    :returns (tval type-value-resultp)
    :parents (evaluation eval-types)
    :short "Evaluate a type to a type value."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the environment.")
     (xdoc::p
      "A base type evaluates to itself.")
     (xdoc::p
      "For an array type,
       we evaluate the element type and the shape,
       and put the results together into an array type value.")
     (xdoc::p
      "A bracket type is treated similarly to an array type,
       but instead of a shape we have a list of shapes,
       and we concatenate all the naturals.")
     (xdoc::p
      "For a function type, we evaluate input and output types,
       and put the resulting type values together into a function type value.")
     (xdoc::p
      "Universal, product, and sum types evaluate to themselves.
       They are treated like lambda abstractions."))
    (type-case
     type
     :var (b* ((var+val (omap::assoc type.var (denv->type-vars denv)))
               ((unless var+val) (reserr nil)))
            (cdr var+val))
     :base (type-value-base type.type)
     :array (b* (((ok elem-tval) (eval-type type.elem denv))
                 ((ok nats) (eval-shape type.shape denv)))
              (make-type-value-array :elem elem-tval :shape nats))
     :bracket (b* (((ok elem-tval) (eval-type type.elem denv))
                   ((ok natss) (eval-shape-list type.shapes denv))
                   (nats (nat-append-all natss)))
                (make-type-value-array :elem elem-tval :shape nats))
     :fun (b* (((ok in-tvals) (eval-type-list type.in denv))
               ((ok out-tval) (eval-type type.out denv)))
            (make-type-value-fun :in in-tvals :out out-tval))
     :forall (make-type-value-forall :params type.params :body type.body)
     :pi (make-type-value-pi :params type.params :body type.body)
     :sigma (make-type-value-sigma :params type.params :body type.body))
    :measure (type-count type))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-type-list ((types type-listp) (denv denvp))
    :returns (tvals type-value-list-resultp)
    :parents (evaluation eval-types)
    :short "Evaluate a list of types to a list of type values."
    :long
    (xdoc::topstring
     (xdoc::p
      "We evaluate each type in turn
       and return the list of results in the same order."))
    (b* (((when (endp types)) nil)
         ((ok tval) (eval-type (car types) denv))
         ((ok tvals) (eval-type-list (cdr types) denv)))
      (cons tval tvals))
    :measure (type-list-count types))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual eval-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: eval-expr & eval-atom
