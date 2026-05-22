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
(include-book "integer-list-operations")

(include-book "kestrel/fty/integer-result" :dir :system)
(include-book "kestrel/fty/integer-list-result" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable acl2::integerp-when-result-not-error
                          acl2::integer-listp-when-result-not-error)))

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
  :long
  (xdoc::topstring
   (xdoc::p
    "The evaluation is with respect to a dynamic environment,
     of which we only need the map from ispace variables to ispace values."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-dim ((dim dimp) (denv denvp))
    :returns (int integer-resultp)
    :parents (evaluation eval-dims)
    :short "Evaluate a dimension."
    :long
    (xdoc::topstring
     (xdoc::p
      "If successful, we return an integer.
       The integer may be negative,
       which we allow in intermediate calculations over dimensions,
       but not as top-level dimensions, which must be non-negative.")
     (xdoc::p
      "A variable is looked up in the environment:
       it must be present and have an associated ispace dimension value.
       We plan to introduce a notion of well-formed dynamic environments,
       which will include the fact that ispace dimension variables
       have ispace dimension values associated to them
       (the plain map just associated ispace values to ispace variables);
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
    :short "Evaluate a list of dimensions."
    :long
    (xdoc::topstring
     (xdoc::p
      "If successful, we return a list of integers,
       which are the results of evaluating each dimension in turn."))
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

; TODO: more evaluation functions
