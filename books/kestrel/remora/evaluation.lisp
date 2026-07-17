; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "bound-and-free-variable-operations")
(include-book "expression-values-and-environments")
(include-book "primitives-evaluation")
(include-book "nat-lists")
(include-book "integer-lists")
(include-book "character-literal-codes")

(include-book "kestrel/fty/integer-result" :dir :system)
(include-book "kestrel/fty/integer-list-result" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

(local (include-book "lists"))

(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable acl2::integerp-when-result-not-error
                          acl2::integer-listp-when-result-not-error
                          acl2::nat-listp-when-result-not-error
                          acl2::nat-list-listp-when-result-not-error
                          ispace-valuep-when-result-not-error
                          ispace-value-listp-when-result-not-error
                          type-valuep-when-result-not-error
                          type-value-listp-when-result-not-error
                          expr-valuep-when-result-not-error
                          expr-value-listp-when-result-not-error
                          expr-value-list-listp-when-result-not-error
                          var+typevalue-p-when-result-not-error
                          var+typevalue-listp-when-result-not-error
                          typep-when-result-not-error
                          type-listp-when-result-not-error
                          expr-denvp-when-result-not-error)))

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

  (define eval-dim ((dim dimp) (denv ispace-denvp))
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
     :var (b* (((ok val)
                (ispace-denv-lookup-ispace (ispace-var-dim dim.name) denv))
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

  (define eval-dim-list ((dims dim-listp) (denv ispace-denvp))
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

  :flag-local nil

  ///

  (fty::deffixequiv-mutual eval-dims))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define splice-ispace-values ((ivals ispace-value-listp))
  :returns (dims nat-listp)
  :short "Splice zero or more ispace values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We concatenate all the dimensions,
     returning the resulting list of dimensions.
     This is used to evaluate splice shapes."))
  (cond ((endp ivals) nil)
        (t (append (ispace-value-to-dims (car ivals))
                   (splice-ispace-values (cdr ivals))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines eval-shapes/ispaces
  :short "Evaluate shapes and ispaces."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-shape ((shape shapep) (denv ispace-denvp))
    :returns (nats nat-list-resultp)
    :parents (evaluation eval-shapes/ispaces)
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
     :var (b* (((ok val)
                (ispace-denv-lookup-ispace (ispace-var-shape shape.name) denv))
               ((unless (ispace-value-case val :shape)) (reserr nil)))
            (ispace-value-shape->val val))
     :dims (b* (((ok ints) (eval-dim-list shape.dims denv))
                ((unless (nat-listp ints)) (reserr nil)))
             ints)
     :append (b* (((ok natss) (eval-shape-list shape.shapes denv)))
               (append-all natss))
     :splice (b* (((ok ivals) (eval-ispace-list shape.ispaces denv)))
               (splice-ispace-values ivals)))
    :measure (shape-count shape))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-shape-list ((shapes shape-listp) (denv ispace-denvp))
    :returns (natss nat-list-list-resultp)
    :parents (evaluation eval-shapes/ispaces)
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

  (define eval-ispace ((ispace ispacep) (denv ispace-denvp))
    :returns (ival ispace-value-resultp)
    :parents (evaluation eval-shapes/ispaces)
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
              (ispace-value-shape nats)))
    :measure (ispace-count ispace))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-ispace-list ((ispaces ispace-listp) (denv ispace-denvp))
    :returns (ivals ispace-value-list-resultp)
    :parents (evaluation eval-shapes/ispaces)
    :short "Evaluate a list of ispaces to a list of ispace values."
    (b* (((when (endp ispaces)) nil)
         ((ok ival) (eval-ispace (car ispaces) denv))
         ((ok ivals) (eval-ispace-list (cdr ispaces) denv)))
      (cons ival ivals))
    :measure (ispace-list-count ispaces))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  :flag-local nil

  :guard-hints
  (("Goal" :in-theory (enable acl2::true-list-listp-when-nat-list-listp)))

  ///

  (fty::deffixequiv-mutual eval-shapes/ispaces))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines eval-types
  :short "Evaluate types and lists of types."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-type ((type typep) (denv type-denvp))
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
       They are treated like lambda abstractions.
       The resulting type values include dynamic environments
       with the bindings for
       the free ispace and type variables of these types,
       obtained by restricting the current dynamic environment
       to those variables."))
    (type-case
     type
     :var (type-denv-lookup-type type.var denv)
     :base (type-value-base type.type)
     :array (b* (((ok elem-tval) (eval-type type.elem denv))
                 ((ok ival) (eval-ispace type.ispace (type-denv->ienv denv)))
                 (dims (ispace-value-to-dims ival)))
              (make-type-value-array :elem elem-tval :dims dims))
     :bracket (b* (((ok elem-tval) (eval-type type.elem denv))
                   ((ok ivals) (eval-ispace-list type.ispaces
                                                 (type-denv->ienv denv)))
                   (natss (ispace-value-list-to-dims ivals))
                   (nats (append-all natss)))
                (make-type-value-array :elem elem-tval :dims nats))
     :fun (b* (((ok in-tvals) (eval-type-list type.in denv))
               ((ok out-tval) (eval-type type.out denv)))
            (make-type-value-fun :in in-tvals :out out-tval))
     :forall (b* (((unless (consp type.params)) (reserr nil)))
               (make-type-value-forall
                :param (car type.params)
                :body (forall-curried-body type.params type.body)
                :denv (type-denv-restrict (type-free-ispace-vars type)
                                          (type-free-type-vars type)
                                          denv)))
     :pi (make-type-value-pi
          :param type.param
          :body type.body
          :denv (type-denv-restrict (type-free-ispace-vars type)
                                    (type-free-type-vars type)
                                    denv))
     :pin (b* (((unless (consp type.params)) (reserr nil)))
            (make-type-value-pi
             :param (car type.params)
             :body (pi-curried-body type.params type.body)
             :denv (type-denv-restrict (type-free-ispace-vars type)
                                       (type-free-type-vars type)
                                       denv)))
     :sigma (make-type-value-sigma
             :params type.params
             :body type.body
             :denv (type-denv-restrict (type-free-ispace-vars type)
                                       (type-free-type-vars type)
                                       denv)))
    :measure (type-count type))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-type-list ((types type-listp) (denv type-denvp))
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
    :measure (type-list-count types)

    ///

    (defret len-of-eval-type-list
      (implies (not (reserrp tvals))
               (equal (len tvals)
                      (len types)))
      :hints (("Goal"
               :induct (len types)
               :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  :flag-local nil

  :guard-hints
  (("Goal" :in-theory (enable acl2::true-list-listp-when-nat-list-listp)))

  ///

  (fty::deffixequiv-mutual eval-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-var+type? ((var+type? var+type?-p) (denv type-denvp))
  :returns (var+tval var+typevalue-resultp)
  :short "Evaluate a variable with an optional type
          to a variable with a type value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is unchanged;
     its associated type must be present, and is evaluated to a type value."))
  (b* (((ok type) (var+type?->type-or-err var+type?))
       ((ok tval) (eval-type type denv)))
    (make-var+typevalue :var (var+type?->var var+type?) :type tval)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-var+type?-list ((var+types var+type?-listp) (denv type-denvp))
  :returns (var+tvals var+typevalue-list-resultp)
  :short "Evaluate a list of variables with optional types
          to a list of variables with type values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We evaluate each element in turn
     and return the list of results in the same order."))
  (b* (((when (endp var+types)) nil)
       ((ok var+tval) (eval-var+type? (car var+types) denv))
       ((ok var+tvals) (eval-var+type?-list (cdr var+types) denv)))
    (cons var+tval var+tvals))

  ///

  (defret len-of-eval-var+type?-list
    (implies (not (reserrp var+tvals))
             (equal (len var+tvals)
                    (len var+types)))
    :hints (("Goal"
             :induct (len var+types)
             :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-int-lit ((lit int-litp))
  :returns (val int-valuep)
  :short "Evaluate an integer literal to an integer value."
  :long
  (xdoc::topstring
   (xdoc::p
    "We evaluate the digits to a natural,
     we apply the sign if present,
     and we embed the integer into an integer value.")
   (xdoc::p
    "This never fails, because we assume unbounded integers."))
  (b* (((int-lit lit))
       (digits-val (str::dec-digit-chars-value lit.digits))
       (signed-val (sign-option-case
                    lit.sign?
                    :some (sign-case
                           lit.sign?.val
                           :plus digits-val
                           :minus (- digits-val))
                    :none digits-val)))
    (int-value signed-val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-expo ((expo expop))
  :returns (val integerp)
  :short "Evaluate an exponent to an integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "We evaluate the digits to a natural
     and we apply the sign if present.")
   (xdoc::p
    "This is used as part of the evaluation of float literals."))
  (b* (((expo expo))
       (digits-val (str::dec-digit-chars-value expo.digits)))
    (sign-option-case
     expo.sign?
     :some (sign-case
            expo.sign?.val
            :plus digits-val
            :minus (- digits-val))
     :none digits-val))
  :type-prescription (integerp (eval-expo expo)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-float-lit ((lit float-litp))
  :returns (val float-valuep)
  :short "Evaluate a float literal to a float value."
  :long
  (xdoc::topstring
   (xdoc::p
    "First we calculate the significand.
     We evaluate the digits of the whole and fractional parts to two integers.
     If the second integer is 0, the significand is the first integer,
     i.e. just the whole part.
     Otherwise, we divide the fractional integer by @($10^n$),
     where @($n$) is the number of fractional digits,
     and we add the whole integer to that,
     obtaining the significand.")
   (xdoc::p
    "Then we calculate the magnitude.
     If there is no exponent, the magnitude is the significand.
     Otherwise, we evaluate the exponent,
     and we multiply the significand by @($10^e$),
     where @($e$) is the value of the exponent.")
   (xdoc::p
    "Finally we apply the sign if present,
     and we embed the rational into a float value.")
   (xdoc::p
    "This never fails, because our current simple model of float values
     includes all the rationals."))
  (b* (((float-lit lit))
       (whole-val (str::dec-digit-chars-value lit.whole-digits))
       (frac-int (str::dec-digit-chars-value lit.frac-digits))
       (frac-val (if (= frac-int 0)
                     0
                   (/ frac-int (expt 10 (len lit.frac-digits)))))
       (signif-val (+ whole-val frac-val))
       (exp-val (expo-option-case
                 lit.expo?
                 :some (b* ((expo-val (eval-expo lit.expo?.val)))
                         (expt 10 expo-val))
                 :none 1))
       (magnit-val (* signif-val exp-val))
       (signed-val (sign-option-case
                    lit.sign?
                    :some (sign-case
                           lit.sign?.val
                           :plus magnit-val
                           :minus (- magnit-val))
                    :none magnit-val)))
    (float-value-ratio signed-val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-base-lit ((lit base-litp))
  :returns (val base-valuep)
  :short "Evaluate a base literal to a base value."
  :long
  (xdoc::topstring
   (xdoc::p
    "Boolean literals evaluate to themselves.")
   (xdoc::p
    "Integer and float literals are evaluated via separate functions."))
  (base-lit-case
   lit
   :bool (base-value-bool lit.lit)
   :int (base-value-int (eval-int-lit lit.lit))
   :float (base-value-float (eval-float-lit lit.lit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-char-lit ((clit char-litp))
  :returns (val int-valuep)
  :short "Evaluate a character literal to an integer value."
  :long
  (xdoc::topstring
   (xdoc::p
    "A character is represented as the integer value of its code.
     This is used to evaluate strings,
     which are sugar for arrays of such integers."))
  (int-value (char-lit-code clit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection eval-char-lit-list ((x char-lit-listp))
  :returns (vals int-value-listp)
  :short "Lift @(tsee eval-char-lit) to lists."
  (eval-char-lit x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-value-with-empty-dim ((dims nat-listp) (elem type-valuep))
  :guard (and (member-equal 0 dims)
              (not (type-value-case elem :array)))
  :returns (val expr-valuep)
  :short "Build a vector value with an empty dimension."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to evaluate empty array or frame expressions,
     which must have at least one zero dimension
     and an atom (i.e. non-array) type value for elements,
     as expressed by the guard.
     In the case of empty frame expressions,
     the type value passed to this function is not
     the result of evaluating the type in the frame expression,
     which may be an array type:
     it is the atom type value of that array type,
     whose dimensions are added to the ones in frame expression
     before calling this function (see callers).")
   (xdoc::p
    "We look at the first dimension,
     which must be present because otherwise 0 could not be in the list.
     If that dimension is 0, we return the empty vector
     with the remaining dimensions and the element type.
     If that dimension is not 0,
     we recursively build a vector value
     for the remaining dimensions (which must still include a 0)
     and the element type,
     and we replicate the value as many times as the first dimension,
     to obtain the final vector value.")
   (xdoc::p
    "A key property is that the resulting expression value is well-formed
     and has exactly the dimensions passed as input."))
  (b* (((when (not (mbt (consp dims)))) (expr-value-vector-empty nil elem))
       (dim (lnfix (car dims))))
    (if (= dim 0)
        (make-expr-value-vector-empty :dims (cdr dims) :elem elem)
      (expr-value-vector
       (repeat dim (expr-value-with-empty-dim (cdr dims) elem)))))
  :verify-guards :after-returns

  ///

  (defret check-dims-of-expr-value-of-expr-value-with-empty-dim
    (b* ((dims1 (check-dims-of-expr-value val)))
      (and (not (reserrp dims1))
           (equal dims1 (nat-list-fix dims))))
    :hyp (member-equal 0 dims)
    :hints (("Goal"
             :induct t
             :in-theory (enable check-dims-of-expr-value
                                check-dims-of-expr-value-list-of-repeat
                                acl2::not-reserrp-when-nat-listp
                                acl2::not-reserrp-when-nat-list-listp
                                car-of-repeat
                                nfix))))

  (defret expr-value-wfp-of-expr-value-with-empty-dim
    (expr-value-wfp val)
    :hyp (member-equal 0 dims)
    :hints (("Goal" :in-theory (enable expr-value-wfp
                                       acl2::not-reserrp-when-nat-listp))))

  (defret dims-of-expr-value-of-expr-value-with-empty-dim
    (equal (dims-of-expr-value val)
           (nat-list-fix dims))
    :hyp (member-equal 0 dims)
    :hints (("Goal" :in-theory (enable dims-of-expr-value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expr-values-with-nonempty-dims
  :short "Build expression values with non-empty dimensions and with given elements."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define expr-value-with-nonempty-dims ((dims nat-listp) (vals expr-value-listp))
    :guard (and (not (member-equal 0 dims))
                (equal (len vals) (nat-list-product dims))
                (expr-value-list-wfp vals)
                (list-repeatp (dims-of-expr-value-list vals)))
    :returns (val expr-valuep)
    :parents (evaluation expr-values-with-nonempty-dims)
    :short "Build an expression value
            from its dimensions and
            from the expression values of its elements."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is used to evaluate non-empty array or frame expressions,
       which have all non-zero dimensions as required by the guard.
       The number of expression values must match the product of the dimensions,
       as required by the guard,
       so that the expression values can be arranged according to the dimensions.
       Furthermore, as also required by the guard,
       all expression values must be well-formed and have the same dimensions.")
     (xdoc::p
      "When there are no dimensions left in the list,
       the list of expression values must be a singleton
       because its length must match the product of dimensions,
       which is 1 for the empty list of dimensions.
       Otherwise, we take out the first dimension,
       and we split the list of expression values
       into as many chunks as that dimension
       (which is not 0 as enforced by the guard),
       where each chunk has as its size the (integer) ratio of
       the total number of expression values and the first dimension.
       We construct expression values for each chunk
       via the companion recursive function.
       We put these expression values together into a vector value,
       which is the final result.")
     (xdoc::p
      "A key property is that the resulting expression value is well-formed
       and has exactly the concatenation of
       the dimensions passed as input
       and the common dimensions of the component expression values."))
    (b* (((when (endp dims)) (expr-value-fix (car vals)))
         (dim (lnfix (car dims)))
         (valss (list-split (expr-value-list-fix vals) (/ (len vals) dim)))
         (vals (expr-value-list-with-nonempty-dims (cdr dims) valss)))
      (expr-value-vector vals))
    :measure (acl2::nat-list-measure (list (len dims) 0 0)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define expr-value-list-with-nonempty-dims ((dims nat-listp)
                                              (valss expr-value-list-listp))
    :guard (and (not (member-equal 0 dims))
                (all-of-len-p valss (nat-list-product dims))
                (expr-value-list-list-wfp valss)
                (list-repeatp (dims-of-expr-value-list-list valss))
                (list-list-repeatp (dims-of-expr-value-list-list valss)))
    :returns (vals expr-value-listp)
    :parents (evaluation expr-values-with-nonempty-dims)
    :short "Build a list of expression values from a common list of dimensions
            and a list of lists of component expression values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This lifts @(tsee expr-value-with-nonempty-dims)
       to lists of lists of expression values.
       See the documentation of that function.")
     (xdoc::p
      "The guard requires the same dimensions of
       all the expression values in the list of lists of expression values:
       this is expressed via @(tsee list-list-repeatp),
       which says that each list of expression values has the same dimensions,
       and via @(tsee list-repeatp),
       which additionally requires the equality of
       the lists of lists of dimensions corresponding to
       the lists of expression values.")
     (xdoc::p
      "The key property mentioned in @(tsee expr-value-with-nonempty-dims)
       is proved by induction simultaneously with
       a corresponding property for this function.
       This corresponding property is lifted to lists:
       the list of lists of dimensions of
       the resulting list of expression values
       is a repetition of the same list of dimensions,
       which consists of the dimensions passed as input
       concatenated with the common dimensions of all the expression values
       (we extract the latter via @(tsee car) of @(tsee car)."))
    (cond ((endp valss) nil)
          (t (cons (expr-value-with-nonempty-dims dims (car valss))
                   (expr-value-list-with-nonempty-dims dims (cdr valss)))))
    :measure (acl2::nat-list-measure (list (len dims) 1 (len valss)))

    ///

    (defret len-of-expr-value-list-with-nonempty-dims
      (equal (len vals)
             (len valss))
      :hints (("Goal"
               :induct (len valss)
               :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))

  :guard-hints (("Goal"
                 :in-theory (e/d
                             (true-list-listp-when-expr-value-list-listp
                              acl2::true-list-listp-when-nat-list-listp
                              acl2::true-list-listp-when-nat-list-list-listp
                              nat-list-product-of-cdr-to-ratio
                              posp
                              dims-of-expr-value-list-list-of-cdr)
                             (cdr-of-dims-of-expr-value-list-list))
                 :use nat-list-product-divided-by-car))

  :flag-local nil

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual expr-values-with-nonempty-dims)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruledl lemma1
    (implies (and (nat-listp dims)
                  (not (member-equal 0 dims))
                  (consp dims)
                  (equal (len vals) (nat-list-product dims)))
             (posp (* (/ (car dims)) (len vals))))
    :enable posp
    :use nat-list-product-divided-by-car)

  (defruledl lemma2
    (implies (and (expr-value-listp vals)
                  (nat-listp dims)
                  (not (member-equal 0 dims))
                  (consp dims)
                  (equal (len vals) (nat-list-product dims)))
             (expr-value-list-listp
              (list-split vals (* (/ (car dims)) (len vals)))))
    :enable posp
    :disable expr-value-list-listp-of-list-split
    :use (nat-list-product-divided-by-car
          (:instance expr-value-list-listp-of-list-split
                     (n (/ (len vals) (car dims))))))

  (defret-mutual check-dims-of-expr-values-with-nonempty-dims
    (defret check-dims-of-expr-value-with-nonempty-dims
      (b* ((dims1 (check-dims-of-expr-value val)))
        (and (not (reserrp dims1))
             (equal dims1
                    (append (nat-list-fix dims)
                            (car (dims-of-expr-value-list vals))))))
      :hyp (and (nat-listp dims)
                (expr-value-listp vals)
                (not (member-equal 0 dims))
                (equal (len vals) (nat-list-product dims))
                (expr-value-list-wfp vals)
                (list-repeatp (dims-of-expr-value-list vals)))
      :fn expr-value-with-nonempty-dims)
    (defret check-dims-of-expr-value-list-with-nonempty-dims
      (b* ((dimss (check-dims-of-expr-value-list vals)))
        (and (not (reserrp dimss))
             (equal dimss
                    (repeat (len valss)
                            (append (nat-list-fix dims)
                                    (car (car (dims-of-expr-value-list-list
                                               valss))))))))
      :hyp (and (nat-listp dims)
                (expr-value-list-listp valss)
                (not (member-equal 0 dims))
                (all-of-len-p valss (nat-list-product dims))
                (expr-value-list-list-wfp valss)
                (list-repeatp (dims-of-expr-value-list-list valss))
                (list-list-repeatp (dims-of-expr-value-list-list valss)))
      :fn expr-value-list-with-nonempty-dims)
    :mutual-recursion expr-values-with-nonempty-dims
    :hints (("Goal"
             :in-theory (enable expr-value-with-nonempty-dims
                                expr-value-list-with-nonempty-dims
                                check-dims-of-expr-value
                                check-dims-of-expr-value-list
                                acl2::not-reserrp-when-nat-listp
                                acl2::not-reserrp-when-nat-list-listp
                                expr-value-wfp
                                dims-of-expr-value
                                dims-of-expr-value-list-list
                                nat-list-product-of-cdr-to-ratio
                                list-repeatp
                                repeat
                                car-of-repeat
                                car-of-car-of-list-split
                                lemma1
                                lemma2))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret expr-value-wfp-of-expr-value-with-nonempty-dims
    (expr-value-wfp val)
    :hyp (and (nat-listp dims)
              (expr-value-listp vals)
              (not (member-equal 0 dims))
              (equal (len vals) (nat-list-product dims))
              (expr-value-list-wfp vals)
              (list-repeatp (dims-of-expr-value-list vals)))
    :fn expr-value-with-nonempty-dims
    :hints (("Goal" :in-theory (enable expr-value-wfp
                                       acl2::not-reserrp-when-nat-listp))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret expr-value-list-wfp-of-expr-value-list-with-nonempty-dims
    (expr-value-list-wfp vals)
    :hyp (and (nat-listp dims)
              (expr-value-list-listp valss)
              (not (member-equal 0 dims))
              (all-of-len-p valss (nat-list-product dims))
              (expr-value-list-list-wfp valss)
              (list-repeatp (dims-of-expr-value-list-list valss))
              (list-list-repeatp (dims-of-expr-value-list-list valss)))
    :fn expr-value-list-with-nonempty-dims
    :hints (("Goal" :in-theory (enable expr-value-list-wfp-alt-def
                                       acl2::not-reserrp-when-nat-list-listp))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret dims-of-expr-value-of-expr-value-with-nonempty-dims
    (equal (dims-of-expr-value val)
           (append (nat-list-fix dims)
                   (car (dims-of-expr-value-list vals))))
    :hyp (and (nat-listp dims)
              (expr-value-listp vals)
              (not (member-equal 0 dims))
              (equal (len vals) (nat-list-product dims))
              (expr-value-list-wfp vals)
              (list-repeatp (dims-of-expr-value-list vals)))
    :fn expr-value-with-nonempty-dims
    :hints (("Goal" :in-theory (enable dims-of-expr-value))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret dims-of-expr-value-list-of-expr-value-list-with-nonempty-dims
    (equal (dims-of-expr-value-list vals)
           (repeat (len valss)
                   (append (nat-list-fix dims)
                           (car (car (dims-of-expr-value-list-list valss))))))
    :hyp (and (nat-listp dims)
              (expr-value-list-listp valss)
              (not (member-equal 0 dims))
              (all-of-len-p valss (nat-list-product dims))
              (expr-value-list-list-wfp valss)
              (list-repeatp (dims-of-expr-value-list-list valss))
              (list-list-repeatp (dims-of-expr-value-list-list valss)))
    :fn expr-value-list-with-nonempty-dims
    :hints (("Goal"
             :use (:instance
                   dims-of-expr-value-list-when-expr-value-list-wfp
                   (vals (expr-value-list-with-nonempty-dims dims valss)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-expr-value-to-frame ((val expr-valuep)
                                  (frame nat-listp)
                                  (pframe nat-listp))
  :guard (prefixp frame pframe)
  :returns (cells expr-value-list-resultp)
  :short "Lift an expression value to a principal frame,
          returning its cells in row-major order."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is part of lifting for Remora function application.
     The @('frame') input of this ACL2 function corresponds to
     @($n_f\\ldots$) and @($n_a\\ldots$) in [thesis],
     which is the full shape in the case of the function,
     while it is in general a prefix of the shape in the case of an argument
     (whose shapes are @($n_a\\ldots n_i\\ldots$) in [thesis]).
     The @('pframe') input of this ACL2 function corresponds to
     @($n_p\\ldots$) in [thesis], i.e. the principal frame,
     of which @('frame') is a prefix, as expressed in the guard.")
   (xdoc::p
    "This ACL2 function obtains all the sub-values (cells) of @('val')
     at depth @('(len frame)'),
     which are a singleton scalar for the function value,
     and which have shape @($n_i\\ldots$) for the argument expression values.
     Then it replicates each such sub-value
     as many times as needed to fill the dimensions
     that follow @('frame') in @('pframe'),
     i.e. @($n_{\\mathit{fe}}\\ldots$) and @($n_{\\mathit{ae}}\\ldots$)
     in [thesis].")
   (xdoc::p
    "Roughly speaking, this ACL2 function corresponds to
     @($Rep_{n_{\\mathit{fe}}}
        [\\![
          \\mathit{Split}_1
          [\\![ \\mathfrak{v}_f \\ldots ]\!!]
        ]\!!]$)
     and
     @($Rep_{n_{\\mathit{ae}}}
        [\\![
          \\mathit{Split}_{n_{\\mathit{ac}}}
          [\\![ \\mathfrak{v}_a \\ldots ]\!!]
        ]\!!]$)
     in [thesis]."))
  (b* (((ok cells) (cells-at-depth-in-expr-value val (len frame))))
    (repeat-each (nat-list-product (nthcdr (len frame) pframe)) cells))

  ///

  (defret expr-value-list-wfp-of-lift-expr-value-to-frame
    (implies (and (expr-value-wfp val)
                  (not (reserrp cells)))
             (expr-value-list-wfp cells))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-expr-value-list-to-frame ((vals expr-value-listp)
                                       (frames nat-list-listp)
                                       (pframe nat-listp))
  :guard (and (equal (len vals) (len frames))
              (all-prefixp frames pframe))
  :returns (cell-lists expr-value-list-list-resultp)
  :short "Lift @(tsee lift-expr-value-to-frame)
          to a list of expression values with corresponding frames."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used on the argument expression values in a function application.
     They all share the principal frame @('pframe'),
     but each expression value has its own frame (a prefix of @('pframe')),
     so there is a list of frames corresponding to
     the list of expression values.
     Each expression value is lifted via @(tsee lift-expr-value-to-frame),
     yielding a list of cell lists, one per argument expression value,
     all of the same length (the number of positions of @('pframe')),
     lined up for the cell-wise application."))
  (b* (((when (endp vals)) nil)
       ((unless (mbt (consp frames))) (reserr nil))
       ((ok cells) (lift-expr-value-to-frame (car vals) (car frames) pframe))
       ((ok cell-lists)
        (lift-expr-value-list-to-frame (cdr vals) (cdr frames) pframe)))
    (cons cells cell-lists))
  :guard-hints
  (("Goal" :in-theory (enable acl2::true-list-listp-when-nat-list-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-values-match-type-values-p ((vals expr-value-listp)
                                         (tvals type-value-listp))
  :guard (expr-value-list-wfp vals)
  :returns (yes/no booleanp)
  :short "Check that expression values match type values
          in number and shape."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same length,
     and, element-wise, the dimensions of each expression value must equal
     the shape of the corresponding type value:
     the shape of an @(':array') type value is its shape component;
     the shape of every other type value, which is an atom type value,
     is the empty one.")
   (xdoc::p
    "This is used to evaluate term applications,
     where the expression values that a lambda is applied to
     must match the parameter type values of the lambda.
     Currently we only compare the dimensions of the expression values
     with the shapes of the type values;
     we plan to extend this to a complete check of
     the expression values against the type values."))
  (b* (((when (endp vals)) (endp tvals))
       ((when (endp tvals)) nil)
       (val (car vals))
       (tval (car tvals))
       (dims (type-value-case tval
                              :array tval.dims
                              :otherwise nil)))
    (and (equal (dims-of-expr-value val) dims)
         (expr-values-match-type-values-p (cdr vals) (cdr tvals))))

  ///

  (defruled len-equal-when-expr-values-match-type-values-p
    (implies (expr-values-match-type-values-p vals tvals)
             (equal (len vals) (len tvals)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines eval-exprs/atoms/binds
  :short "Evaluate expressions, atoms, and bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "These functions are mutually recursive,
     mirroring the mutually recursive structure of
     expressions, atoms, and bindings.
     Unlike the evaluation of ispaces and types,
     which is structurally recursive,
     the evaluation of expressions is not structurally recursive in general:
     evaluating the application of an abstraction
     involves evaluating the body of the abstraction,
     which is not a sub-structure of the application expression,
     but is obtained from a run-time expression value.
     Thus, to ensure termination, as required by ACL2,
     these functions take a limit argument
     that is decremented at each recursive call,
     and whose exhaustion causes an error.
     This is an artificial limit,
     with no counterpart in the run-time data
     of an executing Remora program.
     Formal proofs need to deal with this limit,
     e.g. the termination of a Remora program would be proved
     by exhibiting a suitable limit that does not run out."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-expr ((expr exprp) (denv expr-denvp) (limit natp))
    :guard (expr-denv-wfp denv)
    :returns (val expr-value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate an expression to an expression value."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the dynamic environment;
       it must be present, and its associated expression value is returned.")
     (xdoc::p
      "An atom expression is an atom auto-lifted to a rank-0 (scalar) array.
       We evaluate the atom to an expression value,
       which is also the expression value of the rank-0 array,
       because a rank-0 array is represented as its single atom
       (see @(tsee expr-value-with-nonempty-dims)
       on the empty list of dimensions).")
     (xdoc::p
      "A non-empty array must have no zero dimensions,
       and a number of atoms equal to the product of the dimensions.
       We evaluate the atoms to expression values.
       These are well-formed,
       because, given the well-formed dynamic environment required by the guard,
       evaluation returns well-formed expression values.
       They must also all have the same dimensions;
       we arrange them according to the dimensions
       via a separate function (see its documentation).")
     (xdoc::p
      "An empty array must have at least one 0 dimension,
       and its element type must evaluate to an atom type value.
       We build the result via a separate function (see its documentation).")
     (xdoc::p
      "A non-empty frame is like a non-empty array,
       but its elements are cell expressions instead of atoms.
       We evaluate the cells to expression values.
       These are well-formed,
       because, given the well-formed dynamic environment required by the guard,
       evaluation returns well-formed expression values.
       They must also all have the same dimensions;
       we arrange them according to the dimensions
       via the same function used for arrays;
       the dimensions of the cells become
       the inner dimensions of the result.")
     (xdoc::p
      "An empty frame is treated similarly to an empty array,
       but its type is the cell type, which may be an array type;
       we evaluate it,
       decompose it into the atom type value and the cell dimensions,
       append the cell dimensions to the frame dimensions,
       and build the result via the same function used for arrays.")
     (xdoc::p
      "A string is syntactic sugar for an array of integers,
       namely the codes of its characters;
       we evaluate it directly to the corresponding expression value.
       A non-empty string yields a vector of the integer code values;
       an empty string yields an empty integer array.")
     (xdoc::p
      "For a term application,
       we evaluate the function sub-expression
       and the argument sub-expressions,
       and we use a separate ACL2 function to apply
       the function value to the argument expression values.")
     (xdoc::p
      "For a unary type application,
       we evaluate the function sub-expression and the type argument,
       and we use a separate ACL2 function to apply
       the function value to the argument type value.
       For an n-ary type application,
       we evaluate the function sub-expression,
       and we use a separate ACL2 function
       that goes through the type arguments,
       evaluating each one and applying
       the current function value to it,
       consistently with the n-ary application being sugar for
       a chain of unary applications.")
     (xdoc::p
      "For a unary ispace application,
       we evaluate the function sub-expression and the ispace argument,
       and we use a separate ACL2 function to apply
       the function value to the argument ispace value.
       For an n-ary ispace application,
       we evaluate the function sub-expression,
       and we use a separate ACL2 function
       that goes through the ispace arguments,
       evaluating each one and applying
       the current function value to it,
       consistently with the n-ary application being sugar for
       a chain of unary applications.")
     (xdoc::p
      "For a combined application,
       we evaluate the function sub-expression,
       and then we successively apply the resulting function value to
       the type arguments, the ispace arguments, and the term arguments,
       reusing the ACL2 functions for
       type, ispace, and term applications.
       The type arguments and the ispace arguments are optional:
       the corresponding application is skipped when they are absent.")
     (xdoc::p
      "For an unboxing expression,
       we evaluate the target expression,
       and then we evaluate the unboxing over the resulting value
       via a separate ACL2 function (see @(tsee eval-unbox)).
       The optional type must be present:
       evaluation is only meaningful on type-checked, type-annotated ASTs.
       Our type checker will annotate the ASTs appropriately.")
     (xdoc::p
      "For a bracket expression,
       we evaluate the sub-expressions,
       we ensure that there is at least one resulting value
       (a bracket cannot be empty),
       we ensure that all the resulting values have the same dimensions,
       and we form a vector value with those values.")
     (xdoc::p
      "For a @('let') expression,
       we evaluate the bindings,
       which extend the dynamic environment,
       and then we evaluate the body in the extended environment."))
    (b* (((when (zp limit)) (reserr :limit)))
      (expr-case
       expr
       :var (expr-denv-lookup-expr expr.name denv)
       :atom (eval-atom expr.atom denv (1- limit))
       :array (b* (((when (member-equal 0 expr.dims)) (reserr nil))
                   ((ok vals) (eval-atom-list expr.atoms denv (1- limit)))
                   ((unless (equal (len vals) (nat-list-product expr.dims)))
                    (reserr nil))
                   ((unless (list-repeatp (dims-of-expr-value-list vals)))
                    (reserr nil)))
                (expr-value-with-nonempty-dims expr.dims vals))
       :array-empty (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
                         ((ok elem) (eval-type expr.type
                                               (expr-denv->tenv denv)))
                         ((when (type-value-case elem :array)) (reserr nil)))
                      (expr-value-with-empty-dim expr.dims elem))
       :frame (b* (((when (member-equal 0 expr.dims)) (reserr nil))
                   ((ok vals) (eval-expr-list expr.exprs denv (1- limit)))
                   ((unless (equal (len vals) (nat-list-product expr.dims)))
                    (reserr nil))
                   ((unless (list-repeatp (dims-of-expr-value-list vals)))
                    (reserr nil)))
                (expr-value-with-nonempty-dims expr.dims vals))
       :frame-empty (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
                         ((ok tval) (eval-type expr.type
                                               (expr-denv->tenv denv)))
                         ((mv elem cell-dims)
                          (type-value-case
                           tval
                           :array (mv tval.elem tval.dims)
                           :otherwise (mv tval nil)))
                         ((when (type-value-case elem :array)) (reserr nil))
                         (dims (append expr.dims cell-dims)))
                      (expr-value-with-empty-dim dims elem))
       :string (if (consp expr.chars)
                   (expr-value-vector
                    (expr-value-base-list
                     (base-value-int-list
                      (eval-char-lit-list expr.chars))))
                 (make-expr-value-vector-empty
                  :dims nil
                  :elem (type-value-base (base-type-int))))
       :app (b* (((ok funval) (eval-expr expr.fun denv (1- limit)))
                 ((ok argvals) (eval-expr-list expr.args denv (1- limit))))
              (eval-app funval argvals (1- limit)))
       :tapp (b* (((ok funval) (eval-expr expr.fun denv (1- limit)))
                  ((ok tval) (eval-type expr.arg
                                        (expr-denv->tenv denv))))
               (eval-tapp funval tval (1- limit)))
       :tappn (b* (((ok funval) (eval-expr expr.fun denv (1- limit))))
                (eval-tappn funval expr.args denv (1- limit)))
       :iapp (b* (((ok funval) (eval-expr expr.fun denv (1- limit)))
                  ((ok ival) (eval-ispace expr.arg
                                          (type-denv->ienv
                                           (expr-denv->tenv denv)))))
               (eval-iapp funval ival (1- limit)))
       :iappn (b* (((ok funval) (eval-expr expr.fun denv (1- limit))))
                (eval-iappn funval expr.args denv (1- limit)))
       :capp (b* (((ok funval) (eval-expr expr.fun denv (1- limit)))
                  ((ok funval)
                   (type-list-option-case
                    expr.targs
                    :some (eval-tappn funval expr.targs.val denv (1- limit))
                    :none funval))
                  ((ok funval)
                   (ispace-list-option-case
                    expr.iargs
                    :some (eval-iappn funval expr.iargs.val denv (1- limit))
                    :none funval))
                  ((ok argvals) (eval-expr-list expr.args denv (1- limit))))
               (eval-app funval argvals (1- limit)))
       :unbox (b* (((ok targetval) (eval-expr expr.target denv (1- limit)))
                   ((ok tval) (type-option-case
                               expr.type?
                               :some (eval-type expr.type?.val
                                                (expr-denv->tenv denv))
                               :none (reserr nil))))
                (eval-unbox targetval
                            expr.ispaces
                            expr.var
                            expr.body
                            tval
                            denv
                            (1- limit)))
       :bracket (b* (((ok vals) (eval-expr-list expr.exprs denv (1- limit)))
                     ((unless (consp vals)) (reserr nil))
                     ((unless (list-repeatp (dims-of-expr-value-list vals)))
                      (reserr nil)))
                  (expr-value-vector vals))
       :let (b* (((ok denv) (eval-bind-list expr.binds denv (1- limit))))
              (eval-expr expr.body denv (1- limit)))))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-expr-list ((exprs expr-listp) (denv expr-denvp) (limit natp))
    :guard (expr-denv-wfp denv)
    :returns (vals expr-value-list-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate a list of expressions to a list of expression values."
    :long
    (xdoc::topstring
     (xdoc::p
      "We evaluate each expression in turn
       and return the list of results in the same order."))
    (b* (((when (zp limit)) (reserr :limit))
         ((when (endp exprs)) nil)
         ((ok val) (eval-expr (car exprs) denv (1- limit)))
         ((ok vals) (eval-expr-list (cdr exprs) denv (1- limit))))
      (cons val vals))
    :measure (nfix limit)

    ///

    (defret len-of-eval-expr-list
      (implies (not (reserrp vals))
               (equal (len vals)
                      (len exprs)))
      :hints (("Goal"
               :induct (acl2::cdr-dec-induct exprs limit)
               :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-atom ((atom atomp) (denv expr-denvp) (limit natp))
    :guard (expr-denv-wfp denv)
    :returns (val expr-value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate an atom to an expression value."
    :long
    (xdoc::topstring
     (xdoc::p
      "A base literal is evaluated to a base value,
       which is embedded into an expression value.")
     (xdoc::p
      "A lambda abstraction evaluates to a lambda value
       with the same parameter variables,
       whose associated types are evaluated to type values;
       the optional body type, if present,
       is likewise evaluated to a type value;
       the body itself is not evaluated here,
       but only when the abstraction is applied.")
     (xdoc::p
      "A type lambda abstraction evaluates to
       a unary type lambda value.
       The abstraction must have at least one parameter:
       the value binds the first parameter,
       and its body is the type lambda abstraction
       over the remaining parameters if there are any,
       or otherwise the body of the given type lambda abstraction
       (see @(tsee tlambda-curried-body)):
       a type lambda abstraction with two or more parameters
       stands for the nesting of unary ones, in curried style.
       The body is not evaluated here,
       but only when the abstraction is applied.")
     (xdoc::p
      "An ispace lambda abstraction evaluates to
       a unary ispace lambda value.
       For the unary form, the value binds the parameter,
       and its body is the body of the abstraction.
       The n-ary form must have at least one parameter:
       the value binds the first parameter,
       and its body is the ispace lambda abstraction
       over the remaining parameters if there are any,
       or otherwise the body of the given ispace lambda abstraction
       (see @(tsee ilambda-curried-body)):
       an ispace lambda abstraction with two or more parameters
       stands for the nesting of unary ones, in curried style.")
     (xdoc::p
      "All three kinds of lambda values are closures:
       they include dynamic environments
       with the bindings for the free variables of their bodies
       (excluding the variables bound by their parameters),
       obtained by restricting the current dynamic environment
       to those variables.")
     (xdoc::p
      "A box evaluates to a box value:
       the ispaces are evaluated to ispace values,
       the array is evaluated to an expression value,
       and the type is evaluated to a type value."))
    (b* (((when (zp limit)) (reserr :limit)))
      (atom-case
       atom
       :base (expr-value-base (eval-base-lit atom.lit))
       :lambda (b* (((ok params) (eval-var+type?-list atom.params
                                                      (expr-denv->tenv denv)))
                    ((ok type?) (type-option-case
                                 atom.type?
                                 :none nil
                                 :some (eval-type atom.type?.val
                                                  (expr-denv->tenv denv)))))
                 (make-expr-value-lambda
                  :params params
                  :body atom.body
                  :type? type?
                  :denv (expr-denv-restrict
                         (expr-free-ispace-vars atom.body)
                         (expr-free-type-vars atom.body)
                         (atom-free-expr-vars atom)
                         denv)))
       :tlambdan
       (b* (((unless (consp atom.params)) (reserr nil)))
         (make-expr-value-tlambda
          :param (car atom.params)
          :body (tlambda-curried-body atom.params atom.body)
          :denv (expr-denv-restrict
                 (expr-free-ispace-vars atom.body)
                 (atom-free-type-vars atom)
                 (expr-free-expr-vars atom.body)
                 denv)))
       :ilambda (make-expr-value-ilambda
                 :param atom.param
                 :body atom.body
                 :denv (expr-denv-restrict
                        (atom-free-ispace-vars atom)
                        (expr-free-type-vars atom.body)
                        (expr-free-expr-vars atom.body)
                        denv))
       :ilambdan
       (b* (((unless (consp atom.params)) (reserr nil)))
         (make-expr-value-ilambda
          :param (car atom.params)
          :body (ilambda-curried-body atom.params atom.body)
          :denv (expr-denv-restrict
                 (atom-free-ispace-vars atom)
                 (expr-free-type-vars atom.body)
                 (expr-free-expr-vars atom.body)
                 denv)))
       :box (b* (((ok ivals) (eval-ispace-list atom.ispaces
                                               (type-denv->ienv
                                                (expr-denv->tenv denv))))
                 ((ok arrayval) (eval-expr atom.array denv (1- limit)))
                 ((ok tval) (eval-type atom.type (expr-denv->tenv denv))))
              (make-expr-value-box :ispaces ivals
                                   :array arrayval
                                   :type tval))))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-atom-list ((atoms atom-listp) (denv expr-denvp) (limit natp))
    :guard (expr-denv-wfp denv)
    :returns (vals expr-value-list-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate a list of atoms to a list of expression values."
    :long
    (xdoc::topstring
     (xdoc::p
      "We evaluate each atom in turn
       and return the list of results in the same order."))
    (b* (((when (zp limit)) (reserr :limit))
         ((when (endp atoms)) nil)
         ((ok val) (eval-atom (car atoms) denv (1- limit)))
         ((ok vals) (eval-atom-list (cdr atoms) denv (1- limit))))
      (cons val vals))
    :measure (nfix limit)

    ///

    (defret len-of-eval-atom-list
      (implies (not (reserrp vals))
               (equal (len vals)
                      (len atoms)))
      :hints (("Goal"
               :induct (acl2::cdr-dec-induct atoms limit)
               :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-bind ((bind bindp) (denv expr-denvp) (limit natp))
    :guard (expr-denv-wfp denv)
    :returns (new-denv expr-denv-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate a binding, extending the dynamic environment."
    :long
    (xdoc::topstring
     (xdoc::p
      "For an ispace binding,
       we evaluate the ispace to an ispace value,
       and we extend the dynamic environment
       to bind the ispace variable to that ispace value.")
     (xdoc::p
      "For a type binding,
       we evaluate the type to a type value,
       and we extend the dynamic environment
       to bind the type variable to that type value.")
     (xdoc::p
      "For a value binding,
       we evaluate the expression to an expression value,
       and we extend the dynamic environment
       to bind the variable to that expression value.
       If the optional type is present,
       we evaluate it as well, ignoring the resulting type value for now.
       The reason for evaluating it is that,
       once we extend expression values with type information,
       we plan to defensively check that the type,
       when present, is matched by the value.")
     (xdoc::p
      "For a function binding,
       we evaluate the parameter types to type values,
       and we extend the dynamic environment
       to bind the variable to the resulting lambda value;
       this is the value that the binding would yield
       after being desugared to a value binding.
       If the optional result type is present,
       we evaluate it, ignoring the resulting type value for now.
       Since the parameter types are already evaluated for the lambda value,
       the function type value can be assembled from these pieces
       when we need to check it against the lambda value.")
     (xdoc::p
      "For a type function binding,
       we extend the dynamic environment
       to bind the variable to the corresponding type lambda value,
       whose type parameters and body are taken without evaluation
       (the body is evaluated only when the abstraction is applied).
       If the optional result type is present,
       we form the universal type
       over the type parameters with the result type as body,
       and we evaluate it, ignoring the resulting type value for now.
       Note that we cannot just evaluate the type in the bindings,
       but we need to form the universal type
       (or, equivalently, extend the dynamic environment)
       because that type may reference the type parameters.")
     (xdoc::p
      "For an ispace function binding,
       we extend the dynamic environment
       to bind the variable to the corresponding ispace lambda value,
       whose ispace parameters and body are taken without evaluation
       (the body is evaluated only when the abstraction is applied).
       If the optional result type is present,
       we form the product type
       over the ispace parameters with the result type as body,
       and we evaluate it, ignoring the resulting type value for now;
       we form the product type, instead of evaluating the result type directly,
       because the result type may reference the ispace parameters.")
     (xdoc::p
      "For a combined function binding,
       we form the nested abstraction expression
       (a lambda over the value parameters,
       wrapped in an ispace lambda if there are ispace parameters,
       and then in a type lambda if there are type parameters),
       and we evaluate it to obtain the value to bind;
       this is the value that the binding would yield
       after being desugared to a value binding.
       As for the other bindings,
       we also form the corresponding nested type and evaluate it,
       ignoring the resulting type value for now.")
     (xdoc::p
      "The lambda values formed for the function bindings
       are closures with restricted dynamic environments,
       as in @(tsee eval-atom)."))
    (b* (((when (zp limit)) (reserr :limit)))
      (bind-case
       bind
       :ispace (b* (((ok ival) (eval-ispace bind.ispace
                                            (type-denv->ienv
                                             (expr-denv->tenv denv)))))
                 (expr-denv-add-ispace bind.var ival denv))
       :type (b* (((ok tval) (eval-type bind.type (expr-denv->tenv denv))))
               (expr-denv-add-type bind.var tval denv))
       :val (b* (((ok val) (eval-expr bind.expr denv (1- limit)))
                 ((ok &) (type-option-case
                          bind.type?
                          :some (eval-type bind.type?.val
                                           (expr-denv->tenv denv))
                          :none nil)))
              (expr-denv-add-expr bind.var val denv))
       :fun (b* (((ok params) (eval-var+type?-list bind.params
                                                   (expr-denv->tenv denv)))
                 (val (make-expr-value-lambda
                       :params params
                       :body bind.expr
                       :type? nil
                       :denv (expr-denv-restrict
                              (expr-free-ispace-vars bind.expr)
                              (expr-free-type-vars bind.expr)
                              (set::difference
                               (expr-free-expr-vars bind.expr)
                               (set::mergesort
                                (var+type?-list->var bind.params)))
                              denv)))
                 ((ok &) (type-option-case
                          bind.type?
                          :some (eval-type bind.type?.val
                                           (expr-denv->tenv denv))
                          :none nil)))
              (expr-denv-add-expr bind.var val denv))
       :tfun (b* (((unless (consp bind.params)) (reserr nil))
                  (val (make-expr-value-tlambda
                        :param (car bind.params)
                        :body (tlambda-curried-body bind.params bind.expr)
                        :denv (expr-denv-restrict
                               (expr-free-ispace-vars bind.expr)
                               (set::difference
                                (expr-free-type-vars bind.expr)
                                (set::mergesort bind.params))
                               (expr-free-expr-vars bind.expr)
                               denv)))
                  ((ok &) (type-option-case
                           bind.type?
                           :some (eval-type
                                  (make-type-forall :params bind.params
                                                    :body bind.type?.val)
                                  (expr-denv->tenv denv))
                           :none nil)))
               (expr-denv-add-expr bind.var val denv))
       :ifun (b* (((unless (consp bind.params)) (reserr nil))
                  (val (make-expr-value-ilambda
                        :param (car bind.params)
                        :body (ilambda-curried-body bind.params bind.expr)
                        :denv (expr-denv-restrict
                               (set::difference
                                (expr-free-ispace-vars bind.expr)
                                (set::mergesort bind.params))
                               (expr-free-type-vars bind.expr)
                               (expr-free-expr-vars bind.expr)
                               denv)))
                  ((ok &) (type-option-case
                           bind.type?
                           :some (eval-type
                                  (make-type-pin :params bind.params
                                                 :body bind.type?.val)
                                  (expr-denv->tenv denv))
                           :none nil)))
               (expr-denv-add-expr bind.var val denv))
       :cfun (b* ((lambda-expr (make-expr-array
                                :dims nil
                                :atoms (list (make-atom-lambda
                                              :params bind.params
                                              :body bind.expr
                                              :type? bind.type))))
                  ((ok in) (var+type?-list->type-list-or-err bind.params))
                  (lambda-type (make-type-fun
                                :in in
                                :out bind.type))
                  ((mv iexpr itype)
                   (ispace-var-list-option-case
                    bind.iparams?
                    :some (mv (make-expr-array
                               :dims nil
                               :atoms (list (make-atom-ilambdan
                                             :params bind.iparams?.val
                                             :body lambda-expr)))
                              (make-type-pin :params bind.iparams?.val
                                             :body lambda-type))
                    :none (mv lambda-expr lambda-type)))
                  ((mv cfun-expr cfun-type)
                   (type-var-list-option-case
                    bind.tparams?
                    :some (mv (make-expr-array
                               :dims nil
                               :atoms (list (make-atom-tlambdan
                                             :params bind.tparams?.val
                                             :body iexpr)))
                              (make-type-forall :params bind.tparams?.val
                                                :body itype))
                    :none (mv iexpr itype)))
                  ((ok val) (eval-expr cfun-expr denv (1- limit)))
                  ((ok &) (eval-type cfun-type (expr-denv->tenv denv))))
               (expr-denv-add-expr bind.var val denv))))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-bind-list ((binds bind-listp) (denv expr-denvp) (limit natp))
    :guard (expr-denv-wfp denv)
    :returns (new-denv expr-denv-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate a list of bindings,
            threading the dynamic environment through them."
    :long
    (xdoc::topstring
     (xdoc::p
      "We evaluate each binding in turn,
       extending the dynamic environment as we go,
       and we return the final environment."))
    (b* (((when (zp limit)) (reserr :limit))
         ((when (endp binds)) (expr-denv-fix denv))
         ((ok denv) (eval-bind (car binds) denv (1- limit))))
      (eval-bind-list (cdr binds) denv (1- limit)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-tapp ((funval expr-valuep)
                     (tval type-valuep)
                     (limit natp))
    :guard (expr-value-wfp funval)
    :returns (val expr-value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Apply an expression value to a type value."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called by @(tsee eval-expr) for a unary type application,
       after the function and the type argument have been evaluated:
       @('funval') is the expression value of the function,
       and @('tval') is the type value of the argument.
       It is also called by @(tsee eval-tappn),
       which realizes n-ary type applications
       as chains of unary ones.")
     (xdoc::p
      "The function value must be an array, of any rank,
       whose elements are type lambda abstractions
       or primitive operation values applicable to type values;
       the type argument value must match, in kind,
       the first parameter of each such element.
       Each element is applied to the type argument value.")
     (xdoc::p
      "This ACL2 function performs that element-wise application.
       The base case is that of a scalar (i.e. 0-rank array) function value.
       For a type lambda value, which binds exactly one parameter,
       we check that the argument matches the parameter in kind,
       we extend the dynamic environment contained in the type lambda value
       to associate the argument with the parameter,
       and we evaluate the body in the extended environment.
       If the type lambda abstraction has further parameters,
       the body is itself a type lambda abstraction
       (see @(tsee tlambda-curried-body)),
       whose evaluation, via @(tsee eval-atom),
       creates the closure for the remaining parameters,
       capturing the extended environment
       (restricted to the free variables):
       closure environments are extended
       only via the capture performed in @(tsee eval-atom).
       If instead the scalar function value is
       a primitive operation value applicable to type values,
       it is applied to the type argument value
       via @(tsee eval-primop-tfun).")
     (xdoc::p
      "A non-empty vector function value
       is applied via a separate ACL2 function that goes through the list.
       We check that the resulting list of expression values is not empty
       and that its expression values all have the same dimensions,
       but this should be eliminable via proofs,
       as we plan to do.
       We return the vector value consisting of the result expression values.")
     (xdoc::p
      "An empty vector function value has
       no type lambda abstractions to apply,
       but it carries the type of its would-be elements,
       which must be a universal type value,
       which binds exactly one parameter;
       the type argument value must match that parameter in kind.
       We extend the dynamic environment
       contained in the universal type value
       to associate the argument with the parameter,
       and we evaluate the body of the universal type value
       in the extended environment,
       which yields the type value of the would-be results
       of the element-wise application;
       similarly to the evaluation of empty frame expressions
       in @(tsee eval-expr),
       we decompose that type value into
       the atom type value and the dimensions,
       and we return the empty vector value
       whose element type value is that atom type value,
       and whose element dimensions are
       the element dimensions of the function value
       followed by the dimensions of the evaluated body of the universal type.
       If the universal type has further parameters,
       the body is itself a universal type (see @(tsee forall-curried-body)),
       whose evaluation yields
       the universal type value over the remaining parameters:
       that is an atom type value, contributing no dimensions,
       so partial instantiation needs no special treatment here.
       The implicit leading 0 dimension of the function value
       is also the implicit leading 0 dimension of the result expression value."))
    (b* (((when (zp limit)) (reserr :limit)))
      (expr-value-case
       funval
       :tlambda
       (b* (((unless (type-values-match-type-vars-p (list tval)
                                                    (list funval.param)))
             (reserr nil))
            (denv (expr-denv-add-type funval.param tval funval.denv)))
         (eval-expr funval.body denv (1- limit)))
       :primop (if (primop-value-tfunp funval.val)
                   (eval-primop-tfun funval.val tval)
                 (reserr nil))
       :vector
       (b* (((ok vals) (eval-tapp-list funval.elems tval (1- limit)))
            ;; TODO: eliminate the next two checks via proof
            ((unless (consp vals)) (reserr nil))
            ((unless (list-repeatp (dims-of-expr-value-list vals))) (reserr nil)))
         (expr-value-vector vals))
       :vector-empty
       (type-value-case
        funval.elem
        :forall
        (b* (((unless (type-values-match-type-vars-p
                       (list tval)
                       (list funval.elem.param)))
              (reserr nil))
             (tenv (type-denv-add-type funval.elem.param
                                       tval
                                       funval.elem.denv))
             ((ok bodyval) (eval-type funval.elem.body tenv))
             ((mv elem body-dims)
              (type-value-case
               bodyval
               :array (mv bodyval.elem bodyval.dims)
               :otherwise (mv bodyval nil)))
             ((when (type-value-case elem :array)) (reserr nil)))
          (make-expr-value-vector-empty
           :dims (append funval.dims body-dims)
           :elem elem))
        :otherwise (reserr nil))
       :otherwise (reserr nil)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-tapp-list ((funvals expr-value-listp)
                          (tval type-valuep)
                          (limit natp))
    :guard (expr-value-list-wfp funvals)
    :returns (vals expr-value-list-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Lift @(tsee eval-tapp) to a list of function values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This applies each expression value to the type value,
       returning the list of results in the same order.
       It is used to lift type application over
       a vector of type lambda values (see @(tsee eval-tapp))."))
    (b* (((when (zp limit)) (reserr :limit))
         ((when (endp funvals)) nil)
         ((ok val) (eval-tapp (car funvals) tval (1- limit)))
         ((ok vals) (eval-tapp-list (cdr funvals) tval (1- limit))))
      (cons val vals))
    :measure (nfix limit)

    ///

    (defret len-of-eval-tapp-list
      (implies (not (reserrp vals))
               (equal (len vals)
                      (len funvals)))
      :hints (("Goal"
               :induct (acl2::cdr-dec-induct funvals limit)
               :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-tappn ((funval expr-valuep)
                      (args type-listp)
                      (denv expr-denvp)
                      (limit natp))
    :guard (expr-value-wfp funval)
    :returns (val expr-value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Apply an expression value to
            the arguments of an n-ary type application."
    :long
    (xdoc::topstring
     (xdoc::p
      "An n-ary type application is sugar for
       a left-nested chain of unary type applications (see @(tsee expr)).
       Accordingly, after @(tsee eval-expr) has evaluated
       the function sub-expression of an n-ary type application,
       this function goes through the type arguments,
       evaluating each one
       and applying the current function value to it
       via @(tsee eval-tapp),
       in the same order in which
       the chain of unary applications would be evaluated.
       If there are no arguments, we return the function value."))
    (b* (((when (zp limit)) (reserr :limit))
         ((when (endp args)) (expr-value-fix funval))
         ((ok tval) (eval-type (car args) (expr-denv->tenv denv)))
         ((ok val) (eval-tapp funval tval (1- limit))))
      (eval-tappn val (cdr args) denv (1- limit)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-iapp ((funval expr-valuep)
                     (ival ispace-valuep)
                     (limit natp))
    :guard (expr-value-wfp funval)
    :returns (val expr-value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Apply an expression value to an ispace value."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called by @(tsee eval-expr) for a unary ispace application,
       after the function and the ispace argument have been evaluated:
       @('funval') is the expression value of the function,
       and @('ival') is the ispace value of the argument.
       It is also called by @(tsee eval-iappn),
       which realizes n-ary ispace applications
       as chains of unary ones.")
     (xdoc::p
      "The function value must be an array, of any rank,
       whose elements are ispace lambda abstractions
       or primitive operation values applicable to ispace values;
       the ispace argument value must match, in sort,
       the first parameter of each such element.
       Each element is applied to the ispace argument value.")
     (xdoc::p
      "This ACL2 function performs that element-wise application.
       The base case is that of a scalar (i.e. 0-rank array) function value.
       For an ispace lambda value, which binds exactly one parameter,
       we check that the argument matches the parameter in sort,
       we extend the dynamic environment
       contained in the ispace lambda value
       to associate the argument with the parameter,
       and we evaluate the body in the extended environment.
       If the ispace lambda abstraction has further parameters,
       the body is itself an ispace lambda abstraction
       (see @(tsee ilambda-curried-body)),
       whose evaluation, via @(tsee eval-atom),
       creates the closure for the remaining parameters,
       capturing the extended environment
       (restricted to the free variables):
       closure environments are extended
       only via the capture performed in @(tsee eval-atom).
       If instead the scalar function value is
       a primitive operation value applicable to ispace values,
       it is applied to the ispace argument value
       via @(tsee eval-primop-ifun).")
     (xdoc::p
      "A non-empty vector function value
       is applied via a separate ACL2 function that goes through the list.
       We check that the resulting list of expression values is not empty
       and that its expression values all have the same dimensions,
       but this should be eliminable via proofs,
       as we plan to do.
       We return the vector value consisting of the result expression values.")
     (xdoc::p
      "An empty vector function value has
       no ispace lambda abstractions to apply,
       but it carries the type of its would-be elements,
       which must be a product type value,
       which binds exactly one parameter;
       the ispace argument value must match that parameter in sort.
       We extend the dynamic environment
       contained in the product type value
       to associate the argument with the parameter,
       and we evaluate the body of the product type value
       in the extended environment,
       which yields the type value of the would-be results
       of the element-wise application;
       similarly to the evaluation of empty frame expressions
       in @(tsee eval-expr),
       we decompose that type value into
       the atom type value and the dimensions,
       and we return the empty vector value
       whose element type value is that atom type value,
       and whose element dimensions are
       the element dimensions of the function value
       followed by the dimensions of the evaluated body of the product type.
       If the product type has further parameters,
       the body is itself a product type (see @(tsee pi-curried-body)),
       whose evaluation yields
       the product type value over the remaining parameters:
       that is an atom type value, contributing no dimensions,
       so partial instantiation needs no special treatment here.
       The implicit leading 0 dimension of the function value
       is also the implicit leading 0 dimension of the result expression value."))
    (b* (((when (zp limit)) (reserr :limit)))
      (expr-value-case
       funval
       :ilambda
       (b* (((unless (ispace-values-match-ispace-vars-p
                      (list ival) (list funval.param)))
             (reserr nil))
            (denv (expr-denv-add-ispace funval.param ival funval.denv)))
         (eval-expr funval.body denv (1- limit)))
       :primop (if (primop-value-ifunp funval.val)
                   (eval-primop-ifun funval.val ival)
                 (reserr nil))
       :vector
       (b* (((ok vals) (eval-iapp-list funval.elems ival (1- limit)))
            ;; TODO: eliminate the next two checks via proof
            ((unless (consp vals)) (reserr nil))
            ((unless (list-repeatp (dims-of-expr-value-list vals))) (reserr nil)))
         (expr-value-vector vals))
       :vector-empty
       (type-value-case
        funval.elem
        :pi
        (b* (((unless (ispace-values-match-ispace-vars-p
                       (list ival) (list funval.elem.param)))
              (reserr nil))
             (tenv (type-denv-add-ispace funval.elem.param
                                         ival
                                         funval.elem.denv))
             ((ok tval) (eval-type funval.elem.body tenv))
             ((mv elem body-dims)
              (type-value-case
               tval
               :array (mv tval.elem tval.dims)
               :otherwise (mv tval nil)))
             ((when (type-value-case elem :array)) (reserr nil)))
          (make-expr-value-vector-empty :dims (append funval.dims body-dims)
                                        :elem elem))
        :otherwise (reserr nil))
       :otherwise (reserr nil)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-iapp-list ((funvals expr-value-listp)
                          (ival ispace-valuep)
                          (limit natp))
    :guard (expr-value-list-wfp funvals)
    :returns (vals expr-value-list-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Lift @(tsee eval-iapp) to a list of function values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This applies each expression value to the ispace value,
       returning the list of results in the same order.
       It is used to lift ispace application over
       a vector of ispace lambda values (see @(tsee eval-iapp))."))
    (b* (((when (zp limit)) (reserr :limit))
         ((when (endp funvals)) nil)
         ((ok val) (eval-iapp (car funvals) ival (1- limit)))
         ((ok vals) (eval-iapp-list (cdr funvals) ival (1- limit))))
      (cons val vals))
    :measure (nfix limit)

    ///

    (defret len-of-eval-iapp-list
      (implies (not (reserrp vals))
               (equal (len vals)
                      (len funvals)))
      :hints (("Goal"
               :induct (acl2::cdr-dec-induct funvals limit)
               :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-iappn ((funval expr-valuep)
                      (args ispace-listp)
                      (denv expr-denvp)
                      (limit natp))
    :guard (expr-value-wfp funval)
    :returns (val expr-value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Apply an expression value to
            the arguments of an n-ary ispace application."
    :long
    (xdoc::topstring
     (xdoc::p
      "An n-ary ispace application is sugar for
       a left-nested chain of unary ispace applications (see @(tsee expr)).
       Accordingly, after @(tsee eval-expr) has evaluated
       the function sub-expression of an n-ary ispace application,
       this function goes through the ispace arguments,
       evaluating each one
       and applying the current function value to it
       via @(tsee eval-iapp),
       in the same order in which
       the chain of unary applications would be evaluated.
       If there are no arguments, we return the function value."))
    (b* (((when (zp limit)) (reserr :limit))
         ((when (endp args)) (expr-value-fix funval))
         ((ok ival) (eval-ispace (car args)
                                 (type-denv->ienv (expr-denv->tenv denv))))
         ((ok val) (eval-iapp funval ival (1- limit))))
      (eval-iappn val (cdr args) denv (1- limit)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-app ((funval expr-valuep)
                    (argvals expr-value-listp)
                    (limit natp))
    :guard (and (expr-value-wfp funval)
                (expr-value-list-wfp argvals))
    :returns (val expr-value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Apply an expression value to argument expression values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called by @(tsee eval-expr) for a term application,
       after the function and the argument expressions have been evaluated:
       @('funval') is the expression value of the function,
       and @('argvals') are the expression values of the arguments.")
     (xdoc::p
      "The function value must be an array, of any rank,
       whose elements are all lambda abstractions or primitive operations,
       with the same number of arguments and equivalent argument types.
       Via @(tsee fun-value-param-dims) we obtain
       the dimensions of the cells expected for each argument,
       reading the signature of a representative function leaf
       (a lambda abstraction's parameter types,
       or a primitive operation's arity;
       see @(tsee expr-value-first-fun)).
       The number of arguments must match
       the function's number of parameters.")
     (xdoc::p
      "Following the rank-polymorphic application semantics of Remora,
       each argument array is split into a frame and a cell,
       where the cell dimensions are
       the ones expected of the corresponding parameter
       and the frame consists of the remaining leading dimensions;
       the dimensions of the function array form its own frame.
       The principal frame is the join of all these frames
       under the prefix order (see @(tsee list-prefix-join)):
       it exists only if the frames form a chain,
       and each frame is then a prefix of the principal one.")
     (xdoc::p
      "If the principal frame is empty (it has some zero dimension),
       there are no positions at which to apply the function,
       and hence no result cells to assemble.
       Instead we build an empty result array directly:
       its dimensions are the principal frame
       followed by the result cell dimensions,
       and its element type is the atom type of the codomain
       (see @(tsee fun-value-result-type)),
       analogously to how empty frame expressions are evaluated
       (see @(tsee expr-value-with-empty-dim)).")
     (xdoc::p
      "We lift the function and every argument to the principal frame
       (see @(tsee lift-expr-value-to-frame)
       and @(tsee lift-expr-value-list-to-frame)),
       obtaining, for each application position in the frame,
       a function cell and the corresponding argument cells.
       We apply them element-wise via a separate ACL2 function,
       and we assemble the resulting cells into an array
       whose frame is the principal frame
       (see @(tsee expr-value-with-nonempty-dims)).
       The checks on the result
       (that its length matches the size of the frame,
       that its cells are well-formed,
       and that they all have the same dimensions)
       should be eliminable via proofs, as we plan to do.")
     (xdoc::p
      "Our current approach to frame lifting
       is somewhat in line with [thesis],
       which represents values as
       the list of their constituent atoms
       accompanied by their dimensions,
       wrapped in an array expression:
       in [thesis], frame lifting is performed by
       suitably recombining those atoms.
       Our approach also (partially) flattens, and then recombines,
       constituent values.
       A different approach, more in line with our model of values,
       would instead preserve the recursive structure of our values,
       and perform the necessary replication in the framework of that structure.
       We plan to explore this alternative approach."))
    (b* (((when (zp limit)) (reserr :limit))
         ((ok param-dims) (fun-value-param-dims funval))
         ((unless (equal (len argvals) (len param-dims))) (reserr nil))
         (arg-dims (dims-of-expr-value-list argvals))
         ((mv suffixesp arg-frames) (check-list-suffixes arg-dims param-dims))
         ((unless suffixesp) (reserr nil))
         (fun-frame (dims-of-expr-value funval))
         ((mv joinp pframe) (list-prefix-join (cons fun-frame arg-frames)))
         ((unless joinp) (reserr nil))
         ((when (member-equal 0 pframe))
          (b* (((ok tval) (fun-value-result-type funval))
               ((mv elem cell-dims)
                (type-value-case
                 tval
                 :array (mv tval.elem tval.dims)
                 :otherwise (mv tval nil)))
               ((when (type-value-case elem :array)) (reserr nil))
               (dims (append pframe cell-dims)))
            (expr-value-with-empty-dim dims elem)))
         ((ok fun-cells) (lift-expr-value-to-frame funval fun-frame pframe))
         ((ok arg-cell-lists)
          (lift-expr-value-list-to-frame argvals arg-frames pframe))
         ((ok result-cells)
          (eval-app-list fun-cells arg-cell-lists (1- limit)))
         ;; TODO: eliminate the next three checks via proof
         ((unless (equal (len result-cells) (nat-list-product pframe)))
          (reserr nil))
         ((unless (expr-value-list-wfp result-cells)) (reserr nil))
         ((unless (list-repeatp (dims-of-expr-value-list result-cells)))
          (reserr nil)))
      (expr-value-with-nonempty-dims pframe result-cells))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-app-list ((funcells expr-value-listp)
                         (argcell-lists expr-value-list-listp)
                         (limit natp))
    :guard (expr-value-list-wfp funcells)
    :returns (vals expr-value-list-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Apply function cells to argument cells, position-wise."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is used by @(tsee eval-app) after lifting:
       @('funcells') are the function cells, one per application position,
       and @('argcell-lists') are the cells of the arguments,
       one list per argument, each in application-position order.
       We go through the function cells in order;
       for each one, we collect the corresponding cells of all the arguments
       (the heads of the argument cell lists, via @(tsee car-list))
       and apply the function cell to them via a separate ACL2 function,
       advancing all the argument cell lists (via @(tsee cdr-list)).
       We return the list of results in application-position order.")
     (xdoc::p
      "The check that the collected argument cells
       form a list of expression values
       should be eliminable via proof, as we plan to do."))
    (b* (((when (zp limit)) (reserr :limit))
         ((when (endp funcells)) nil)
         (argcell-lists (expr-value-list-list-fix argcell-lists))
         ;; TODO: eliminate the next check via proof (may need a guard)
         ((unless (cons-listp argcell-lists)) (reserr nil))
         (argcells (car-list argcell-lists))
         ;; TODO: eliminate the next check via proof
         ((unless (expr-value-list-wfp argcells)) (reserr nil))
         ((ok val) (eval-app-cell (car funcells) argcells (1- limit)))
         ((ok vals) (eval-app-list (cdr funcells)
                                   (cdr-list argcell-lists)
                                   (1- limit))))
      (cons val vals))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-app-cell ((funcell expr-valuep)
                         (argcells expr-value-listp)
                         (limit natp))
    :guard (and (expr-value-wfp funcell)
                (expr-value-list-wfp argcells))
    :returns (val expr-value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Apply a single (scalar) function cell to its argument cells."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the base case of term application,
       used by @(tsee eval-app-list) at each application position.
       The function cell must be a (scalar) lambda abstraction;
       the argument cells must match its parameters in number and types.
       We extend the dynamic environment contained in the lambda value
       to associate the arguments with the parameters,
       and we evaluate the body of the lambda abstraction
       in the extended environment.")
     (xdoc::p
      "If the function cell is
       a primitive operation value applicable to expression values,
       it is applied to the argument cells via @(tsee eval-primop-fun),
       which dispatches to the corresponding ACL2 function
       in @(see primitives-evaluation)."))
    (b* (((when (zp limit)) (reserr :limit)))
      (expr-value-case
       funcell
       :lambda
       (b* (((unless (expr-values-match-type-values-p
                      argcells
                      (var+typevalue-list->type funcell.params)))
             (reserr nil))
            (denv (expr-denv-add-exprs
                   (var+typevalue-list->var funcell.params)
                   argcells
                   funcell.denv)))
         (eval-expr funcell.body denv (1- limit)))
       :primop (if (primop-value-funp funcell.val)
                   (eval-primop-fun funcell.val argcells)
                 (reserr nil))
       :otherwise (reserr nil)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-unbox ((target expr-valuep)
                      (ispaces ispace-var-listp)
                      (var stringp)
                      (body exprp)
                      (type type-valuep)
                      (denv expr-denvp)
                      (limit natp))
    :guard (and (expr-value-wfp target)
                (expr-denv-wfp denv))
    :returns (val expr-value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate the unboxing of a target value."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called by @(tsee eval-expr) for an unboxing expression,
       after the target expression has been evaluated to @('target');
       @('ispaces'), @('var'), and @('body') are
       the ispace variables, the term variable, and the body
       of the unboxing expression,
       while @('type') is the result type of the body,
       already evaluated to a type value.
       The type checker is required to have annotated this type;
       @(tsee eval-expr) returns an error if it is absent.")
     (xdoc::p
      "If the target is a scalar box value,
       we check that its ispace values match,
       in number and sorts,
       the ispace variables of the unboxing expression;
       we extend the dynamic environment
       to bind the ispace variables to the box's ispace values
       and the term variable to the box's array value;
       and we evaluate the body in the extended environment.")
     (xdoc::p
      "If the target is a non-empty vector,
       i.e. a non-empty array of boxes,
       we recursively evaluate the unboxing over each element,
       via a separate ACL2 function,
       and we form a vector value with the results.")
     (xdoc::p
      "If the target is an empty vector,
       i.e. an empty array of boxes,
       there are no boxes to unbox and hence no results to assemble.
       We instead build an empty result array directly:
       its dimensions are the target's dimensions
       followed by the result cell dimensions,
       and its element type is the atom type of @('type'),
       analogously to @(tsee eval-app) over an empty principal frame
       (see @(tsee expr-value-with-empty-dim))."))
    (b* (((when (zp limit)) (reserr :limit)))
      (expr-value-case
       target
       :box
       (b* (((unless (ispace-values-match-ispace-vars-p target.ispaces ispaces))
             (reserr nil))
            (denv (expr-denv-add-ispaces ispaces target.ispaces denv))
            (denv (expr-denv-add-expr var target.array denv)))
         (eval-expr body denv (1- limit)))
       :vector
       (b* (((ok vals)
             (eval-unbox-list target.elems ispaces var body type denv (1- limit)))
            ;; TODO: eliminate the next two checks via proof
            ((unless (consp vals)) (reserr nil))
            ((unless (list-repeatp (dims-of-expr-value-list vals))) (reserr nil)))
         (expr-value-vector vals))
       :vector-empty
       (b* (((unless (member-equal 0 target.dims)) (reserr nil))
            ((mv elem cell-dims)
             (type-value-case type
                              :array (mv type.elem type.dims)
                              :otherwise (mv type nil)))
            ((when (type-value-case elem :array)) (reserr nil))
            (dims (append target.dims cell-dims)))
         (expr-value-with-empty-dim dims elem))
       :otherwise (reserr nil)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-unbox-list ((targets expr-value-listp)
                           (ispaces ispace-var-listp)
                           (var stringp)
                           (body exprp)
                           (type type-valuep)
                           (denv expr-denvp)
                           (limit natp))
    :guard (and (expr-value-list-wfp targets)
                (expr-denv-wfp denv))
    :returns (vals expr-value-list-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Lift @(tsee eval-unbox) to a list of target values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This evaluates the unboxing over each element,
       returning the list of results in the same order.
       It is used to lift unboxing over
       a non-empty array of boxes (see @(tsee eval-unbox))."))
    (b* (((when (zp limit)) (reserr :limit))
         ((when (endp targets)) nil)
         ((ok val) (eval-unbox (car targets) ispaces var body type denv (1- limit)))
         ((ok vals)
          (eval-unbox-list (cdr targets) ispaces var body type denv (1- limit))))
      (cons val vals))
    :measure (nfix limit)

    ///

    (defret len-of-eval-unbox-list
      (implies (not (reserrp vals))
               (equal (len vals)
                      (len targets)))
      :hints (("Goal"
               :induct (acl2::cdr-dec-induct targets limit)
               :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual eval-exprs/atoms/binds
    :hints (("Goal"
             :expand ((eval-expr expr denv limit)
                      (eval-expr (expr-fix expr) denv limit)
                      (eval-expr expr (expr-denv-fix denv) limit)
                      (eval-expr-list exprs denv limit)
                      (eval-expr-list (expr-list-fix exprs) denv limit)
                      (eval-expr-list exprs (expr-denv-fix denv) limit)
                      (eval-atom atom denv limit)
                      (eval-atom (atom-fix atom) denv limit)
                      (eval-atom atom (expr-denv-fix denv) limit)
                      (eval-atom-list atoms denv limit)
                      (eval-atom-list (atom-list-fix atoms) denv limit)
                      (eval-atom-list atoms (expr-denv-fix denv) limit)
                      (eval-bind bind denv limit)
                      (eval-bind (bind-fix bind) denv limit)
                      (eval-bind bind (expr-denv-fix denv) limit)
                      (eval-bind-list binds denv limit)
                      (eval-bind-list (bind-list-fix binds) denv limit)
                      (eval-bind-list binds (expr-denv-fix denv) limit)
                      (eval-tapp funval tval limit)
                      (eval-tapp (expr-value-fix funval) tval limit)
                      (eval-tapp funval (type-value-fix tval) limit)
                      (eval-tapp-list funvals tval limit)
                      (eval-tapp-list (expr-value-list-fix funvals)
                                      tval limit)
                      (eval-tapp-list funvals (type-value-fix tval) limit)
                      (eval-tappn funval args denv limit)
                      (eval-tappn (expr-value-fix funval) args denv limit)
                      (eval-tappn funval (type-list-fix args) denv limit)
                      (eval-tappn funval args (expr-denv-fix denv) limit)
                      (eval-iapp funval ival limit)
                      (eval-iapp (expr-value-fix funval) ival limit)
                      (eval-iapp funval
                                 (ispace-value-fix ival) limit)
                      (eval-iapp-list funvals ival limit)
                      (eval-iapp-list (expr-value-list-fix funvals)
                                      ival limit)
                      (eval-iapp-list funvals
                                      (ispace-value-fix ival) limit)
                      (eval-iappn funval args denv limit)
                      (eval-iappn (expr-value-fix funval) args denv limit)
                      (eval-iappn funval
                                  (ispace-list-fix args) denv limit)
                      (eval-iappn funval args (expr-denv-fix denv) limit)
                      (eval-app funval argvals limit)
                      (eval-app (expr-value-fix funval) argvals limit)
                      (eval-app funval (expr-value-list-fix argvals) limit)
                      (eval-app-list funcells argcell-lists limit)
                      (eval-app-list (expr-value-list-fix funcells)
                                     argcell-lists limit)
                      (eval-app-list funcells
                                     (expr-value-list-list-fix argcell-lists)
                                     limit)
                      (eval-app-cell funcell argcells limit)
                      (eval-app-cell (expr-value-fix funcell) argcells limit)
                      (eval-app-cell funcell (expr-value-list-fix argcells)
                                     limit)
                      (eval-unbox target ispaces var body type denv limit)
                      (eval-unbox (expr-value-fix target)
                                  ispaces var body type denv limit)
                      (eval-unbox target (ispace-var-list-fix ispaces)
                                  var body type denv limit)
                      (eval-unbox target ispaces (str::str-fix var)
                                  body type denv limit)
                      (eval-unbox target ispaces var (expr-fix body)
                                  type denv limit)
                      (eval-unbox target ispaces var body
                                  (type-value-fix type) denv limit)
                      (eval-unbox target ispaces var body
                                  type (expr-denv-fix denv) limit)
                      (eval-unbox-list targets ispaces var body type denv limit)
                      (eval-unbox-list (expr-value-list-fix targets)
                                       ispaces var body type denv limit)
                      (eval-unbox-list targets (ispace-var-list-fix ispaces)
                                       var body type denv limit)
                      (eval-unbox-list targets ispaces (str::str-fix var)
                                       body type denv limit)
                      (eval-unbox-list targets ispaces var (expr-fix body)
                                       type denv limit)
                      (eval-unbox-list targets ispaces var body
                                       (type-value-fix type) denv limit)
                      (eval-unbox-list targets ispaces var body
                                       type (expr-denv-fix denv) limit))
             :in-theory (enable nfix zp))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual expr-value-wfp-of-eval-exprs/atoms/binds
    (defret expr-value-wfp-of-eval-expr
      (implies (and (expr-denv-wfp denv)
                    (not (reserrp val)))
               (expr-value-wfp val))
      :fn eval-expr)
    (defret expr-value-list-wfp-of-eval-expr-list
      (implies (and (expr-denv-wfp denv)
                    (not (reserrp vals)))
               (expr-value-list-wfp vals))
      :fn eval-expr-list)
    (defret expr-value-wfp-of-eval-atom
      (implies (and (expr-denv-wfp denv)
                    (not (reserrp val)))
               (expr-value-wfp val))
      :fn eval-atom)
    (defret expr-value-list-wfp-of-eval-atom-list
      (implies (and (expr-denv-wfp denv)
                    (not (reserrp vals)))
               (expr-value-list-wfp vals))
      :fn eval-atom-list)
    (defret expr-denv-wfp-of-eval-bind
      (implies (and (expr-denv-wfp denv)
                    (not (reserrp new-denv)))
               (expr-denv-wfp new-denv))
      :fn eval-bind)
    (defret expr-denv-wfp-of-eval-bind-list
      (implies (and (expr-denv-wfp denv)
                    (not (reserrp new-denv)))
               (expr-denv-wfp new-denv))
      :fn eval-bind-list)
    (defret expr-value-wfp-of-eval-tapp
      (implies (and (expr-value-wfp funval)
                    (not (reserrp val)))
               (expr-value-wfp val))
      :fn eval-tapp)
    (defret expr-value-list-wfp-of-eval-tapp-list
      (implies (and (expr-value-list-wfp funvals)
                    (not (reserrp vals)))
               (expr-value-list-wfp vals))
      :fn eval-tapp-list)
    (defret expr-value-wfp-of-eval-tappn
      (implies (and (expr-value-wfp funval)
                    (not (reserrp val)))
               (expr-value-wfp val))
      :fn eval-tappn)
    (defret expr-value-wfp-of-eval-iapp
      (implies (and (expr-value-wfp funval)
                    (not (reserrp val)))
               (expr-value-wfp val))
      :fn eval-iapp)
    (defret expr-value-list-wfp-of-eval-iapp-list
      (implies (and (expr-value-list-wfp funvals)
                    (not (reserrp vals)))
               (expr-value-list-wfp vals))
      :fn eval-iapp-list)
    (defret expr-value-wfp-of-eval-iappn
      (implies (and (expr-value-wfp funval)
                    (not (reserrp val)))
               (expr-value-wfp val))
      :fn eval-iappn)
    (defret expr-value-wfp-of-eval-app
      (implies (and (expr-value-wfp funval)
                    (not (reserrp val)))
               (expr-value-wfp val))
      :fn eval-app)
    (defret expr-value-list-wfp-of-eval-app-list
      (implies (and (expr-value-list-wfp funcells)
                    (not (reserrp vals)))
               (expr-value-list-wfp vals))
      :fn eval-app-list)
    (defret expr-value-wfp-of-eval-app-cell
      (implies (and (expr-value-wfp funcell)
                    (expr-value-list-wfp argcells)
                    (not (reserrp val)))
               (expr-value-wfp val))
      :fn eval-app-cell)
    (defret expr-value-wfp-of-eval-unbox
      (implies (and (expr-denv-wfp denv)
                    (expr-value-wfp target)
                    (not (reserrp val)))
               (expr-value-wfp val))
      :fn eval-unbox)
    (defret expr-value-list-wfp-of-eval-unbox-list
      (implies (and (expr-denv-wfp denv)
                    (expr-value-list-wfp targets)
                    (not (reserrp vals)))
               (expr-value-list-wfp vals))
      :fn eval-unbox-list)
    :mutual-recursion eval-exprs/atoms/binds
    :hints
    (("Goal"
      :in-theory (enable expr-value-wfp-of-cdr-of-assoc-when-expr-denv-wfp
                         expr-value-wfp-of-expr-value-with-nonempty-dims
                         nfix
                         zp)
      :expand ((eval-expr expr denv limit)
               (eval-expr-list exprs denv limit)
               (eval-atom atom denv limit)
               (eval-atom-list atoms denv limit)
               (eval-bind bind denv limit)
               (eval-bind-list binds denv limit)
               (eval-tapp funval tval limit)
               (eval-tapp-list funvals tval limit)
               (eval-tappn funval args denv limit)
               (eval-iapp funval ival limit)
               (eval-iapp-list funvals ival limit)
               (eval-iappn funval args denv limit)
               (eval-app funval argvals limit)
               (eval-app-list funcells argcell-lists limit)
               (eval-app-cell funcell argcells limit)
               (eval-unbox target ispaces var body type denv limit)
               (eval-unbox-list targets ispaces var body type denv limit)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards eval-expr
    :hints
    (("Goal"
      :in-theory (e/d (len-equal-when-expr-values-match-type-values-p
                       true-listp-when-nat-listp
                       acl2::true-list-listp-when-nat-list-listp
                       true-list-listp-when-expr-value-list-listp)
                      (len-of-eval-expr-list))))))

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
