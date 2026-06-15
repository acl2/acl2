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
                          valuep-when-result-not-error
                          value-listp-when-result-not-error
                          var+typevalue-p-when-result-not-error
                          var+typevalue-listp-when-result-not-error)))

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
               (append-all natss))
     :splice (b* (((ok natss) (eval-shape-list shape.shapes denv)))
               (append-all natss)))
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

  :guard-hints
  (("Goal" :in-theory (enable acl2::true-list-listp-when-nat-list-listp)))

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
                   (nats (append-all natss)))
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

  :guard-hints
  (("Goal" :in-theory (enable acl2::true-list-listp-when-nat-list-listp)))

  ///

  (fty::deffixequiv-mutual eval-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-var+type ((var+type var+type-p) (denv denvp))
  :returns (var+tval var+typevalue-resultp)
  :short "Evaluate a variable with a type
          to a variable with a type value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is unchanged;
     its associated type is evaluated to a type value."))
  (b* (((var+type var+type) var+type)
       ((ok tval) (eval-type var+type.type denv)))
    (make-var+typevalue :var var+type.var :type tval)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-var+type-list ((var+types var+type-listp) (denv denvp))
  :returns (var+tvals var+typevalue-list-resultp)
  :short "Evaluate a list of variables with types
          to a list of variables with type values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We evaluate each element in turn
     and return the list of results in the same order."))
  (b* (((when (endp var+types)) nil)
       ((ok var+tval) (eval-var+type (car var+types) denv))
       ((ok var+tvals) (eval-var+type-list (cdr var+types) denv)))
    (cons var+tval var+tvals))

  ///

  (defret len-of-eval-var+type-list
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

(define value-with-empty-dim ((dims nat-listp) (elem type-valuep))
  :guard (and (member-equal 0 dims)
              (not (type-value-case elem :array)))
  :returns (val valuep)
  :short "Build a vector value with an empty dimension."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to evaluate empty array or frame expressions,
     which must have at least one zero dimension
     and an atom (i.e. non-array) type (value) for elements,
     as expressed by the guard.
     In the case of empty frame expressions,
     the type value passed to this function is not
     the result of evaluating the type in the frame expression,
     which may be an array type:
     it is the atom type (value) of that array type,
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
    "A key property is that the resulting value is well-formed
     and has exactly the dimensions passed as input."))
  (b* (((when (not (mbt (consp dims)))) (value-vector-empty nil elem))
       (dim (lnfix (car dims))))
    (if (= dim 0)
        (make-value-vector-empty :dims (cdr dims) :elem elem)
      (value-vector
       (repeat dim (value-with-empty-dim (cdr dims) elem)))))
  :verify-guards :after-returns

  ///

  (defret check-dims-of-value-of-value-with-empty-dim
    (b* ((dims1 (check-dims-of-value val)))
      (and (not (reserrp dims1))
           (equal dims1 (nat-list-fix dims))))
    :hyp (member-equal 0 dims)
    :hints (("Goal"
             :induct t
             :in-theory (enable check-dims-of-value
                                check-dims-of-value-list-of-repeat
                                acl2::not-reserrp-when-nat-listp
                                acl2::not-reserrp-when-nat-list-listp
                                car-of-repeat
                                nfix))))

  (defret value-wfp-of-value-with-empty-dim
    (value-wfp val)
    :hyp (member-equal 0 dims)
    :hints (("Goal" :in-theory (enable value-wfp
                                       acl2::not-reserrp-when-nat-listp))))

  (defret dims-of-value-of-value-with-empty-dim
    (equal (dims-of-value val)
           (nat-list-fix dims))
    :hyp (member-equal 0 dims)
    :hints (("Goal" :in-theory (enable dims-of-value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines values-with-nonempty-dims
  :short "Build values with non-empty dimensions and with given elements."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define value-with-nonempty-dims ((dims nat-listp) (vals value-listp))
    :guard (and (not (member-equal 0 dims))
                (equal (len vals) (nat-list-product dims))
                (value-list-wfp vals)
                (list-repeatp (dims-of-value-list vals)))
    :returns (val valuep)
    :parents (evaluation values-with-nonempty-dims)
    :short "Build a value
            from its dimensions and
            from the values of its elements."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is used to evaluate non-empty array or frame expressions,
       which have all non-zero dimensions as required by the guard.
       The number of values must match the product of the dimensions,
       as required by the guard,
       so that the values can be arranged according to the dimensions.
       Furthermore, as also required by the guard,
       all values must be well-formed and have the same dimensions.")
     (xdoc::p
      "When there are no dimensions left in the list,
       the list of values must be a singleton
       because its length must match the product of dimensions,
       which is 1 for the empty list of dimensions.
       Otherwise, we take out the first dimension,
       and we split the list of values into as many chunks as that dimension
       (which is not 0 as enforced by the guard),
       where each chunk has as its size the (integer) ratio of
       the total number of values and the first dimension.
       We construct values for each chunk
       via the companion recursive function.
       We put these values together into a vector value,
       which is the final result.")
     (xdoc::p
      "A key property is that the resulting value is well-formed
       and has exactly the concatenation of
       the dimensions passed as input
       and the common dimensions of the component values."))
    (b* (((when (endp dims)) (value-fix (car vals)))
         (dim (lnfix (car dims)))
         (valss (list-split (value-list-fix vals) (/ (len vals) dim)))
         (vals (value-list-with-nonempty-dims (cdr dims) valss)))
      (value-vector vals))
    :measure (acl2::nat-list-measure (list (len dims) 0 0)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define value-list-with-nonempty-dims ((dims nat-listp)
                                         (valss value-list-listp))
    :guard (and (not (member-equal 0 dims))
                (all-of-len-p valss (nat-list-product dims))
                (value-list-list-wfp valss)
                (list-repeatp (dims-of-value-list-list valss))
                (list-list-repeatp (dims-of-value-list-list valss)))
    :returns (vals value-listp)
    :parents (evaluation values-with-nonempty-dims)
    :short "Build a list of values from a common list of dimensions
            and a list of lists of component values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This lifts @(tsee value-with-nonempty-dims) to lists of lists of values.
       See the documentation of that function.")
     (xdoc::p
      "The guard requires the same dimensions of
       all the values in the list of lists of values:
       this is expressed via @(tsee list-list-repeatp),
       which says that each list of values has the same dimensions,
       and via @(tsee list-repeatp),
       which additionally requires the equality of
       the lists of lists of dimensions corresponding to the lists of values.")
     (xdoc::p
      "The key property mentioned in @(tsee value-with-nonempty-dims)
       is proved by induction simultaneously with
       a corresponding property for this function.
       This corresponding property is lifted to lists:
       the list of lists of dimensions of the resulting list of values
       is a repetition of the same list of dimensions,
       which consists of the dimensions passed as input
       concatenated with the common dimensions of all the values
       (we extract the latter via @(tsee car) of @(tsee car)."))
    (cond ((endp valss) nil)
          (t (cons (value-with-nonempty-dims dims (car valss))
                   (value-list-with-nonempty-dims dims (cdr valss)))))
    :measure (acl2::nat-list-measure (list (len dims) 1 (len valss)))

    ///

    (defret len-of-value-list-with-nonempty-dims
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
                             (true-list-listp-when-value-list-listp
                              acl2::true-list-listp-when-nat-list-listp
                              acl2::true-list-listp-when-nat-list-list-listp
                              nat-list-product-of-cdr-to-ratio
                              posp
                              dims-of-value-list-list-of-cdr)
                             (cdr-of-dims-of-value-list-list))
                 :use nat-list-product-divided-by-car))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual values-with-nonempty-dims)

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
    (implies (and (value-listp vals)
                  (nat-listp dims)
                  (not (member-equal 0 dims))
                  (consp dims)
                  (equal (len vals) (nat-list-product dims)))
             (value-list-listp
              (list-split vals (* (/ (car dims)) (len vals)))))
    :enable posp
    :disable value-list-listp-of-list-split
    :use (nat-list-product-divided-by-car
          (:instance value-list-listp-of-list-split
                     (n (/ (len vals) (car dims))))))

  (defret-mutual check-dims-of-values-with-nonempty-dims
    (defret check-dims-of-value-with-nonempty-dims
      (b* ((dims1 (check-dims-of-value val)))
        (and (not (reserrp dims1))
             (equal dims1
                    (append (nat-list-fix dims)
                            (car (dims-of-value-list vals))))))
      :hyp (and (nat-listp dims)
                (value-listp vals)
                (not (member-equal 0 dims))
                (equal (len vals) (nat-list-product dims))
                (value-list-wfp vals)
                (list-repeatp (dims-of-value-list vals)))
      :fn value-with-nonempty-dims)
    (defret check-dims-of-value-list-with-nonempty-dims
      (b* ((dimss (check-dims-of-value-list vals)))
        (and (not (reserrp dimss))
             (equal dimss
                    (repeat (len valss)
                            (append (nat-list-fix dims)
                                    (car (car (dims-of-value-list-list
                                               valss))))))))
      :hyp (and (nat-listp dims)
                (value-list-listp valss)
                (not (member-equal 0 dims))
                (all-of-len-p valss (nat-list-product dims))
                (value-list-list-wfp valss)
                (list-repeatp (dims-of-value-list-list valss))
                (list-list-repeatp (dims-of-value-list-list valss)))
      :fn value-list-with-nonempty-dims)
    :mutual-recursion values-with-nonempty-dims
    :hints (("Goal"
             :in-theory (enable value-with-nonempty-dims
                                value-list-with-nonempty-dims
                                check-dims-of-value
                                check-dims-of-value-list
                                acl2::not-reserrp-when-nat-listp
                                acl2::not-reserrp-when-nat-list-listp
                                value-wfp
                                dims-of-value
                                dims-of-value-list-list
                                nat-list-product-of-cdr-to-ratio
                                list-repeatp
                                repeat
                                car-of-repeat
                                car-of-car-of-list-split
                                lemma1
                                lemma2))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret value-wfp-of-value-with-nonempty-dims
    (value-wfp val)
    :hyp (and (nat-listp dims)
              (value-listp vals)
              (not (member-equal 0 dims))
              (equal (len vals) (nat-list-product dims))
              (value-list-wfp vals)
              (list-repeatp (dims-of-value-list vals)))
    :fn value-with-nonempty-dims
    :hints (("Goal" :in-theory (enable value-wfp
                                       acl2::not-reserrp-when-nat-listp))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret value-list-wfp-of-value-list-with-nonempty-dims
    (value-list-wfp vals)
    :hyp (and (nat-listp dims)
              (value-list-listp valss)
              (not (member-equal 0 dims))
              (all-of-len-p valss (nat-list-product dims))
              (value-list-list-wfp valss)
              (list-repeatp (dims-of-value-list-list valss))
              (list-list-repeatp (dims-of-value-list-list valss)))
    :fn value-list-with-nonempty-dims
    :hints (("Goal" :in-theory (enable value-list-wfp-alt-def
                                       acl2::not-reserrp-when-nat-list-listp))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret dims-of-value-of-value-with-nonempty-dims
    (equal (dims-of-value val)
           (append (nat-list-fix dims)
                   (car (dims-of-value-list vals))))
    :hyp (and (nat-listp dims)
              (value-listp vals)
              (not (member-equal 0 dims))
              (equal (len vals) (nat-list-product dims))
              (value-list-wfp vals)
              (list-repeatp (dims-of-value-list vals)))
    :fn value-with-nonempty-dims
    :hints (("Goal" :in-theory (enable dims-of-value))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret dims-of-value-list-of-value-list-with-nonempty-dims
    (equal (dims-of-value-list vals)
           (repeat (len valss)
                   (append (nat-list-fix dims)
                           (car (car (dims-of-value-list-list valss))))))
    :hyp (and (nat-listp dims)
              (value-list-listp valss)
              (not (member-equal 0 dims))
              (all-of-len-p valss (nat-list-product dims))
              (value-list-list-wfp valss)
              (list-repeatp (dims-of-value-list-list valss))
              (list-list-repeatp (dims-of-value-list-list valss)))
    :fn value-list-with-nonempty-dims
    :hints (("Goal"
             :use (:instance
                   dims-of-value-list-when-value-list-wfp
                   (vals (value-list-with-nonempty-dims dims valss)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-value-to-frame ((val valuep) (frame nat-listp) (pframe nat-listp))
  :guard (prefixp frame pframe)
  :returns (cells value-list-resultp)
  :short "Lift a value to a principal frame,
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
     and which have shape @($n_i\\ldots$) for the argument values.
     Then it replicates each such sub-value
     as many times as needed to fill the dimensions
     that follow @('frame') in @('pframe'),
     i.e. @($n_{\\mathit{fe}}\\ldots$) and @($n_{\\mathit{ae}}\\ldots$)
     in [thesis].")
   (xdoc::p
    "Roughly speaking, this ACL2 function corresponds to
     @($Rep_{n_{\\mathit{fe}}}
        \\llbracket
          \\mathit{Split}_1
          \\llbracket \\mathfrak{v}_f \\ldots \\rrbracket
        \\rrbracket$)
     and
     @($Rep_{n_{\\mathit{ae}}}
        \\llbracket
          \\mathit{Split}_{n_{\\mathit{ac}}}
          \\llbracket \\mathfrak{v}_a \\ldots \\rrbracket
        \\rrbracket$)
     in [thesis]."))
  (b* (((ok cells) (cells-at-depth-in-value val (len frame))))
    (repeat-each (nat-list-product (nthcdr (len frame) pframe)) cells)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-values-match-type-vars-p ((tvals type-value-listp)
                                       (vars type-var-listp))
  :returns (yes/no booleanp)
  :short "Check that type values match type variables
          in number and kind."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same length,
     and, element-wise, each type value must match
     the kind of the corresponding type variable:
     an @(':atom') type variable must be matched by an atom type value,
     and an @(':array') type variable by an array type value.
     A type value has the array kind when it is an @(':array');
     every other type value has the atom kind.")
   (xdoc::p
    "This is used to evaluate type applications,
     where the type values that a type lambda is applied to
     must match the type parameters of the type lambda."))
  (b* (((when (endp tvals)) (endp vars))
       ((when (endp vars)) nil)
       (tval (car tvals))
       (var (car vars)))
    (and (type-var-case var
                        :atom (not (type-value-case tval :array))
                        :array (type-value-case tval :array))
         (type-values-match-type-vars-p (cdr tvals) (cdr vars))))

  ///

  (defrule len-equal-when-type-values-match-type-vars-p
    (implies (type-values-match-type-vars-p tvals vars)
             (equal (len tvals) (len vars)))
    :rule-classes :forward-chaining
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-values-match-ispace-vars-p ((ivals ispace-value-listp)
                                           (vars ispace-var-listp))
  :returns (yes/no booleanp)
  :short "Check that ispace values match ispace variables
          in number and sort."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same length,
     and, element-wise, each ispace value must match
     the sort of the corresponding ispace variable:
     a @(':dim') ispace variable must be matched by a @(':dim') ispace value,
     and a @(':shape') ispace variable by a @(':shape') ispace value.")
   (xdoc::p
    "This is used to evaluate ispace applications,
     where the ispace values that an ispace lambda is applied to
     must match the ispace parameters of the ispace lambda."))
  (b* (((when (endp ivals)) (endp vars))
       ((when (endp vars)) nil)
       (ival (car ivals))
       (var (car vars)))
    (and (ispace-var-case var
                          :dim (ispace-value-case ival :dim)
                          :shape (ispace-value-case ival :shape))
         (ispace-values-match-ispace-vars-p (cdr ivals) (cdr vars))))

  ///

  (defrule len-equal-when-ispace-values-match-ispace-vars-p
    (implies (ispace-values-match-ispace-vars-p ivals vars)
             (equal (len ivals) (len vars)))
    :rule-classes :forward-chaining
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define values-match-type-values-p ((vals value-listp)
                                    (tvals type-value-listp))
  :guard (value-list-wfp vals)
  :returns (yes/no booleanp)
  :short "Check that values match type values
          in number and shape."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same length,
     and, element-wise, the dimensions of each value must equal
     the shape of the corresponding type value:
     the shape of an @(':array') type value is its shape component;
     the shape of every other type value, which is an atom type value,
     is the empty one.")
   (xdoc::p
    "This is used to evaluate term applications,
     where the values that a lambda is applied to
     must match the parameter type values of the lambda.
     Currently we only compare the dimensions of the values
     with the shapes of the type values;
     we plan to extend this to a complete check of
     the values against the type values."))
  (b* (((when (endp vals)) (endp tvals))
       ((when (endp tvals)) nil)
       (val (car vals))
       (tval (car tvals))
       (shape (type-value-case tval
                               :array tval.shape
                               :otherwise nil)))
    (and (equal (dims-of-value val) shape)
         (values-match-type-values-p (cdr vals) (cdr tvals))))

  ///

  (defruled len-equal-when-values-match-type-values-p
    (implies (values-match-type-values-p vals tvals)
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
     but is obtained from a run-time value.
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

  (define eval-expr ((expr exprp) (denv denvp) (limit natp))
    :guard (denv-wfp denv)
    :returns (val value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate an expression to a value."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the dynamic environment;
       it must be present, and its associated value is returned.")
     (xdoc::p
      "An atom expression is an atom auto-lifted to a rank-0 (scalar) array.
       We evaluate the atom to a value,
       which is also the value of the rank-0 array,
       because a rank-0 array is represented as its single atom
       (see @(tsee value-with-nonempty-dims) on the empty list of dimensions).")
     (xdoc::p
      "A non-empty array must have no zero dimensions,
       and a number of atoms equal to the product of the dimensions.
       We evaluate the atoms to values.
       These are well-formed,
       because, given the well-formed dynamic environment required by the guard,
       evaluation returns well-formed values.
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
       We evaluate the cells to values.
       These are well-formed,
       because, given the well-formed dynamic environment required by the guard,
       evaluation returns well-formed values.
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
       we evaluate it directly to the corresponding value.
       A non-empty string yields a vector of the integer code values;
       an empty string yields an empty integer array.")
     (xdoc::p
      "For a term application,
       we evaluate the function sub-expression
       and the argument sub-expressions.
       For now we require the function value to be
       a scalar lambda abstraction value,
       and the dimensions of each argument value to be exactly
       the shape of the corresponding parameter type value
       of the lambda abstraction:
       we do not support lifting yet, but we plan to add support for it.
       We check that the argument values match
       the parameter type values of the lambda abstraction
       in number and shape.
       We extend the dynamic environment
       to associate the argument values with the parameters
       (which may override existing associations,
       which is intended hiding behavior),
       and we evaluate the body of the lambda abstraction.")
     (xdoc::p
      "For a type application,
       we evaluate the function sub-expression and the type arguments,
       and we use a separate ACL2 function to apply
       the function value to the argument type values.")
     (xdoc::p
      "For an ispace application,
       we evaluate the function sub-expression and the ispace arguments,
       and we use a separate ACL2 function to apply
       the function value to the argument ispace values."))
    (b* (((when (zp limit)) (reserr :limit)))
      (expr-case
       expr
       :var (b* ((var+val (omap::assoc expr.name (denv->expr-vars denv)))
                 ((unless var+val) (reserr nil)))
              (cdr var+val))
       :atom (eval-atom expr.atom denv (1- limit))
       :array (b* (((when (member-equal 0 expr.dims)) (reserr nil))
                   ((ok vals) (eval-atom-list expr.atoms denv (1- limit)))
                   ((unless (equal (len vals) (nat-list-product expr.dims)))
                    (reserr nil))
                   ((unless (list-repeatp (dims-of-value-list vals)))
                    (reserr nil)))
                (value-with-nonempty-dims expr.dims vals))
       :array-empty (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
                         ((ok elem) (eval-type expr.type denv))
                         ((when (type-value-case elem :array)) (reserr nil)))
                      (value-with-empty-dim expr.dims elem))
       :frame (b* (((when (member-equal 0 expr.dims)) (reserr nil))
                   ((ok vals) (eval-expr-list expr.exprs denv (1- limit)))
                   ((unless (equal (len vals) (nat-list-product expr.dims)))
                    (reserr nil))
                   ((unless (list-repeatp (dims-of-value-list vals)))
                    (reserr nil)))
                (value-with-nonempty-dims expr.dims vals))
       :frame-empty (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
                         ((ok tval) (eval-type expr.type denv))
                         ((mv elem cell-dims)
                          (type-value-case
                           tval
                           :array (mv tval.elem tval.shape)
                           :otherwise (mv tval nil)))
                         ((when (type-value-case elem :array)) (reserr nil))
                         (dims (append expr.dims cell-dims)))
                      (value-with-empty-dim dims elem))
       :string (if (consp expr.chars)
                   (value-vector
                    (value-base-list
                     (base-value-int-list
                      (eval-char-lit-list expr.chars))))
                 (make-value-vector-empty
                  :dims nil
                  :elem (type-value-base (base-type-int))))
       :app (b* (((ok funval) (eval-expr expr.fun denv (1- limit)))
                 ((ok argvals) (eval-expr-list expr.args denv (1- limit))))
              ;; TODO: extend to non-scalar functions
              ;; and framed arguments (lifting)
              (value-case
               funval
               :lambda
               (b* (((unless (values-match-type-values-p
                              argvals
                              (var+typevalue-list->type funval.params)))
                     (reserr nil))
                    (denv (denv-add-expr-vars
                           (var+typevalue-list->var funval.params)
                           argvals
                           denv)))
                 (eval-expr funval.body denv (1- limit)))
               :otherwise (reserr nil)))
       :tapp (b* (((ok funval) (eval-expr expr.fun denv (1- limit)))
                  ((ok tvals) (eval-type-list expr.args denv)))
               (eval-tapp funval tvals denv (1- limit)))
       :iapp (b* (((ok funval) (eval-expr expr.fun denv (1- limit)))
                  ((ok ivals) (eval-ispace-list expr.args denv)))
               (eval-iapp funval ivals denv (1- limit)))
       :capp (reserr :todo)
       :unbox (reserr :todo)
       :bracket (reserr :todo)
       :let (reserr :todo)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-expr-list ((exprs expr-listp) (denv denvp) (limit natp))
    :guard (denv-wfp denv)
    :returns (vals value-list-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate a list of expressions to a list of values."
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

  (define eval-atom ((atom atomp) (denv denvp) (limit natp))
    :returns (val value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate an atom to a value."
    :long
    (xdoc::topstring
     (xdoc::p
      "A base literal is evaluated to a base value,
       which is embedded into a value.")
     (xdoc::p
      "A lambda abstraction evaluates to a lambda value
       with the same parameter variables,
       whose associated types are evaluated to type values;
       the body is not evaluated here,
       but only when the abstraction is applied.")
     (xdoc::p
      "A type lambda abstraction or an ispace lambda abstraction
       evaluates to a type lambda value or an ispace lambda value,
       respectively,
       with the same parameters and body,
       which are not evaluated here but only when the abstraction is applied."))
    (b* (((when (zp limit)) (reserr :limit)))
      (atom-case
       atom
       :base (value-base (eval-base-lit atom.lit))
       :lambda (b* (((ok params) (eval-var+type-list atom.params denv)))
                 (make-value-lambda :params params :body atom.body))
       :tlambda (make-value-tlambda :params atom.params :body atom.body)
       :ilambda (make-value-ilambda :params atom.params :body atom.body)
       :box (reserr :todo)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-atom-list ((atoms atom-listp) (denv denvp) (limit natp))
    :returns (vals value-list-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate a list of atoms to a list of values."
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

  (define eval-bind ((bind bindp) (denv denvp) (limit natp))
    :returns (new-denv denv-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Evaluate a binding, extending the dynamic environment."
    (declare (ignore denv))
    (b* (((when (zp limit)) (reserr :limit)))
      (bind-case
       bind
       :ispace (reserr :todo)
       :type (reserr :todo)
       :val (reserr :todo)
       :fun (reserr :todo)
       :tfun (reserr :todo)
       :ifun (reserr :todo)
       :cfun (reserr :todo)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-bind-list ((binds bind-listp) (denv denvp) (limit natp))
    :returns (new-denv denv-resultp)
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
         ((when (endp binds)) (denv-fix denv))
         ((ok denv) (eval-bind (car binds) denv (1- limit))))
      (eval-bind-list (cdr binds) denv (1- limit)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-tapp ((funval valuep)
                     (tvals type-value-listp)
                     (denv denvp)
                     (limit natp))
    :guard (and (value-wfp funval)
                (denv-wfp denv))
    :returns (val value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Apply a value to type values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called by @(tsee eval-expr) for a type application,
       after the function and the type arguments have been evaluated:
       @('funval') is the value of the function,
       and @('tvals') are the values of the type arguments.")
     (xdoc::p
      "The function value must be an array, of any rank,
       whose elements are type lambda abstractions;
       the type argument values must match
       the parameters in number and kinds.
       Each such lambda abstraction is applied to the type argument values.")
     (xdoc::p
      "This ACL2 function performs that element-wise application.
       The base case is that of a scalar (i.e. 0-rank array) function value:
       we check that the arguments match the parameters,
       we extend the dynamic environment
       to associate the arguments with the parameters
       (which may override existing associations,
       which is intended hiding behavior),
       and we evaluate the body of the type lambda abstraction.")
     (xdoc::p
      "A non-empty vector function value
       is applied via a separate ACL2 function that goes through the list.
       We check that the resulting list of values is not empty
       and that its values all have the same dimensions,
       but this should be eliminable via proofs,
       as we plan to do.
       We return the vector value consisting of the result values.")
     (xdoc::p
      "An empty vector function value has
       no type lambda abstractions to apply,
       but it carries the type of its would-be elements,
       which must be a universal type value;
       the type argument values must match
       its parameters in number and kinds.
       We extend the dynamic environment
       to associate the arguments with the parameters,
       and we evaluate the body of the universal type value,
       which yields the type value of the would-be results
       of the element-wise application.
       Similarly to the evaluation of empty frame expressions
       in @(tsee eval-expr),
       we decompose that type value into
       the atom type value and the dimensions.
       We return the empty vector value
       whose element type value is that atom type value,
       and whose element dimensions are
       the element dimensions of the function value
       followed by the dimensions of the evaluated body of the universal type.
       The implicit leading 0 dimension of the function value
       is also the implicit leading 0 dimension of the result value."))
    (b* (((when (zp limit)) (reserr :limit)))
      (value-case
       funval
       :tlambda
       (b* (((unless (type-values-match-type-vars-p tvals funval.params))
             (reserr nil))
            (denv (denv-add-type-vars funval.params tvals denv)))
         (eval-expr funval.body denv (1- limit)))
       :vector
       (b* (((ok vals) (eval-tapp-list funval.elems tvals denv (1- limit)))
            ;; TODO: eliminate the next two checks via proof
            ((unless (consp vals)) (reserr nil))
            ((unless (list-repeatp (dims-of-value-list vals))) (reserr nil)))
         (value-vector vals))
       :vector-empty
       (type-value-case
        funval.elem
        :forall
        (b* (((unless (type-values-match-type-vars-p tvals funval.elem.params))
              (reserr nil))
             (denv (denv-add-type-vars funval.elem.params tvals denv))
             ((ok tval) (eval-type funval.elem.body denv))
             ((mv elem body-dims)
              (type-value-case
               tval
               :array (mv tval.elem tval.shape)
               :otherwise (mv tval nil)))
             ((when (type-value-case elem :array)) (reserr nil)))
          (make-value-vector-empty :dims (append funval.dims body-dims)
                                   :elem elem))
        :otherwise (reserr nil))
       :otherwise (reserr nil)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-tapp-list ((funvals value-listp)
                          (tvals type-value-listp)
                          (denv denvp)
                          (limit natp))
    :guard (and (value-list-wfp funvals)
                (denv-wfp denv))
    :returns (vals value-list-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Lift @(tsee eval-tapp) to a list of function values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This applies the type values to each element value in turn,
       returning the list of results in the same order.
       It is used to lift type application over
       a vector of type lambda values (see @(tsee eval-tapp))."))
    (b* (((when (zp limit)) (reserr :limit))
         ((when (endp funvals)) nil)
         ((ok val) (eval-tapp (car funvals) tvals denv (1- limit)))
         ((ok vals) (eval-tapp-list (cdr funvals) tvals denv (1- limit))))
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

  (define eval-iapp ((funval valuep)
                     (ivals ispace-value-listp)
                     (denv denvp)
                     (limit natp))
    :guard (and (value-wfp funval)
                (denv-wfp denv))
    :returns (val value-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Apply a value to ispace values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called by @(tsee eval-expr) for an ispace application,
       after the function and the ispace arguments have been evaluated:
       @('funval') is the value of the function,
       and @('ivals') are the values of the ispace arguments.")
     (xdoc::p
      "The function value must be an array, of any rank,
       whose elements are ispace lambda abstractions;
       the ispace argument values must match
       the parameters in number and sorts.
       Each such lambda abstraction is applied to the ispace argument values.")
     (xdoc::p
      "This ACL2 function performs that element-wise application.
       The base case is that of a scalar (i.e. 0-rank array) function value:
       we check that the arguments match the parameters,
       we extend the dynamic environment
       to associate the arguments with the parameters
       (which may override existing associations,
       which is intended hiding behavior),
       and we evaluate the body of the ispace lambda abstraction.")
     (xdoc::p
      "A non-empty vector function value
       is applied via a separate ACL2 function that goes through the list.
       We check that the resulting list of values is not empty
       and that its values all have the same dimensions,
       but this should be eliminable via proofs,
       as we plan to do.
       We return the vector value consisting of the result values.")
     (xdoc::p
      "An empty vector function value has
       no ispace lambda abstractions to apply,
       but it carries the type of its would-be elements,
       which must be a product type value;
       the ispace argument values must match
       its parameters in number and sorts.
       We extend the dynamic environment
       to associate the arguments with the parameters,
       and we evaluate the body of the product type value,
       which yields the type value of the would-be results
       of the element-wise application.
       Similarly to the evaluation of empty frame expressions
       in @(tsee eval-expr),
       we decompose that type value into
       the atom type value and the dimensions.
       We return the empty vector value
       whose element type value is that atom type value,
       and whose element dimensions are
       the element dimensions of the function value
       followed by the dimensions of the evaluated body of the product type.
       The implicit leading 0 dimension of the function value
       is also the implicit leading 0 dimension of the result value."))
    (b* (((when (zp limit)) (reserr :limit)))
      (value-case
       funval
       :ilambda
       (b* (((unless (ispace-values-match-ispace-vars-p ivals funval.params))
             (reserr nil))
            (denv (denv-add-ispace-vars funval.params ivals denv)))
         (eval-expr funval.body denv (1- limit)))
       :vector
       (b* (((ok vals) (eval-iapp-list funval.elems ivals denv (1- limit)))
            ;; TODO: eliminate the next two checks via proof
            ((unless (consp vals)) (reserr nil))
            ((unless (list-repeatp (dims-of-value-list vals))) (reserr nil)))
         (value-vector vals))
       :vector-empty
       (type-value-case
        funval.elem
        :pi
        (b* (((unless (ispace-values-match-ispace-vars-p ivals
                                                         funval.elem.params))
              (reserr nil))
             (denv (denv-add-ispace-vars funval.elem.params ivals denv))
             ((ok tval) (eval-type funval.elem.body denv))
             ((mv elem body-dims)
              (type-value-case
               tval
               :array (mv tval.elem tval.shape)
               :otherwise (mv tval nil)))
             ((when (type-value-case elem :array)) (reserr nil)))
          (make-value-vector-empty :dims (append funval.dims body-dims)
                                   :elem elem))
        :otherwise (reserr nil))
       :otherwise (reserr nil)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-iapp-list ((funvals value-listp)
                          (ivals ispace-value-listp)
                          (denv denvp)
                          (limit natp))
    :guard (and (value-list-wfp funvals)
                (denv-wfp denv))
    :returns (vals value-list-resultp)
    :parents (evaluation eval-exprs/atoms/binds)
    :short "Lift @(tsee eval-iapp) to a list of function values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This applies the ispace values to each element value in turn,
       returning the list of results in the same order.
       It is used to lift ispace application over
       a vector of ispace lambda values (see @(tsee eval-iapp))."))
    (b* (((when (zp limit)) (reserr :limit))
         ((when (endp funvals)) nil)
         ((ok val) (eval-iapp (car funvals) ivals denv (1- limit)))
         ((ok vals) (eval-iapp-list (cdr funvals) ivals denv (1- limit))))
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

  :prepwork ((set-bogus-mutual-recursion-ok t)) ; TODO: remove eventually

  :verify-guards nil ; done below

  ///

  (fty::deffixequiv-mutual eval-exprs/atoms/binds
    :hints (("Goal"
             :expand ((eval-expr expr denv limit)
                      (eval-expr (expr-fix expr) denv limit)
                      (eval-expr expr (denv-fix denv) limit)
                      (eval-expr-list exprs denv limit)
                      (eval-expr-list (expr-list-fix exprs) denv limit)
                      (eval-expr-list exprs (denv-fix denv) limit)
                      (eval-atom atom denv limit)
                      (eval-atom (atom-fix atom) denv limit)
                      (eval-atom atom (denv-fix denv) limit)
                      (eval-atom-list atoms denv limit)
                      (eval-atom-list (atom-list-fix atoms) denv limit)
                      (eval-atom-list atoms (denv-fix denv) limit)
                      (eval-bind bind denv limit)
                      (eval-bind (bind-fix bind) denv limit)
                      (eval-bind bind (denv-fix denv) limit)
                      (eval-bind-list binds denv limit)
                      (eval-bind-list (bind-list-fix binds) denv limit)
                      (eval-bind-list binds (denv-fix denv) limit)
                      (eval-tapp funval tvals denv limit)
                      (eval-tapp (value-fix funval) tvals denv limit)
                      (eval-tapp funval (type-value-list-fix tvals) denv limit)
                      (eval-tapp funval tvals (denv-fix denv) limit)
                      (eval-tapp-list funvals tvals denv limit)
                      (eval-tapp-list (value-list-fix funvals)
                                      tvals denv limit)
                      (eval-tapp-list funvals
                                      (type-value-list-fix tvals) denv limit)
                      (eval-tapp-list funvals tvals (denv-fix denv) limit)
                      (eval-iapp funval ivals denv limit)
                      (eval-iapp (value-fix funval) ivals denv limit)
                      (eval-iapp funval
                                 (ispace-value-list-fix ivals) denv limit)
                      (eval-iapp funval ivals (denv-fix denv) limit)
                      (eval-iapp-list funvals ivals denv limit)
                      (eval-iapp-list (value-list-fix funvals)
                                      ivals denv limit)
                      (eval-iapp-list funvals
                                      (ispace-value-list-fix ivals) denv limit)
                      (eval-iapp-list funvals ivals (denv-fix denv) limit))
             :in-theory (enable nfix zp))))

  (defret-mutual value-wfp-of-eval-exprs/atoms/binds
    (defret value-wfp-of-eval-expr
      (implies (and (denv-wfp denv)
                    (not (reserrp val)))
               (value-wfp val))
      :fn eval-expr)
    (defret value-list-wfp-of-eval-expr-list
      (implies (and (denv-wfp denv)
                    (not (reserrp vals)))
               (value-list-wfp vals))
      :fn eval-expr-list)
    (defret value-wfp-of-eval-atom
      (implies (and (denv-wfp denv)
                    (not (reserrp val)))
               (value-wfp val))
      :fn eval-atom)
    (defret value-list-wfp-of-eval-atom-list
      (implies (and (denv-wfp denv)
                    (not (reserrp vals)))
               (value-list-wfp vals))
      :fn eval-atom-list)
    (defret denv-wfp-of-eval-bind
      (implies (and (denv-wfp denv)
                    (not (reserrp new-denv)))
               (denv-wfp new-denv))
      :fn eval-bind)
    (defret denv-wfp-of-eval-bind-list
      (implies (and (denv-wfp denv)
                    (not (reserrp new-denv)))
               (denv-wfp new-denv))
      :fn eval-bind-list)
    (defret value-wfp-of-eval-tapp
      (implies (and (denv-wfp denv)
                    (not (reserrp val)))
               (value-wfp val))
      :fn eval-tapp)
    (defret value-list-wfp-of-eval-tapp-list
      (implies (and (denv-wfp denv)
                    (not (reserrp vals)))
               (value-list-wfp vals))
      :fn eval-tapp-list)
    (defret value-wfp-of-eval-iapp
      (implies (and (denv-wfp denv)
                    (not (reserrp val)))
               (value-wfp val))
      :fn eval-iapp)
    (defret value-list-wfp-of-eval-iapp-list
      (implies (and (denv-wfp denv)
                    (not (reserrp vals)))
               (value-list-wfp vals))
      :fn eval-iapp-list)
    :mutual-recursion eval-exprs/atoms/binds
    :hints
    (("Goal"
      :in-theory (enable value-wfp-of-cdr-of-assoc-when-denv-wfp
                         nfix
                         zp)
      :expand ((eval-expr expr denv limit)
               (eval-expr-list exprs denv limit)
               (eval-atom atom denv limit)
               (eval-atom-list atoms denv limit)
               (eval-bind bind denv limit)
               (eval-bind-list binds denv limit)
               (eval-tapp funval tvals denv limit)
               (eval-tapp-list funvals tvals denv limit)
               (eval-iapp funval ivals denv limit)
               (eval-iapp-list funvals ivals denv limit)))))

  (verify-guards eval-expr
    :hints
    (("Goal"
      :in-theory (e/d (len-equal-when-values-match-type-values-p)
                      (len-of-eval-expr-list))))))
