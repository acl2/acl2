; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-values-and-environments")
(include-book "type-values-and-environments")
(include-book "abstract-syntax-structurals")
(include-book "base-values")
(include-book "unit-types")
(include-book "nat-lists")

(include-book "kestrel/fty/nat-list-list-list" :dir :system)
(include-book "kestrel/fty/nat-list-result" :dir :system)
(include-book "kestrel/fty/nat-list-list-result" :dir :system)
(include-book "std/typed-lists/cons-listp" :dir :system)

(local (include-book "arithmetic"))

(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable acl2::nat-listp-when-result-not-error
                          acl2::nat-list-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ expression-values-and-environments
  :parents (dynamic-semantics)
  :short "Expression values and expression dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "Expressions (ASTs), and atoms with them, evaluate to expression values.
     Expression dynamic environments capture
     the expression variables in scope
     and their associated expression values.")
   (xdoc::p
    "Expression values include representations for primitive operations.
     By `primitive operation' we mean
     a built-in Remora function
     that is not implemented in Remora
     and that is implicitly in scope (unless overwritten).
     Syntactically, it is a variable,
     whose value is the reification of the operation.
     We represent this as a special kind of expression value,
     which includes not only the ``full'' operations,
     but also partially instantiated forms of those operations;
     the latter are essentially closures.
     See @(tsee primop-value) for details and examples.")
   (xdoc::p
    "The term `primitive' comes from [thesis], [arxiv], and [esop].
     Instead, [impl] uses the terms `primitive' and `intrinsic':
     the first for the ones on integer and similar types,
     and the second for the ones on lists and similar types.
     The latter are polymorphic while the former are monomorphic,
     but that division is not the explicit intention in [impl]."))
  :order-subtopics (base-values
                    t)
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum int-unary-primop
  :short "Fixtype of integer unary primitive operations."
  (:bit-not ())
  (:popc ())
  :pred int-unary-primop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum int-binary-primop
  :short "Fixtype of integer binary primitive operations."
  (:add ())
  (:sub ())
  (:mul ())
  (:div ())
  (:expt ())
  (:mod ())
  (:max ())
  (:min ())
  (:bit-and ())
  (:bit-or ())
  (:bit-xor ())
  (:shl ())
  (:shr ())
  :pred int-binary-primop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum int-rel-primop
  :short "Fixtype of integer relational primitive operations."
  (:eq ())
  (:neq ())
  (:lt ())
  (:gt ())
  (:leq ())
  (:geq ())
  :pred int-rel-primop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum float-unary-primop
  :short "Fixtype of float unary primitive operations."
  (:sqrt ())
  :pred float-unary-primop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum float-binary-primop
  :short "Fixtype of float binary primitive operations."
  (:add ())
  (:sub ())
  (:mul ())
  (:div ())
  (:expt ())
  (:max ())
  (:min ())
  :pred float-binary-primop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum float-rel-primop
  :short "Fixtype of float relational primitive operations."
  (:eq ())
  (:neq ())
  (:lt ())
  (:gt ())
  (:leq ())
  (:geq ())
  :pred float-rel-primop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bool-unary-primop
  :short "Fixtype of boolean unary primitive operations."
  (:not ())
  :pred bool-unary-primop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bool-binary-primop
  :short "Fixtype of boolean binary primitive operations."
  (:and ())
  (:or ())
  :pred bool-binary-primop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bool-rel-primop
  :short "Fixtype of boolean relational primitive operations."
  (:eq ())
  (:neq ())
  :pred bool-rel-primop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes expr-values/denv
  :short "Fixtypes of expression values and expression dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "Expression values and expression dynamic environments
     are mutually recursive because
     some expression values are closures that contain dynamic environments."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum expr-value
    :parents (expression-values-and-environments expr-values/denv)
    :short "Fixtype of expression values."
    :long
    (xdoc::topstring
     (xdoc::p
      "In Remora, every value that an expression may evaluate to is an array.
       Scalar values are zero-rank arrays, consisting of single atom values,
       but we do not define a distinct notion of atom value,
       folding them into the first six summands of
       this fixtype of expression values
       (described in more detail below).
       Non-scalar values are positive-rank arrays,
       consisting of zero or more expression values of rank immediately lower
       (i.e. the rank of the containing array decremented by one);
       we call non-scalars `vectors' in our model of expression values.
       A one-dimensional array is a vector of scalars,
       a two-dimensional array is a vector of one-dimensional arrays,
       and so on.
       We treat empty vectors separately:
       they carry their own type,
       in the form of
       (i) a list of the dimensions of its elements
       (not the dimensions of the whole vector,
       which is obtained by adding a 0 dimension
       in front of the elements' dimensions;
       see @(tsee check-dims-of-expr-value))
       and (ii) an (atom) type value;
       together, (i) and (ii) determine
       the array type of the expression value.")
     (xdoc::p
      "The atoms that form scalar values are
       base values,
       primitive operations,
       lambda abstractions,
       and boxed values.
       Scalar values correspond to atom values @($\\mathit{Atval}$) in [thesis].
       The primitive operations
       (the @(':primop') summand, see @(tsee primop-value))
       correspond to @($\\mathfrak{o}$) in [thesis];
       the difference is that, in our ASTs, as in [impl],
       primitive operations are not a dedicated kind of atom,
       but are represented as variables
       whose predefined values are these @(':primop') expression values.
       However, as already noted,
       we fold atom values into (array) expression values.
       Our fixtype of expression values loosely corresponds
       to @($\\mathit{Val}$) in [thesis],
       but with a different yet equivalent structure.")
     (xdoc::p
      "The parameter of a lambda value associates
       a type value, not a type, to the variable:
       the parameter type is evaluated
       when the lambda abstraction is evaluated,
       while the body is evaluated
       when the lambda abstraction is applied.
       The same goes for the optional type of the body of the lambda value,
       which mirrors the one in the AST for lambda abstraction atoms;
       it is present only when the lambda value binds
       the innermost parameter of a lambda abstraction
       (see below), which is the one whose body carries the annotation.")
     (xdoc::p
      "All three kinds of lambda values bind exactly one parameter:
       consistently with the curried view of
       ispace, type, and term applications
       (see @(tsee expr)),
       a lambda abstraction with two or more parameters
       evaluates to the unary lambda value
       that binds the first parameter,
       whose body is the lambda abstraction
       over the remaining parameters.")
     (xdoc::p
      "This fixtype does not capture constraints like
       the non-emptiness of the expression value list in @(':vector'),
       and the dimension and type consistency of the elements of a @(':vector').
       These constraints are captured separately.")
     (xdoc::p
      "Critically, all three kinds of lambda abstractions contain
       environments for their free ispace, type, and expression variables.
       This fixtype currently does not enforce the constraint that
       the environment contains exactly those free variables."))
    (:base ((val base-value)))
    (:primop ((val primop-value)))
    (:lambda ((param var+typevalue)
              (body expr)
              (type? type-value-option)
              (denv expr-denv)))
    (:tlambda ((param type-var)
               (body expr)
               (denv expr-denv)))
    (:ilambda ((param ispace-var)
               (body expr)
               (denv expr-denv)))
    (:box ((ispaces ispace-value-list)
           (array expr-value)
           (type type-value)))
    (:vector ((elems expr-value-list)))
    (:vector-empty ((dims nat-list)
                    (elem type-value)))
    :pred expr-valuep
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist expr-value-list
    :parents (expression-values-and-environments expr-values/denv)
    :short "Fixtype of lists of expression values."
    :elt-type expr-value
    :true-listp t
    :elementp-of-nil nil
    :pred expr-value-listp
    :measure (two-nats-measure (acl2-count x) 0)

    ///

    (defrule expr-value-listp-of-repeat-each
      (implies (expr-value-listp vals)
               (expr-value-listp (repeat-each n vals)))
      :induct (repeat-each n vals)
      :enable (repeat-each expr-value-listp)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum primop-value
    :parents (expression-values-and-environments expr-values/denv)
    :short "Fixtype of primitive operation values."
    :long
    (xdoc::topstring
     (xdoc::p
      "A value of this fixtype represents a primitive operation,
       or an instantiation stage thereof,
       as a scalar (zero-rank array) function value,
       analogously to how the three kinds of lambda abstractions
       are scalar function values.
       These are incorporated into @(tsee expr-value)
       as its @(':primop') summand.")
     (xdoc::p
      "Since the Remora primitive operations are curried,
       there are as many stages as there are parameters:
       the first stage stores no parameter values,
       and the last stage stores all but the last parameter values.
       Each application moves from one stage to the next;
       the final application is on the last parameter value,
       so all parameter values are available.")
     (xdoc::p
      "For example, here are the stages of @('length'):
       @(':length') is the uninstantiated operation;
       @(':length-t') is the operation applied to
       a type value for its type parameter;
       @(':length-t-d') is the operation further applied to
       a natural number for its dimension parameter;
       @(':length-t-d-s') is the operation further applied to
       a list of natural numbers for its shape parameter.
       As another example, here are the stages of integer binary operations:
       @(':int-binary') is the uninstantiated operation;
       @(':int-binary-x') is the operation applied to
       its first argument value
       (which we call @('x'), based on the idea that
       the two arguments are @('x') and @('y').")
     (xdoc::p
      "Not every polymorphic operation has a stage for every kind of value.
       For example, @('sum') is monomorphic in the element type,
       which is always integer,
       so it has no type stage:
       @(':sum') is the uninstantiated operation, and
       @(':sum-s') is the operation applied to
       a list of natural numbers for its shape parameter."))
    (:int-unary ((op int-unary-primop)))
    (:int-binary ((op int-binary-primop)))
    (:int-binary-x ((op int-binary-primop)
                    (xval expr-value)))
    (:int-rel ((op int-rel-primop)))
    (:int-rel-x ((op int-rel-primop)
                 (xval expr-value)))
    (:int-to-float ())
    (:int-to-bool ())
    (:float-unary ((op float-unary-primop)))
    (:float-binary ((op float-binary-primop)))
    (:float-binary-x ((op float-binary-primop)
                      (xval expr-value)))
    (:float-rel ((op float-rel-primop)))
    (:float-rel-x ((op float-rel-primop)
                   (xval expr-value)))
    (:float-truncate ())
    (:float-round ())
    (:float-ceiling ())
    (:float-floor ())
    (:bool-unary ((op bool-unary-primop)))
    (:bool-binary ((op bool-binary-primop)))
    (:bool-binary-x ((op bool-binary-primop)
                     (xval expr-value)))
    (:bool-rel ((op bool-rel-primop)))
    (:bool-rel-x ((op bool-rel-primop)
                  (xval expr-value)))
    (:bool-to-int ())
    (:bool-to-float ())
    (:head ())
    (:head-t ((tval type-value)))
    (:head-t-d ((tval type-value)
                (dval nat)))
    (:head-t-d-s ((tval type-value)
                  (dval nat)
                  (sval nat-list)))
    (:tail ())
    (:tail-t ((tval type-value)))
    (:tail-t-d ((tval type-value)
                (dval nat)))
    (:tail-t-d-s ((tval type-value)
                  (dval nat)
                  (sval nat-list)))
    (:length ())
    (:length-t ((tval type-value)))
    (:length-t-d ((tval type-value)
                  (dval nat)))
    (:length-t-d-s ((tval type-value)
                    (dval nat)
                    (sval nat-list)))
    (:append ())
    (:append-t ((tval type-value)))
    (:append-t-m ((tval type-value)
                  (mval nat)))
    (:append-t-m-n ((tval type-value)
                    (mval nat)
                    (nval nat)))
    (:append-t-m-n-s ((tval type-value)
                      (mval nat)
                      (nval nat)
                      (sval nat-list)))
    (:append-t-m-n-s-x ((tval type-value)
                        (mval nat)
                        (nval nat)
                        (sval nat-list)
                        (xval expr-value)))
    (:reverse ())
    (:reverse-t ((tval type-value)))
    (:reverse-t-d ((tval type-value)
                   (dval nat)))
    (:reverse-t-d-s ((tval type-value)
                     (dval nat)
                     (sval nat-list)))
    (:index ())
    (:index-t ((tval type-value)))
    (:index-t-m ((tval type-value)
                 (mval nat)))
    (:index-t-m-x ((tval type-value)
                   (mval nat)
                   (xval expr-value)))
    (:index2d ())
    (:index2d-t ((tval type-value)))
    (:index2d-t-m ((tval type-value)
                   (mval nat)))
    (:index2d-t-m-n ((tval type-value)
                     (mval nat)
                     (nval nat)))
    (:index2d-t-m-n-x ((tval type-value)
                       (mval nat)
                       (nval nat)
                       (xval expr-value)))
    (:sum ())
    (:sum-s ((sval nat-list)))
    :pred primop-valuep
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defomap string-expr-value-map
    :parents (expression-values-and-environments expr-values/denv)
    :short "Fixtype of maps from strings to expression values."
    :key-type string
    :val-type expr-value
    :pred string-expr-value-mapp
    :measure (two-nats-measure (acl2-count x) 0)

    ///

    (defrule string-expr-value-mapp-of-restrict
      (implies (string-expr-value-mapp map)
               (string-expr-value-mapp (omap::restrict keys map)))
      :induct t
      :enable omap::restrict))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod expr-denv
    :parents (expression-values-and-environments expr-values/denv)
    :short "Fixtype of expression dynamic environments."
    :long
    (xdoc::topstring
     (xdoc::p
      "This includes a type dynamic environment,
       because expressions contain types;
       and the type dynamic environment includes an ispace dynamic environment.
       Additionally,
       we have a map from expression variables to expression values,
       which are the expression variables in scope
       with the associated values."))
    ((tenv type-denv)
     (exprs string-expr-value-map))
    :pred expr-denvp
    :measure (two-nats-measure (acl2-count x) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-value-base-list ((x base-value-listp))
  :returns (vals expr-value-listp)
  :short "Lift @(tsee expr-value-base) to lists."
  (expr-value-base x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption expr-value-option
  expr-value
  :short "Fixtype of optional expression values."
  :pred expr-value-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist expr-value-list-list
  :short "Fixtype of lists of lists of expression values."
  :elt-type expr-value-list
  :true-listp t
  :elementp-of-nil t
  :pred expr-value-list-listp

  ///

  (defruled true-list-listp-when-expr-value-list-listp
    (implies (expr-value-list-listp x)
             (true-list-listp x))
    :induct t
    :enable true-list-listp)

  (defrule expr-value-list-listp-of-list-split
    (implies (and (expr-value-listp vals)
                  (posp n)
                  (integerp (/ (len vals) n)))
             (expr-value-list-listp (list-split vals n)))
    :induct t
    :enable (list-split
             expr-value-list-listp
             lt-to-zero-when-divided-by-pos
             nfix
             posp)
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defrule expr-value-listp-of-car-list
    (implies (expr-value-list-listp x)
             (equal (expr-value-listp (car-list x))
                    (cons-listp x)))
    :induct t
    :enable car-list)

  (defrule expr-value-list-listp-of-cdr-list
    (implies (expr-value-list-listp x)
             (expr-value-list-listp (cdr-list x)))
    :induct t
    :enable cdr-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult expr-value-result
  :short "Fixtype of expression values and errors."
  :ok expr-value
  :pred expr-value-resultp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult expr-value-list-result
  :short "Fixtype of (i) lists of expression values and (ii) errors."
  :ok expr-value-list
  :pred expr-value-list-resultp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult expr-value-list-list-result
  :short "Fixtype of (i) lists of lists of expression values and (ii) errors."
  :ok expr-value-list-list
  :pred expr-value-list-list-resultp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult expr-denv-result
  :short "Fixtype of expression dynamic environments and errors."
  :ok expr-denv
  :pred expr-denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-dims-of-expr-values/denv
  :short "Check dimension constraints on
          expression values and expression dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "As discussed in @(tsee expr-value),
     that fixtype does not capture many of the constraints of expression values.
     We do that in these functions,
     which also return the dimensions of the expression values
     if the expression values satisfy the constraints:
     the dimensions are needed to check the containing expression values.
     So these functions define, simultaneously,
     predicates on expression values saying whether
     the expression values are well-formed,
     and functions returning dimensions of well-formed expression values.")
   (xdoc::p
    "Since expression values are mutually recursive
     with expression dynamic environments,
     these functions also operate on the latter,
     because they need to check the expression values inside them.
     But an environment as such does not have dimensions,
     so no dimensions are returned by the checking function on environments
     (and on the underlying maps).")
   (xdoc::p
    "Since expression values are mutually recursive
     with primitive operation values,
     these functions also operate on the latter.
     Although these are always scalars,
     we still need to check the well-formedness
     of the expression values stored in them.
     As done with environment, no dimensions are returned."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dims-of-expr-value ((val expr-valuep))
    :returns (dims nat-list-resultp)
    :parents (expression-values-and-environments check-dims-of-expr-values/denv)
    :short "Check dimension constraints on expression values."
    :long
    (xdoc::topstring
     (xdoc::p
      "Base and abstraction values always satisfy dimension constraints
       and have the empty list of dimensions.
       Primitive operation values also have the empty list of dimensions,
       but the expression values stored in their instantiation stages, if any,
       must satisfy the dimension constraints
       (see @(tsee check-dims-of-primop-value)).
       Box values also have the empty list of dimensions,
       but their boxed value must satisfy the dimension constraints.")
     (xdoc::p
      "For a (non-empty) vector, there must be at least one element.
       We recursively check its element expression values,
       obtaining a list of lists of dimensions, in the same order.
       All the lists of dimensions in the list must be the same,
       i.e. all the elements must have the same dimensions.
       Then the dimensions of the vector value are obtained
       by adding the number of elements of the vector to
       the list of dimensions of all the elements.
       For instance, if a vector has 2 elements,
       each of which is a 3x4 matrix,
       the vector value is a 2x3x4 tensor.")
     (xdoc::p
      "An empty vector, as noted in @(tsee expr-value),
       carries the dimensions of its non-existent elements,
       which otherwise could not be determined.
       The dimensions of the whole vector are obtained
       by adding 0 in front of the elements' dimensions.
       It may seem strange to have dimensions for non-existent elements,
       but that matches the Remora type system:
       in particular, the syntax for empty arrays."))
    (expr-value-case
     val
     :base nil
     :primop (b* (((ok &) (check-dims-of-primop-value val.val)))
               nil)
     :lambda (b* (((ok &) (check-dims-of-expr-denv val.denv)))
               nil)
     :tlambda (b* (((ok &) (check-dims-of-expr-denv val.denv)))
                nil)
     :ilambda (b* (((ok &) (check-dims-of-expr-denv val.denv)))
                nil)
     :box (b* (((ok &) (check-dims-of-expr-value val.array)))
            nil)
     :vector (b* (((ok dimss) (check-dims-of-expr-value-list val.elems))
                  ((unless (consp dimss)) (reserr nil))
                  ((unless (list-repeatp dimss)) (reserr nil)))
               (cons (len val.elems) (car dimss)))
     :vector-empty (cons 0 val.dims))
    :measure (expr-value-count val))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dims-of-expr-value-list ((vals expr-value-listp))
    :returns (dimss nat-list-list-resultp)
    :parents (expression-values-and-environments check-dims-of-expr-values/denv)
    :short "Check dimension constraints on lists of expression values."
    :long
    (xdoc::topstring
     (xdoc::p
      "Each list element is checked in turn.
       If they all check successfully,
       we return the dimensions of each, in the same order as the list."))
    (b* (((when (endp vals)) nil)
         ((ok dims) (check-dims-of-expr-value (car vals)))
         ((ok dimss) (check-dims-of-expr-value-list (cdr vals))))
      (cons dims dimss))
    :measure (expr-value-list-count vals)

    ///

    (defret consp-of-check-dims-of-expr-value-list-when-not-error
      (implies (not (reserrp dimss))
               (equal (consp dimss)
                      (consp vals)))
      :hints (("Goal"
               :induct (len vals)
               :in-theory (enable len))))

    (defret len-of-check-dims-of-expr-value-list-when-not-error
      (implies (not (reserrp dimss))
               (equal (len dimss)
                      (len vals)))
      :hints (("Goal"
               :induct (len vals)
               :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dims-of-primop-value ((val primop-valuep))
    :returns (unit unit-resultp)
    :parents (expression-values-and-environments check-dims-of-expr-values/denv)
    :short "Check dimension constraints on primitive operation values."
    (primop-value-case
     val
     :int-binary-x (b* (((ok &) (check-dims-of-expr-value val.xval)))
                     :unit)
     :int-rel-x (b* (((ok &) (check-dims-of-expr-value val.xval)))
                  :unit)
     :float-binary-x (b* (((ok &) (check-dims-of-expr-value val.xval)))
                       :unit)
     :float-rel-x (b* (((ok &) (check-dims-of-expr-value val.xval)))
                    :unit)
     :bool-binary-x (b* (((ok &) (check-dims-of-expr-value val.xval)))
                      :unit)
     :bool-rel-x (b* (((ok &) (check-dims-of-expr-value val.xval)))
                   :unit)
     :append-t-m-n-s-x (b* (((ok &) (check-dims-of-expr-value val.xval)))
                         :unit)
     :index-t-m-x (b* (((ok &) (check-dims-of-expr-value val.xval)))
                    :unit)
     :index2d-t-m-n-x (b* (((ok &) (check-dims-of-expr-value val.xval)))
                        :unit)
     :otherwise :unit)
    :measure (primop-value-count val))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dims-of-string-expr-value-map ((map string-expr-value-mapp))
    :returns (unit unit-resultp)
    :parents (expression-values-and-environments check-dims-of-expr-values/denv)
    :short "Check dimension constraints on (the expression values in)
            a map from strings to expression values."
    (b* (((when (omap::emptyp (string-expr-value-map-fix map))) :unit)
         (eval (omap::head-val map))
         ((ok &) (check-dims-of-expr-value eval))
         ((ok &) (check-dims-of-string-expr-value-map (omap::tail map))))
      :unit)
    :measure (string-expr-value-map-count map))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dims-of-expr-denv ((denv expr-denvp))
    :returns (unit unit-resultp)
    :parents (expression-values-and-environments check-dims-of-expr-values/denv)
    :short "Check dimension constraints on (the expression values in)
            an expression dynamic environment."
    (check-dims-of-string-expr-value-map (expr-denv->exprs denv))
    :measure (expr-denv-count denv))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork
  ((local (in-theory (enable acl2::true-listp-when-nat-list-listp
                             acl2::nat-listp-of-car-when-nat-list-listp))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual check-dims-of-expr-values/denv)

  (defruled check-dims-of-expr-value-list-of-repeat
    (b* ((dims (check-dims-of-expr-value val))
         (dimss (check-dims-of-expr-value-list (repeat n val))))
      (implies (not (reserrp dims))
               (and (not (reserrp dimss))
                    (equal dimss (repeat n dims)))))
    :induct (repeat n dims)
    :enable (repeat
             acl2::not-reserrp-when-nat-list-listp))

  (defruled check-dims-of-expr-value-list-of-expr-value-base-list
    (equal (check-dims-of-expr-value-list (expr-value-base-list bvals))
           (repeat (len bvals) nil))
    :induct (expr-value-base-list bvals)
    :enable (expr-value-base-list
             check-dims-of-expr-value-list
             check-dims-of-expr-value
             repeat
             len
             acl2::not-reserrp-when-nat-list-listp)
    :prep-books ((local (include-book "arithmetic-3/top" :dir :system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-value-wfp ((val expr-valuep))
  :returns (yes/no booleanp)
  :short "Check if an expression value is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expression value must satisfy the dimension constraints.
     We will extend this to also add the satisfaction of type constraints."))
  (not (reserrp (check-dims-of-expr-value val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expr-value-list-wfp (x)
  :guard (expr-value-listp x)
  :short "Lift @(tsee expr-value-wfp) to lists."
  (expr-value-wfp x)

  ///

  (defruled expr-value-list-wfp-alt-def
    (equal (expr-value-list-wfp x)
           (not (reserrp (check-dims-of-expr-value-list x))))
    :induct t
    :enable (check-dims-of-expr-value-list
             expr-value-wfp
             acl2::not-reserrp-when-nat-list-listp))

  (defrule expr-value-list-wfp-of-repeat-each
    (implies (expr-value-list-wfp vals)
             (expr-value-list-wfp (repeat-each n vals)))
    :induct (repeat-each n vals)
    :enable (repeat-each expr-value-list-wfp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expr-value-list-list-wfp (x)
  :guard (expr-value-list-listp x)
  :short "Lift @(tsee expr-value-list-wfp) to lists."
  (expr-value-list-wfp x)

  ///

  (defrule expr-value-list-list-wfp-of-list-split
    (implies (expr-value-list-wfp vals)
             (expr-value-list-list-wfp (list-split vals n)))
    :induct t
    :enable list-split))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-value-wfp ((val primop-valuep))
  :returns (yes/no booleanp)
  :short "Check if a primitive operation value is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The primitive operation value must satisfy the dimension constraints."))
  (not (reserrp (check-dims-of-primop-value val)))

  ///

  (defrule expr-value-wfp-of-x-stage-xvals
    (and (implies (primop-value-case op :int-binary-x)
                  (equal (expr-value-wfp (primop-value-int-binary-x->xval op))
                         (primop-value-wfp op)))
         (implies (primop-value-case op :int-rel-x)
                  (equal (expr-value-wfp (primop-value-int-rel-x->xval op))
                         (primop-value-wfp op)))
         (implies (primop-value-case op :float-binary-x)
                  (equal (expr-value-wfp
                          (primop-value-float-binary-x->xval op))
                         (primop-value-wfp op)))
         (implies (primop-value-case op :float-rel-x)
                  (equal (expr-value-wfp (primop-value-float-rel-x->xval op))
                         (primop-value-wfp op)))
         (implies (primop-value-case op :bool-binary-x)
                  (equal (expr-value-wfp (primop-value-bool-binary-x->xval op))
                         (primop-value-wfp op)))
         (implies (primop-value-case op :bool-rel-x)
                  (equal (expr-value-wfp (primop-value-bool-rel-x->xval op))
                         (primop-value-wfp op)))
         (implies (primop-value-case op :append-t-m-n-s-x)
                  (equal (expr-value-wfp
                          (primop-value-append-t-m-n-s-x->xval op))
                         (primop-value-wfp op)))
         (implies (primop-value-case op :index-t-m-x)
                  (equal (expr-value-wfp (primop-value-index-t-m-x->xval op))
                         (primop-value-wfp op)))
         (implies (primop-value-case op :index2d-t-m-n-x)
                  (equal (expr-value-wfp
                          (primop-value-index2d-t-m-n-x->xval op))
                         (primop-value-wfp op))))
    :enable (primop-value-wfp expr-value-wfp)
    :expand ((check-dims-of-primop-value op)))

  (defrule primop-value-wfp-of-x-stage-constructors
    (and (equal (primop-value-wfp (primop-value-int-binary-x op xval))
                (expr-value-wfp xval))
         (equal (primop-value-wfp (primop-value-int-rel-x op xval))
                (expr-value-wfp xval))
         (equal (primop-value-wfp (primop-value-float-binary-x op xval))
                (expr-value-wfp xval))
         (equal (primop-value-wfp (primop-value-float-rel-x op xval))
                (expr-value-wfp xval))
         (equal (primop-value-wfp (primop-value-bool-binary-x op xval))
                (expr-value-wfp xval))
         (equal (primop-value-wfp (primop-value-bool-rel-x op xval))
                (expr-value-wfp xval))
         (equal (primop-value-wfp
                 (primop-value-append-t-m-n-s-x tval mval nval sval xval))
                (expr-value-wfp xval))
         (equal (primop-value-wfp (primop-value-index-t-m-x tval mval xval))
                (expr-value-wfp xval))
         (equal (primop-value-wfp
                 (primop-value-index2d-t-m-n-x tval mval nval xval))
                (expr-value-wfp xval)))
    :enable (primop-value-wfp expr-value-wfp)
    :expand ((check-dims-of-primop-value (primop-value-int-binary-x op xval))
             (check-dims-of-primop-value (primop-value-int-rel-x op xval))
             (check-dims-of-primop-value (primop-value-float-binary-x op xval))
             (check-dims-of-primop-value (primop-value-float-rel-x op xval))
             (check-dims-of-primop-value (primop-value-bool-binary-x op xval))
             (check-dims-of-primop-value (primop-value-bool-rel-x op xval))
             (check-dims-of-primop-value
              (primop-value-append-t-m-n-s-x tval mval nval sval xval))
             (check-dims-of-primop-value
              (primop-value-index-t-m-x tval mval xval))
             (check-dims-of-primop-value
              (primop-value-index2d-t-m-n-x tval mval nval xval)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-expr-value-map-wfp ((map string-expr-value-mapp))
  :returns (yes/no booleanp)
  :short "Check that all the expression values
          in a string-to-expression-value map
          are well-formed."
  (or (omap::emptyp (string-expr-value-map-fix map))
      (and (expr-value-wfp (omap::head-val map))
           (string-expr-value-map-wfp (omap::tail map))))

  ///

  (defruled string-expr-value-map-wfp-alt-def
    (equal (string-expr-value-map-wfp map)
           (not (reserrp (check-dims-of-string-expr-value-map map))))
    :induct t
    :enable (expr-value-wfp
             check-dims-of-string-expr-value-map))

  (defruled expr-value-wfp-of-cdr-of-assoc-when-string-expr-value-map-wfp
    (implies (and (string-expr-value-mapp map)
                  (string-expr-value-map-wfp map)
                  (omap::assoc key map))
             (expr-value-wfp (cdr (omap::assoc key map))))
    :induct t
    :enable omap::assoc)

  (defruled string-expr-value-map-wfp-of-update
    (implies (and (string-expr-value-mapp map)
                  (string-expr-value-map-wfp map)
                  (expr-value-wfp val))
             (string-expr-value-map-wfp (omap::update key val map)))
    :induct (string-expr-value-map-wfp map)
    :expand ((string-expr-value-map-wfp (omap::update key val map))))

  (defruled string-expr-value-map-wfp-of-restrict
    (implies (and (string-expr-value-mapp map)
                  (string-expr-value-map-wfp map))
             (string-expr-value-map-wfp (omap::restrict keys map)))
    :induct t
    :enable (omap::restrict
             string-expr-value-map-wfp
             string-expr-value-map-wfp-of-update)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-denv-wfp ((denv expr-denvp))
  :returns (yes/no booleanp)
  :short "Check that the expression values in an expression dynamic environment
          are well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an initial notion of well-formedness,
     concerning just the expression values bound to expression variables.
     We may extend it, or fold it into a broader notion,
     when we introduce well-formedness conditions
     on the ispace and type variables as well."))
  (string-expr-value-map-wfp (expr-denv->exprs denv))

  ///

  (defruled expr-denv-wfp-alt-def
    (equal (expr-denv-wfp denv)
           (not (reserrp (check-dims-of-expr-denv denv))))
    :enable (check-dims-of-expr-denv
             string-expr-value-map-wfp-alt-def))

  (defruled expr-value-wfp-of-cdr-of-assoc-when-expr-denv-wfp
    (implies (and (expr-denv-wfp denv)
                  (omap::assoc key (expr-denv->exprs denv)))
             (expr-value-wfp (cdr (omap::assoc key (expr-denv->exprs denv)))))
    :enable (expr-denv-wfp
             expr-value-wfp-of-cdr-of-assoc-when-string-expr-value-map-wfp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dims-of-expr-value ((val expr-valuep))
  :guard (expr-value-wfp val)
  :returns (dims nat-listp :hints (("Goal" :in-theory (enable expr-value-wfp))))
  :short "Dimensions of a well-formed expression value."
  (if (mbt (expr-value-wfp val))
      (check-dims-of-expr-value val)
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection dims-of-expr-value-list ((x expr-value-listp))
  :guard (expr-value-list-wfp x)
  :returns (dimss nat-list-listp)
  :short "Lift @(tsee dims-of-expr-value) to lists."
  (dims-of-expr-value x)
  :nil-preservingp t

  ///

  (defruled dims-of-expr-value-list-of-cdr
    (equal (dims-of-expr-value-list (cdr vals))
           (cdr (dims-of-expr-value-list vals))))

  (theory-invariant (incompatible (:rewrite dims-of-expr-value-list-of-cdr)
                                  (:rewrite cdr-of-dims-of-expr-value-list)))

  (defrule dims-of-expr-value-list-of-repeat
    (equal (dims-of-expr-value-list (repeat n val))
           (repeat n (dims-of-expr-value val)))
    :induct t
    :enable repeat)

  (defruled dims-of-expr-value-list-when-expr-value-list-wfp
    (implies (expr-value-list-wfp vals)
             (equal (dims-of-expr-value-list vals)
                    (check-dims-of-expr-value-list vals)))
    :induct t
    :enable (dims-of-expr-value-list
             check-dims-of-expr-value-list
             expr-value-list-wfp
             dims-of-expr-value
             expr-value-wfp
             acl2::not-reserrp-when-nat-list-listp))

  (defruled check-dims-of-expr-value-list-when-expr-value-list-wfp
    (implies (expr-value-list-wfp vals)
             (equal (check-dims-of-expr-value-list vals)
                    (dims-of-expr-value-list vals)))
    :enable dims-of-expr-value-list-when-expr-value-list-wfp)

  (theory-invariant
   (incompatible
    (:rewrite dims-of-expr-value-list-when-expr-value-list-wfp)
    (:rewrite check-dims-of-expr-value-list-when-expr-value-list-wfp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection dims-of-expr-value-list-list ((x expr-value-list-listp))
  :guard (expr-value-list-list-wfp x)
  :returns (dimss nat-list-list-listp)
  :short "Lift @(tsee dims-of-expr-value-list) to lists."
  (dims-of-expr-value-list x)
  :nil-preservingp t

  ///

  (defruled dims-of-expr-value-list-list-of-cdr
    (equal (dims-of-expr-value-list-list (cdr valss))
           (cdr (dims-of-expr-value-list-list valss))))

  (theory-invariant (incompatible
                     (:rewrite dims-of-expr-value-list-list-of-cdr)
                     (:rewrite cdr-of-dims-of-expr-value-list-list)))

  (defrule dims-of-expr-value-list-list-of-list-split
    (equal (dims-of-expr-value-list-list (list-split vals n))
           (list-split (dims-of-expr-value-list vals) n))
    :induct t
    :enable (list-split
             dims-of-expr-value-list-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-value-vectorp ((val expr-valuep))
  :returns (yes/no booleanp)
  :short "Check if an expression value is a possibly empty vector."
  :long
  (xdoc::topstring
   (xdoc::p
    "The naming of this predicate and of the @(tsee expr-value) summands
     are not ideal,
     because in @(tsee expr-value) @(':vector') refers to non-empty vectors,
     while in this predicate name @('vectorp') refers to all vectors.
     We may improve names in the future,
     or we may merge @(':vector-empty') into @('vector') in @(tsee expr-value)
     by adding a type value to non-empty vectors."))
  (or (expr-value-case val :vector)
      (expr-value-case val :vector-empty))

  ///

  (defruled expr-value-vectorp-to-consp-of-dims
    (implies (expr-value-wfp val)
             (equal (expr-value-vectorp val)
                    (consp (dims-of-expr-value val))))
    :enable (dims-of-expr-value
             expr-value-wfp)
    :expand (check-dims-of-expr-value val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-value-vector-elements ((val expr-valuep))
  :guard (expr-value-vectorp val)
  :returns (vals expr-value-listp)
  :short "Element values of a possibly empty vector."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lets us treat non-empty and empty vectors uniformly
     for the purpose of obtaining their element values."))
  (expr-value-case
   val
   :vector val.elems
   :vector-empty nil
   :otherwise (impossible))
  :guard-hints (("Goal" :in-theory (enable expr-value-vectorp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection expr-value-wfp-theorems
  :short "Theorems about well-formedness expression values."

  (defrule expr-value-wfp-of-expr-value-base
    (expr-value-wfp (expr-value-base base))
    :enable (expr-value-wfp check-dims-of-expr-value))

  (defrule expr-value-wfp-of-expr-value-primop
    (equal (expr-value-wfp (expr-value-primop opval))
           (primop-value-wfp opval))
    :enable (expr-value-wfp
             primop-value-wfp)
    :expand (check-dims-of-expr-value (expr-value-primop opval)))

  (defrule primop-value-wfp-of-expr-value-primop->val
    (implies (expr-value-case val :primop)
             (equal (primop-value-wfp (expr-value-primop->val val))
                    (expr-value-wfp val)))
    :enable (expr-value-wfp
             primop-value-wfp)
    :expand (check-dims-of-expr-value val))

  (defrule expr-value-wfp-of-expr-value-lambda
    (implies (expr-denv-wfp denv)
             (expr-value-wfp (expr-value-lambda param body type? denv)))
    :enable (expr-value-wfp
             expr-denv-wfp-alt-def)
    :expand (check-dims-of-expr-value
             (expr-value-lambda param body type? denv)))

  (defrule expr-denv-wfp-of-expr-value-lambda->denv
    (implies (and (expr-value-wfp val)
                  (expr-value-case val :lambda))
             (expr-denv-wfp (expr-value-lambda->denv val)))
    :enable (expr-value-wfp
             expr-denv-wfp-alt-def)
    :expand (check-dims-of-expr-value val))

  (defrule expr-value-wfp-of-expr-value-tlambda
    (implies (expr-denv-wfp denv)
             (expr-value-wfp (expr-value-tlambda param body denv)))
    :enable (expr-value-wfp
             expr-denv-wfp-alt-def)
    :expand (check-dims-of-expr-value (expr-value-tlambda param body denv)))

  (defrule expr-denv-wfp-of-expr-value-tlambda->denv
    (implies (and (expr-value-wfp val)
                  (expr-value-case val :tlambda))
             (expr-denv-wfp (expr-value-tlambda->denv val)))
    :enable (expr-value-wfp
             expr-denv-wfp-alt-def)
    :expand (check-dims-of-expr-value val))

  (defrule expr-value-wfp-of-expr-value-ilambda
    (implies (expr-denv-wfp denv)
             (expr-value-wfp (expr-value-ilambda param body denv)))
    :enable (expr-value-wfp
             expr-denv-wfp-alt-def)
    :expand (check-dims-of-expr-value (expr-value-ilambda param body denv)))

  (defrule expr-denv-wfp-of-expr-value-ilambda->denv
    (implies (and (expr-value-wfp val)
                  (expr-value-case val :ilambda))
             (expr-denv-wfp (expr-value-ilambda->denv val)))
    :enable (expr-value-wfp
             expr-denv-wfp-alt-def)
    :expand (check-dims-of-expr-value val))

  (defrule expr-value-wfp-of-expr-value-box
    (equal (expr-value-wfp (expr-value-box ispaces array type))
           (expr-value-wfp array))
    :enable expr-value-wfp
    :expand (check-dims-of-expr-value (expr-value-box ispaces array type)))

  (defrule expr-value-wfp-of-expr-value-vector-empty
    (expr-value-wfp (expr-value-vector-empty dims elem))
    :enable (expr-value-wfp
             check-dims-of-expr-value
             acl2::not-reserrp-when-nat-listp))

  (defrule expr-value-wfp-of-expr-value-vector-of-expr-value-base-list
    (implies (consp bvals)
             (expr-value-wfp (expr-value-vector (expr-value-base-list bvals))))
    :enable (expr-value-wfp
             check-dims-of-expr-value
             check-dims-of-expr-value-list-of-expr-value-base-list
             acl2::consp-of-repeat
             car-of-repeat
             list-repeatp-of-repeat
             acl2::not-reserrp-when-nat-listp
             acl2::not-reserrp-when-nat-list-listp))

  (defrule expr-value-wfp-of-expr-value-vector
    (implies (and (consp vals)
                  (expr-value-list-wfp vals)
                  (list-repeatp (dims-of-expr-value-list vals)))
             (expr-value-wfp (expr-value-vector vals)))
    :enable (expr-value-wfp
             check-dims-of-expr-value-list-when-expr-value-list-wfp
             consp-of-dims-of-expr-value-list
             acl2::not-reserrp-when-nat-listp
             acl2::not-reserrp-when-nat-list-listp)
    :expand (check-dims-of-expr-value (expr-value-vector vals)))

  (defrule expr-value-wfp-of-expr-value-box->array
    (implies (and (expr-value-wfp val)
                  (expr-value-case val :box))
             (expr-value-wfp (expr-value-box->array val)))
    :enable expr-value-wfp
    :expand (check-dims-of-expr-value val))

  (defrule expr-value-list-wfp-of-expr-value-vector->elems
    (implies (and (expr-value-wfp val)
                  (expr-value-case val :vector))
             (expr-value-list-wfp (expr-value-vector->elems val)))
    :enable (expr-value-wfp
             expr-value-list-wfp-alt-def)
    :expand (check-dims-of-expr-value val))

  (defrule expr-value-list-wfp-of-expr-value-vector-elements
    (implies (expr-value-wfp val)
             (expr-value-list-wfp (expr-value-vector-elements val)))
    :enable expr-value-vector-elements)

  (defrule list-repeatp-of-dims-of-expr-value-vector->elems
    (implies (and (expr-value-wfp val)
                  (expr-value-case val :vector))
             (list-repeatp
              (dims-of-expr-value-list (expr-value-vector->elems val))))
    :enable (expr-value-wfp
             expr-value-list-wfp-alt-def
             check-dims-of-expr-value
             check-dims-of-expr-value-list-when-expr-value-list-wfp))

  (defrule list-repeatp-of-dims-of-expr-value-vector-elements
    (implies (expr-value-wfp val)
             (list-repeatp
              (dims-of-expr-value-list (expr-value-vector-elements val))))
    :enable expr-value-vector-elements)

  (defruled dims-of-expr-value-vector->elems-to-repeat
    (implies (and (expr-value-wfp val)
                  (expr-value-case val :vector))
             (equal (dims-of-expr-value-list (expr-value-vector->elems val))
                    (repeat (car (dims-of-expr-value val))
                            (cdr (dims-of-expr-value val)))))
    :enable (expr-value-wfp
             dims-of-expr-value
             dims-of-expr-value-list-when-expr-value-list-wfp
             check-dims-of-expr-value
             repeat-of-len-and-car-when-list-repeatp
             acl2::nat-list-listp-when-result-not-error
             acl2::true-listp-when-nat-list-listp))

  (defruled dims-of-expr-value-vector-elements-to-repeat
    (implies (and (expr-value-wfp val)
                  (expr-value-vectorp val))
             (equal (dims-of-expr-value-list (expr-value-vector-elements val))
                    (repeat (car (dims-of-expr-value val))
                            (cdr (dims-of-expr-value val)))))
    :enable (expr-value-vectorp
             expr-value-vector-elements
             dims-of-expr-value-vector->elems-to-repeat
             dims-of-expr-value
             check-dims-of-expr-value)))

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

(defines expr-values-atoms
  :short "Collect the flattened list of atom values of expression values."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define expr-value-atoms ((val expr-valuep))
    :returns (vals expr-value-listp)
    :parents (expression-values-and-environments expr-value-atoms/list)
    :short "Collect the flattened list of atom values of an expression value."
    :long
    (xdoc::topstring
     (xdoc::p
      "Recall that we fold atom values into expression values
       (see @(tsee expr-value)):
       the atom values of an array are the expression values at its leaves,
       i.e. the ones that are neither vectors nor empty vectors.
       We return them in row-major order,
       i.e. in the order in which they occur in the nested vectors.")
     (xdoc::p
      "This is the inverse of
       @(tsee expr-value-with-nonempty-dims),
       which builds an expression value
       from its dimensions and from its atom values in the same order.
       An empty vector has no atom values,
       and a non-empty vector has the atom values of its elements.")
     (xdoc::p
      "This function is total:
       every expression value that is not a vector is an atom value,
       including boxes and lambda abstractions."))
    (expr-value-case
     val
     :vector (expr-value-list-atoms val.elems)
     :vector-empty nil
     :otherwise (list (expr-value-fix val)))
    :measure (expr-value-count val))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define expr-value-list-atoms ((vals expr-value-listp))
    :returns (vals1 expr-value-listp)
    :parents (expression-values-and-environments expr-value-atoms/list)
    :short "Collect the flattened list of atom values of a list of expression values."
    :long
    (xdoc::topstring
     (xdoc::p
      "We concatenate the atom values of each expression value in the list,
       preserving the order."))
    (b* (((when (endp vals)) nil))
      (append (expr-value-atoms (car vals))
              (expr-value-list-atoms (cdr vals))))
    :measure (expr-value-list-count vals))

  ///

  (fty::deffixequiv-mutual expr-values-atoms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-value-funp ((op primop-valuep))
  :returns (yes/no booleanp)
  :short "Check if a primitive operation value is
          applicable to expression values."
  :long
  (xdoc::topstring
   (xdoc::p
    "A primitive operation value (see @(tsee primop-value))
     may be applicable to expression values (via term applications),
     or to type values (via type applications),
     or to ispace values (via ispace applications).
     This predicate,
     along with @(tsee primop-value-tfunp) and @(tsee primop-value-ifunp),
     checks these applicabilities,
     which are exhaustive and non-overlapping.
     The three predicates mirror the three kinds of lambda abstraction values,
     i.e. the @(':lambda'), @(':tlambda'), and @(':ilambda') summands
     of @(tsee expr-value).")
   (xdoc::p
    "This predicate holds on the monomorphic primitive operations,
     which need no instantiation,
     and on the fully instantiated stages
     of the polymorphic primitive operations."))
  (primop-value-case op
                     :int-unary t
                     :int-binary t
                     :int-binary-x t
                     :int-rel t
                     :int-rel-x t
                     :int-to-float t
                     :int-to-bool t
                     :float-unary t
                     :float-binary t
                     :float-binary-x t
                     :float-rel t
                     :float-rel-x t
                     :float-truncate t
                     :float-round t
                     :float-ceiling t
                     :float-floor t
                     :bool-unary t
                     :bool-binary t
                     :bool-binary-x t
                     :bool-rel t
                     :bool-rel-x t
                     :bool-to-int t
                     :bool-to-float t
                     :head nil
                     :head-t nil
                     :head-t-d nil
                     :head-t-d-s t
                     :tail nil
                     :tail-t nil
                     :tail-t-d nil
                     :tail-t-d-s t
                     :length nil
                     :length-t nil
                     :length-t-d nil
                     :length-t-d-s t
                     :append nil
                     :append-t nil
                     :append-t-m nil
                     :append-t-m-n nil
                     :append-t-m-n-s t
                     :append-t-m-n-s-x t
                     :reverse nil
                     :reverse-t nil
                     :reverse-t-d nil
                     :reverse-t-d-s t
                     :index nil
                     :index-t nil
                     :index-t-m t
                     :index-t-m-x t
                     :index2d nil
                     :index2d-t nil
                     :index2d-t-m nil
                     :index2d-t-m-n t
                     :index2d-t-m-n-x t
                     :sum nil
                     :sum-s t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-value-tfunp ((op primop-valuep))
  :returns (yes/no booleanp)
  :short "Check if a primitive operation value is
          applicable to type values."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee primop-value-funp) for
     a description of the three applicability predicates.")
   (xdoc::p
    "This predicate holds on
     the stages of polymorphic primitive operations
     that expect type values next."))
  (primop-value-case op
                     :int-unary nil
                     :int-binary nil
                     :int-binary-x nil
                     :int-rel nil
                     :int-rel-x nil
                     :int-to-float nil
                     :int-to-bool nil
                     :float-unary nil
                     :float-binary nil
                     :float-binary-x nil
                     :float-rel nil
                     :float-rel-x nil
                     :float-truncate nil
                     :float-round nil
                     :float-ceiling nil
                     :float-floor nil
                     :bool-unary nil
                     :bool-binary nil
                     :bool-binary-x nil
                     :bool-rel nil
                     :bool-rel-x nil
                     :bool-to-int nil
                     :bool-to-float nil
                     :head t
                     :head-t nil
                     :head-t-d nil
                     :head-t-d-s nil
                     :tail t
                     :tail-t nil
                     :tail-t-d nil
                     :tail-t-d-s nil
                     :length t
                     :length-t nil
                     :length-t-d nil
                     :length-t-d-s nil
                     :append t
                     :append-t nil
                     :append-t-m nil
                     :append-t-m-n nil
                     :append-t-m-n-s nil
                     :append-t-m-n-s-x nil
                     :reverse t
                     :reverse-t nil
                     :reverse-t-d nil
                     :reverse-t-d-s nil
                     :index t
                     :index-t nil
                     :index-t-m nil
                     :index-t-m-x nil
                     :index2d t
                     :index2d-t nil
                     :index2d-t-m nil
                     :index2d-t-m-n nil
                     :index2d-t-m-n-x nil
                     :sum nil
                     :sum-s nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-value-ifunp ((op primop-valuep))
  :returns (yes/no booleanp)
  :short "Check if a primitive operation value is applicable to ispace values."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee primop-value-funp) for
     a description of the three applicability predicates.")
   (xdoc::p
    "This predicate holds on
     the stages of polymorphic primitive operations
     that expect ispace values next."))
  (primop-value-case op
                     :int-unary nil
                     :int-binary nil
                     :int-binary-x nil
                     :int-rel nil
                     :int-rel-x nil
                     :int-to-float nil
                     :int-to-bool nil
                     :float-unary nil
                     :float-binary nil
                     :float-binary-x nil
                     :float-rel nil
                     :float-rel-x nil
                     :float-truncate nil
                     :float-round nil
                     :float-ceiling nil
                     :float-floor nil
                     :bool-unary nil
                     :bool-binary nil
                     :bool-binary-x nil
                     :bool-rel nil
                     :bool-rel-x nil
                     :bool-to-int nil
                     :bool-to-float nil
                     :head nil
                     :head-t t
                     :head-t-d t
                     :head-t-d-s nil
                     :tail nil
                     :tail-t t
                     :tail-t-d t
                     :tail-t-d-s nil
                     :length nil
                     :length-t t
                     :length-t-d t
                     :length-t-d-s nil
                     :append nil
                     :append-t t
                     :append-t-m t
                     :append-t-m-n t
                     :append-t-m-n-s nil
                     :append-t-m-n-s-x nil
                     :reverse nil
                     :reverse-t t
                     :reverse-t-d t
                     :reverse-t-d-s nil
                     :index nil
                     :index-t t
                     :index-t-m nil
                     :index-t-m-x nil
                     :index2d nil
                     :index2d-t t
                     :index2d-t-m t
                     :index2d-t-m-n nil
                     :index2d-t-m-n-x nil
                     :sum t
                     :sum-s nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection primop-value-applicability-theorems
  :short "Theorems about the applicability predicates
          for primitive operation values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicates
     @(tsee primop-value-funp),
     @(tsee primop-value-tfunp), and
     @(tsee primop-value-ifunp)
     are exhaustive and non-overlapping:
     every primitive operation value satisfies exactly one of them."))

  (defrule primop-value-applicability-exhaustive
    (or (primop-value-funp op)
        (primop-value-tfunp op)
        (primop-value-ifunp op))
    :rule-classes nil
    :enable (primop-value-funp
             primop-value-tfunp
             primop-value-ifunp))

  (defrule primop-value-applicability-non-overlapping
    (and (not (and (primop-value-funp op)
                   (primop-value-tfunp op)))
         (not (and (primop-value-funp op)
                   (primop-value-ifunp op)))
         (not (and (primop-value-tfunp op)
                   (primop-value-ifunp op))))
    :rule-classes nil
    :enable (primop-value-funp
             primop-value-tfunp
             primop-value-ifunp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-value-uninstantiated ((op primop-valuep))
  :returns (uninst primop-valuep)
  :short "Uninstantiated stage of a primitive operation value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This maps each stage of a polymorphic primitive operation
     to the uninstantiated stage of the same operation,
     discarding the instantiation values (if any);
     it maps every other primitive operation value to itself."))
  (primop-value-case op
                     :int-binary-x (primop-value-int-binary op.op)
                     :int-rel-x (primop-value-int-rel op.op)
                     :float-binary-x (primop-value-float-binary op.op)
                     :float-rel-x (primop-value-float-rel op.op)
                     :bool-binary-x (primop-value-bool-binary op.op)
                     :bool-rel-x (primop-value-bool-rel op.op)
                     :head-t (primop-value-head)
                     :head-t-d (primop-value-head)
                     :head-t-d-s (primop-value-head)
                     :tail-t (primop-value-tail)
                     :tail-t-d (primop-value-tail)
                     :tail-t-d-s (primop-value-tail)
                     :length-t (primop-value-length)
                     :length-t-d (primop-value-length)
                     :length-t-d-s (primop-value-length)
                     :append-t (primop-value-append)
                     :append-t-m (primop-value-append)
                     :append-t-m-n (primop-value-append)
                     :append-t-m-n-s (primop-value-append)
                     :append-t-m-n-s-x (primop-value-append)
                     :reverse-t (primop-value-reverse)
                     :reverse-t-d (primop-value-reverse)
                     :reverse-t-d-s (primop-value-reverse)
                     :index-t (primop-value-index)
                     :index-t-m (primop-value-index)
                     :index-t-m-x (primop-value-index)
                     :index2d-t (primop-value-index2d)
                     :index2d-t-m (primop-value-index2d)
                     :index2d-t-m-n (primop-value-index2d)
                     :index2d-t-m-n-x (primop-value-index2d)
                     :sum-s (primop-value-sum)
                     :otherwise (primop-value-fix op)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-of-primop-value-fun ((op primop-valuep))
  :guard (primop-value-funp op)
  :returns (type type-valuep)
  :short "Type of a primitive operation value applicable to expression values,
          as a type value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type value form of the type that
     @(tsee primop-types) associates to the operation's surface name.
     We keep this consistent with @(tsee primop-types) by construction;
     a theorem relating the two could be added later.")
   (xdoc::p
    "Currently this type is always
     a zero-rank array of the operation's function type,
     whose inputs and output are themselves
     zero-rank arrays of base types.
     From this type value we can obtain,
     for an operation used as a function value,
     both the expected cell dimensions of its arguments
     and the type of its result,
     uniformly with how the same information
     is obtained for lambda abstractions.")
   (xdoc::p
    "This function is restricted, via the guard,
     to the primitive operation values applicable to expression values,
     which are the ones used as function values.
     For the fully instantiated stages
     of polymorphic primitive operations,
     the function type value is constructed
     from the instantiation values in the fields:
     for the @(':length-t-d-s') stage of @('length'),
     the input is an array of the stored type value,
     whose dimensions are the stored dimension
     followed by the stored shape,
     and the output is the zero-rank array of the integer type.
     For the stages not applicable to expression values,
     which are outside the guard,
     we return an irrelevant type value."))
  (b* ((int-tv (make-type-value-array
                :elem (type-value-base (base-type-int))
                :dims nil))
       (bool-tv (make-type-value-array
                 :elem (type-value-base (base-type-bool))
                 :dims nil))
       (float-tv (make-type-value-array
                  :elem (type-value-base (base-type-float))
                  :dims nil))
       (int-binop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list int-tv int-tv) :out int-tv)
         :dims nil))
       (int-unop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list int-tv) :out int-tv)
         :dims nil))
       (int-relop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list int-tv int-tv) :out bool-tv)
         :dims nil))
       (int-to-float-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list int-tv) :out float-tv)
         :dims nil))
       (int-to-bool-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list int-tv) :out bool-tv)
         :dims nil))
       (float-binop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list float-tv float-tv) :out float-tv)
         :dims nil))
       (float-unop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list float-tv) :out float-tv)
         :dims nil))
       (float-relop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list float-tv float-tv) :out bool-tv)
         :dims nil))
       (float-to-int-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list float-tv) :out int-tv)
         :dims nil))
       (float-to-bool-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list float-tv) :out bool-tv)
         :dims nil))
       (bool-unop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list bool-tv) :out bool-tv)
         :dims nil))
       (bool-binop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list bool-tv bool-tv) :out bool-tv)
         :dims nil))
       (bool-to-int-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list bool-tv) :out int-tv)
         :dims nil))
       (bool-to-float-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list bool-tv) :out float-tv)
         :dims nil)))
    (primop-value-case
     op
     :int-unary int-unop-tv
     :int-binary int-binop-tv
     :int-binary-x int-unop-tv
     :int-rel int-relop-tv
     :int-rel-x int-to-bool-tv
     :int-to-float int-to-float-tv
     :int-to-bool int-to-bool-tv
     :float-unary float-unop-tv
     :float-binary float-binop-tv
     :float-binary-x float-unop-tv
     :float-rel float-relop-tv
     :float-rel-x float-to-bool-tv
     :float-truncate float-to-int-tv
     :float-round float-to-int-tv
     :float-ceiling float-to-int-tv
     :float-floor float-to-int-tv
     :bool-unary bool-unop-tv
     :bool-binary bool-binop-tv
     :bool-binary-x bool-unop-tv
     :bool-rel bool-binop-tv
     :bool-rel-x bool-unop-tv
     :bool-to-int bool-to-int-tv
     :bool-to-float bool-to-float-tv
     :head (prog2$ (impossible) (type-value-base (base-type-bool)))
     :head-t (prog2$ (impossible) (type-value-base (base-type-bool)))
     :head-t-d (prog2$ (impossible) (type-value-base (base-type-bool)))
     :head-t-d-s (make-type-value-array
                  :elem (make-type-value-fun
                         :in (list (make-type-value-array
                                    :elem op.tval
                                    :dims (cons (1+ op.dval) op.sval)))
                         :out (make-type-value-array
                               :elem op.tval
                               :dims op.sval))
                  :dims nil)
     :tail (prog2$ (impossible) (type-value-base (base-type-bool)))
     :tail-t (prog2$ (impossible) (type-value-base (base-type-bool)))
     :tail-t-d (prog2$ (impossible) (type-value-base (base-type-bool)))
     :tail-t-d-s (make-type-value-array
                  :elem (make-type-value-fun
                         :in (list (make-type-value-array
                                    :elem op.tval
                                    :dims (cons (1+ op.dval) op.sval)))
                         :out (make-type-value-array
                               :elem op.tval
                               :dims (cons op.dval op.sval)))
                  :dims nil)
     :length (prog2$ (impossible) (type-value-base (base-type-bool)))
     :length-t (prog2$ (impossible) (type-value-base (base-type-bool)))
     :length-t-d (prog2$ (impossible) (type-value-base (base-type-bool)))
     :length-t-d-s (make-type-value-array
                    :elem (make-type-value-fun
                           :in (list (make-type-value-array
                                      :elem op.tval
                                      :dims (cons op.dval op.sval)))
                           :out int-tv)
                    :dims nil)
     :append (prog2$ (impossible) (type-value-base (base-type-bool)))
     :append-t (prog2$ (impossible) (type-value-base (base-type-bool)))
     :append-t-m (prog2$ (impossible) (type-value-base (base-type-bool)))
     :append-t-m-n (prog2$ (impossible) (type-value-base (base-type-bool)))
     :append-t-m-n-s (make-type-value-array
                      :elem (make-type-value-fun
                             :in (list (make-type-value-array
                                        :elem op.tval
                                        :dims (cons op.mval op.sval))
                                       (make-type-value-array
                                        :elem op.tval
                                        :dims (cons op.nval op.sval)))
                             :out (make-type-value-array
                                   :elem op.tval
                                   :dims (cons (+ op.mval op.nval) op.sval)))
                      :dims nil)
     :append-t-m-n-s-x (make-type-value-array
                        :elem (make-type-value-fun
                               :in (list (make-type-value-array
                                          :elem op.tval
                                          :dims (cons op.nval op.sval)))
                               :out (make-type-value-array
                                     :elem op.tval
                                     :dims (cons (+ op.mval op.nval) op.sval)))
                        :dims nil)
     :reverse (prog2$ (impossible) (type-value-base (base-type-bool)))
     :reverse-t (prog2$ (impossible) (type-value-base (base-type-bool)))
     :reverse-t-d (prog2$ (impossible) (type-value-base (base-type-bool)))
     :reverse-t-d-s (make-type-value-array
                     :elem (make-type-value-fun
                            :in (list (make-type-value-array
                                       :elem op.tval
                                       :dims (cons op.dval op.sval)))
                            :out (make-type-value-array
                                  :elem op.tval
                                  :dims (cons op.dval op.sval)))
                     :dims nil)
     :index (prog2$ (impossible) (type-value-base (base-type-bool)))
     :index-t (prog2$ (impossible) (type-value-base (base-type-bool)))
     :index-t-m (make-type-value-array
                 :elem (make-type-value-fun
                        :in (list (make-type-value-array
                                   :elem op.tval
                                   :dims (list op.mval))
                                  int-tv)
                        :out (make-type-value-array
                              :elem op.tval
                              :dims nil))
                 :dims nil)
     :index-t-m-x (make-type-value-array
                   :elem (make-type-value-fun
                          :in (list int-tv)
                          :out (make-type-value-array
                                :elem op.tval
                                :dims nil))
                   :dims nil)
     :index2d (prog2$ (impossible) (type-value-base (base-type-bool)))
     :index2d-t (prog2$ (impossible) (type-value-base (base-type-bool)))
     :index2d-t-m (prog2$ (impossible) (type-value-base (base-type-bool)))
     :index2d-t-m-n (make-type-value-array
                     :elem (make-type-value-fun
                            :in (list (make-type-value-array
                                       :elem op.tval
                                       :dims (list op.mval op.nval))
                                      (make-type-value-array
                                       :elem (type-value-base (base-type-int))
                                       :dims (list 2)))
                            :out (make-type-value-array
                                  :elem op.tval
                                  :dims nil))
                     :dims nil)
     :index2d-t-m-n-x (make-type-value-array
                       :elem (make-type-value-fun
                              :in (list (make-type-value-array
                                         :elem (type-value-base (base-type-int))
                                         :dims (list 2)))
                              :out (make-type-value-array
                                    :elem op.tval
                                    :dims nil))
                       :dims nil)
     :sum (prog2$ (impossible) (type-value-base (base-type-bool)))
     :sum-s (make-type-value-array
             :elem (make-type-value-fun
                    :in (list (make-type-value-array
                               :elem (type-value-base (base-type-int))
                               :dims op.sval))
                    :out int-tv)
             :dims nil)))
  :guard-hints (("Goal" :in-theory (enable primop-value-funp)))

  ///

  (defret type-value-kind-of-type-of-primop-value-fun
    (implies (primop-value-funp op)
             (equal (type-value-kind type) :array))
    :hints (("Goal" :in-theory (enable primop-value-funp))))

  (defret type-value-kind-of-elem-of-type-of-primop-value-fun
    (implies (primop-value-funp op)
             (equal (type-value-kind (type-value-array->elem type)) :fun))
    :hints (("Goal" :in-theory (enable primop-value-funp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define arity-of-primop-value-fun ((op primop-valuep))
  :guard (primop-value-funp op)
  :returns (arity natp)
  :short "Arity of a primitive operation value applicable to expression values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the number of expression arguments that the operation takes,
     matching the @('prim-...') function that defines its semantics
     in @(see primitives-evaluation):
     1 for the unary operations, 2 for the binary ones.")
   (xdoc::p
    "We define this as the number of inputs
     of the operation's function type (see @(tsee type-of-primop-value-fun)),
     so that the arity cannot diverge from the type.
     Like @(tsee type-of-primop-value-fun),
     this function is restricted, via the guard,
     to the values applicable to expression values."))
  (len (type-value-fun->in
        (type-value-array->elem (type-of-primop-value-fun op)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-value-first-fun ((val expr-valuep))
  :returns (fval expr-value-resultp)
  :short "First function leaf expression value
          (lambda abstraction or primitive operation)
          of an expression value, in row-major order."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function value is an array, of any rank,
     whose elements are lambda abstractions or primitive operations,
     all with equivalent function types if the expression value is well-formed.
     This ACL2 function descends into the first element of each vector
     until it reaches a scalar lambda abstraction or primitive operation,
     which it returns.
     A representative function leaf is used by term application
     (see @(tsee fun-value-param-dims) and @(tsee eval-expr))
     to read the function's signature
     (the parameter type values of a lambda abstraction,
     or the arity of a primitive operation),
     which determines the expected cell shapes of the arguments
     and hence the frames over which the application is lifted.")
   (xdoc::p
    "It is an error if a non-function leaf is reached,
     or if an empty vector is reached, which has no function to return.
     A @(':primop') leaf must be applicable to expression values
     (see @(tsee primop-value-funp));
     otherwise, it is an error as well.")
   (xdoc::p
    "It should be an invariant that, in a well-formed expression value,
     all elements (if the expression value is not scalar) have equivalent types,
     which implies that it makes no difference that this function
     picks the first scalar value rather than any of the others.
     Our current notion of well-formedness of expression values
     does not capture the invariant about equivalent types,
     but we plan to add it;
     then we might consider replacing the use of this function
     with something that returns, under well-formedness guards,
     the shape that @(tsee eval-expr) needs."))
  (expr-value-case
   val
   :base (reserr nil)
   :primop (if (primop-value-funp val.val)
               (expr-value-fix val)
             (reserr nil))
   :lambda (expr-value-fix val)
   :tlambda (reserr nil)
   :ilambda (reserr nil)
   :box (reserr nil)
   :vector (if (consp val.elems)
               (expr-value-first-fun (car val.elems))
             (reserr nil))
   :vector-empty (reserr nil))
  :measure (expr-value-count val)

  ///

  (defret primop-value-funp-of-expr-value-first-fun
    (implies (and (not (reserrp fval))
                  (expr-value-case fval :primop))
             (primop-value-funp (expr-value-primop->val fval)))
    :hints (("Goal"
             :induct t
             :in-theory (enable expr-value-first-fun)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-value-param-dims ((funval expr-valuep))
  :returns (param-dims nat-list-list-resultp)
  :short "Expected argument cell dimensions of a function value."
  :long
  (xdoc::topstring
   (xdoc::p
    "In term application (see @(tsee eval-expr)),
     this ACL2 function is used to return
     the dimensions of the cells
     expected for each remaining argument of a function value,
     one list of dimensions per argument.
     These determine how each argument array
     is split into a frame and cells,
     and hence the frames over which the application is lifted.
     Only the first of these dimension lists
     is used at each unary application step,
     but a primitive operation value may still expect
     more than one argument (see below).")
   (xdoc::p
    "We obtain a representative function leaf
     (see @(tsee expr-value-first-fun)),
     and read its signature.
     A lambda abstraction value binds one parameter,
     whose type is an array type
     whose dimensions we return, as a one-element list.
     For a primitive operation,
     we read the input types of its (residual) function type
     (see @(tsee type-of-primop-value-fun)),
     which are all array types,
     and return their dimensions;
     this list has one element for the operations
     that still expect one argument,
     and two elements for the ones that still expect two arguments.
     It is an error if the value is not a function value."))
  (b* ((fval (expr-value-first-fun funval))
       ((when (reserrp fval)) (reserr nil)))
    (expr-value-case
     fval
     :lambda (list (dims-of-type-value
                    (var+typevalue->type
                     (expr-value-lambda->param fval))))
     :primop (b* ((tvals (type-value-fun->in
                          (type-value-array->elem
                           (type-of-primop-value-fun
                            (expr-value-primop->val fval))))))
               (dims-of-type-value-list tvals))
     :otherwise (reserr nil)))
  :guard-hints (("Goal" :in-theory (enable expr-valuep-when-result-not-error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-value-result-type ((funval expr-valuep))
  :returns (type type-value-resultp)
  :short "Result type (codomain) of a function value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the companion of @(tsee fun-value-param-dims):
     it returns the type of each result cell of applying the function value
     (its codomain).
     It is used to build the result of an application
     over an empty principal frame (see @(tsee eval-app)),
     where there are no cells to compute a result from.")
   (xdoc::p
    "We read the codomain from a representative function leaf
     (see @(tsee expr-value-first-fun)):
     for a primitive operation, it is the output of its function type
     (see @(tsee type-of-primop-value-fun));
     for a lambda abstraction, it is the body type stored in the value,
     which must be present,
     because evaluation is only meaningful on
     type-checked-and-annotated Remora code,
     and we will explicate this as an invariant,
     but for now we return an error if there is no type.
     If instead the function value is an empty array,
     there is no leaf, but its element type value is the function type,
     whose output type we return."))
  (b* (((when (expr-value-case funval :vector-empty))
        (b* ((elem (expr-value-vector-empty->elem funval))
             ((unless (type-value-case elem :fun)) (reserr nil)))
          (type-value-fun->out elem)))
       ((ok fval) (expr-value-first-fun funval)))
    (expr-value-case
     fval
     :primop (type-value-fun->out
              (type-value-array->elem (type-of-primop-value-fun fval.val)))
     :lambda (b* ((type? (expr-value-lambda->type? fval)))
               (type-value-option-case
                type?
                :some type?.val
                :none (reserr nil)))
     :otherwise (reserr nil)))
  :guard-hints (("Goal" :in-theory (enable expr-valuep-when-result-not-error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines cells-at-depth-in-expr-values
  :short "Cells of an expression value, or list of expression values,
          at a given frame depth."

  (define cells-at-depth-in-expr-value ((val expr-valuep) (depth natp))
    :returns (cells expr-value-list-resultp)
    :parents (expression-values-and-environments cells-at-depth-in-expr-values)
    :short "Cells of an expression value at a given frame depth,
            in row-major order."
    :long
    (xdoc::topstring
     (xdoc::p
      "A expression value is an array, whose dimensions may be split into
       a frame (a prefix) and a cell shape (the remaining suffix);
       the exact point of splitting depends on the purpose.
       Given the frame depth, i.e. the number of frame dimensions,
       this function returns the cells in row-major order:
       the sub-arrays reached by descending @('depth') levels
       into the expression value.
       Note that this returns a flat list of cell values:
       as we descend into the depth of the frame,
       the nested vector structure is discarded.")
     (xdoc::p
      "At depth 0 there is no frame,
       so the whole expression value is the single cell,
       which we return as a singleton.
       At a positive depth the expression value must be a non-empty vector,
       and we collect the cells of each element at one less depth, in order.
       It is an error if the depth exceeds the rank,
       i.e. if a non-vector value is reached before the depth is exhausted.
       It is also an error if we reach an empty vector;
       this function only operates on expression values without 0 dimensions.")
     (xdoc::p
      "This is used as part of the rank lifting in the dynamic semantics.
       It is used on the expression values that
       the arguments of an application expression evaluate to.
       It roughly corresponds to
       @($\\mathit{Split}_{n_{\\mathit{ac}}}
          [\\![ \\mathfrak{v}_a \\ldots ]\!!]$)
       in [thesis],
       where expression values, unlike our @(tsee expr-value) fixtype,
       are represented as flat lists of atoms wrapped in
       an array expression that specifies the dimensions
       (which is an equivalent representation to ours).
       This ACL2 function returns a list isomorphic to that one,
       but its elements (the cells) retain their structure.
       Although [thesis] defines @($n_{\\mathit{ac}}$)
       in terms of the dimensions @($n_i\\ldots$) of
       the input type of the Remora function,
       we get the same effect by using,
       as the depth passed to this ACL2 function,
       the number of dimensions @($n_a\\ldots$)
       that precede @($n_i\\ldots$) in the full dimensions of the argument."))
    (if (zp depth)
        (list (expr-value-fix val))
      (expr-value-case
       val
       :base (reserr nil)
       :primop (reserr nil)
       :lambda (reserr nil)
       :tlambda (reserr nil)
       :ilambda (reserr nil)
       :box (reserr nil)
       :vector (cells-at-depth-in-expr-value-list val.elems (1- depth))
       :vector-empty (reserr nil)))
    :measure (expr-value-count val))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define cells-at-depth-in-expr-value-list ((vals expr-value-listp)
                                             (depth natp))
    :returns (cells expr-value-list-resultp)
    :parents (expression-values-and-environments cells-at-depth-in-expr-values)
    :short "Concatenation of
            the cells of a list of expression values at a given frame depth,
            in the same order as the list."
    (b* (((when (endp vals)) nil)
         ((ok cells1) (cells-at-depth-in-expr-value (car vals) depth))
         ((ok cells2) (cells-at-depth-in-expr-value-list (cdr vals) depth)))
      (append cells1 cells2))
    :measure (expr-value-list-count vals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork
  ((local (in-theory (enable expr-value-listp-when-result-not-error))))

  :flag-local nil

  ///

  (fty::deffixequiv-mutual cells-at-depth-in-expr-values
    :hints (("Goal" :in-theory (enable nfix))))

  (defret-mutual expr-value-list-wfp-of-cells-at-depth-in-expr-values
    (defret expr-value-list-wfp-of-cells-at-depth-in-expr-value
      (implies (and (expr-value-wfp val)
                    (not (reserrp cells)))
               (expr-value-list-wfp cells))
      :fn cells-at-depth-in-expr-value)
    (defret expr-value-list-wfp-of-cells-at-depth-in-expr-value-list
      (implies (and (expr-value-list-wfp vals)
                    (not (reserrp cells)))
               (expr-value-list-wfp cells))
      :fn cells-at-depth-in-expr-value-list)
    :mutual-recursion cells-at-depth-in-expr-values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-ispace ((var ispace-varp)
                              (ival ispace-valuep)
                              (denv expr-denvp))
  :returns (new-denv expr-denvp)
  :short "Add an ispace variable, with an associated ispace value,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-expr-denv denv
                    :tenv (type-denv-add-ispace var
                                                ival
                                                (expr-denv->tenv denv)))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-ispace
    (implies (expr-denv-wfp denv)
             (expr-denv-wfp new-denv))
    :hints (("Goal" :in-theory (enable expr-denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-ispaces ((vars ispace-var-listp)
                               (ivals ispace-value-listp)
                               (denv expr-denvp))
  :guard (equal (len vars) (len ivals))
  :returns (new-denv expr-denvp)
  :short "Add zero or more ispace variables, with associated ispace values,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (change-expr-denv denv
                    :tenv (type-denv-add-ispaces vars
                                                 ivals
                                                 (expr-denv->tenv denv)))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-ispaces
    (implies (expr-denv-wfp denv)
             (expr-denv-wfp new-denv))
    :hints (("Goal" :in-theory (enable expr-denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-type ((var type-varp)
                            (tval type-valuep)
                            (denv expr-denvp))
  :returns (new-denv expr-denvp)
  :short "Add a type variable, with an associated type value,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-expr-denv denv
                    :tenv (type-denv-add-type var
                                              tval
                                              (expr-denv->tenv denv)))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-type
    (implies (expr-denv-wfp denv)
             (expr-denv-wfp new-denv))
    :hints (("Goal" :in-theory (enable expr-denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-types ((vars type-var-listp)
                             (tvals type-value-listp)
                             (denv expr-denvp))
  :guard (equal (len vars) (len tvals))
  :returns (new-denv expr-denvp)
  :short "Add zero or more type variables, with associated type values,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (change-expr-denv denv
                    :tenv (type-denv-add-types vars
                                               tvals
                                               (expr-denv->tenv denv)))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-types
    (implies (expr-denv-wfp denv)
             (expr-denv-wfp new-denv))
    :hints (("Goal" :in-theory (enable expr-denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-expr ((var stringp) (val expr-valuep) (denv expr-denvp))
  :returns (new-denv expr-denvp)
  :short "Add an expression variable,
          with an associated expression value,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-expr-denv denv
                    :exprs (omap::update (str-fix var)
                                         (expr-value-fix val)
                                         (expr-denv->exprs denv)))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-expr
    (implies (and (expr-denv-wfp denv)
                  (expr-value-wfp val))
             (expr-denv-wfp new-denv))
    :hints (("Goal"
             :in-theory (enable expr-denv-wfp
                                string-expr-value-map-wfp-of-update)))))

;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-exprs ((vars string-listp)
                             (vals expr-value-listp)
                             (denv expr-denvp))
  :guard (equal (len vars) (len vals))
  :returns (new-denv expr-denvp)
  :short "Add zero or more expression variables,
          with associated expression values,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (b* (((when (endp vars)) (expr-denv-fix denv))
       ((unless (mbt (consp vals))) (expr-denv-fix denv))
       (denv (expr-denv-add-expr (car vars) (car vals) denv)))
    (expr-denv-add-exprs (cdr vars) (cdr vals) denv))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-exprs
    (implies (and (expr-denv-wfp denv)
                  (expr-value-list-wfp vals))
             (expr-denv-wfp new-denv))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-denv-lookup-ispace ((var ispace-varp) (denv expr-denvp))
  :returns (ispace-val ispace-value-resultp)
  :short "Lookup an ispace variable in an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if the variable is not in the environment."))
  (type-denv-lookup-ispace var (expr-denv->tenv denv)))

;;;;;;;;;;;;;;;;;;;;

(define expr-denv-lookup-type ((var type-varp) (denv expr-denvp))
  :returns (type-val type-value-resultp)
  :short "Lookup a type variable in an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if the variable is not in the environment."))
  (type-denv-lookup-type var (expr-denv->tenv denv)))

;;;;;;;;;;;;;;;;;;;;

(define expr-denv-lookup-expr ((var stringp) (denv expr-denvp))
  :returns (expr-val expr-value-resultp)
  :short "Lookup an expression variable in an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if the variable is not in the environment."))
  (b* ((var+val (omap::assoc (str-fix var) (expr-denv->exprs denv))))
    (if var+val
        (cdr var+val)
      (reserr nil)))

  ///

  (defret expr-value-wfp-of-expr-denv-lookup-expr
    (implies (not (reserrp expr-val))
             (expr-value-wfp expr-val))
    :hyp (expr-denv-wfp denv)
    :hints
    (("Goal"
      :in-theory
      (enable expr-value-wfp-of-cdr-of-assoc-when-string-expr-value-map-wfp
              expr-denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-denv-restrict ((ivars ispace-var-setp)
                            (tvars type-var-setp)
                            (evars string-setp)
                            (denv expr-denvp))
  :returns (new-denv expr-denvp)
  :short "Restrict an expression dynamic environment
          to a set of ispace variables,
          a set of type variables,
          and a set of expression variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "We restrict the underlying type dynamic environment
     to the first and second given sets,
     and we remove from the environment
     the expression variables not in the third given set."))
  (change-expr-denv denv
                    :tenv (type-denv-restrict ivars
                                              tvars
                                              (expr-denv->tenv denv))
                    :exprs (omap::restrict (string-sfix evars)
                                           (expr-denv->exprs denv)))

  ///

  (defret expr-denv-wfp-of-expr-denv-restrict
    (implies (expr-denv-wfp denv)
             (expr-denv-wfp new-denv))
    :hints
    (("Goal"
      :in-theory (enable expr-denv-wfp
                         string-expr-value-map-wfp-of-restrict)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-values ()
  :returns (expr-var-val-map string-expr-value-mapp)
  :short "Association of primitive operations to their values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart of @(tsee primop-types):
     it associates each variable that denotes a primitive operation
     to the value of that variable,
     which is a scalar @(':primop') expression value
     (see @(tsee primop-value)).
     These variables are implicitly in scope,
     and thus part of the initial dynamic environment
     (see @(tsee init-expr-denv)).")
   (xdoc::p
    "The names (the map keys) are the surface names [impl],
     exactly as in @(tsee primop-types).
     A polymorphic operation like @('head'), @('tail'), or @('length')
     is associated to its uninstantiated stage."))
  (omap::from-alist
   (list (cons "+" (expr-value-primop
                    (primop-value-int-binary
                     (int-binary-primop-add))))
         (cons "-" (expr-value-primop
                    (primop-value-int-binary
                     (int-binary-primop-sub))))
         (cons "*" (expr-value-primop
                    (primop-value-int-binary
                     (int-binary-primop-mul))))
         (cons "/" (expr-value-primop
                    (primop-value-int-binary
                     (int-binary-primop-div))))
         (cons "^" (expr-value-primop
                    (primop-value-int-binary
                     (int-binary-primop-expt))))
         (cons "mod" (expr-value-primop
                      (primop-value-int-binary
                       (int-binary-primop-mod))))
         (cons "max" (expr-value-primop
                      (primop-value-int-binary
                       (int-binary-primop-max))))
         (cons "min" (expr-value-primop
                      (primop-value-int-binary
                       (int-binary-primop-min))))
         (cons "bit-and" (expr-value-primop
                          (primop-value-int-binary
                           (int-binary-primop-bit-and))))
         (cons "bit-or" (expr-value-primop
                         (primop-value-int-binary
                          (int-binary-primop-bit-or))))
         (cons "bit-xor" (expr-value-primop
                          (primop-value-int-binary
                           (int-binary-primop-bit-xor))))
         (cons "shl" (expr-value-primop
                      (primop-value-int-binary
                       (int-binary-primop-shl))))
         (cons "shr" (expr-value-primop
                      (primop-value-int-binary
                       (int-binary-primop-shr))))
         (cons "bit-not" (expr-value-primop
                          (primop-value-int-unary
                           (int-unary-primop-bit-not))))
         (cons "popc" (expr-value-primop
                       (primop-value-int-unary
                        (int-unary-primop-popc))))
         (cons "==" (expr-value-primop
                     (primop-value-int-rel
                      (int-rel-primop-eq))))
         (cons "!=" (expr-value-primop
                     (primop-value-int-rel
                      (int-rel-primop-neq))))
         (cons "<" (expr-value-primop
                    (primop-value-int-rel
                     (int-rel-primop-lt))))
         (cons ">" (expr-value-primop
                    (primop-value-int-rel
                     (int-rel-primop-gt))))
         (cons "<=" (expr-value-primop
                     (primop-value-int-rel
                      (int-rel-primop-leq))))
         (cons ">=" (expr-value-primop
                     (primop-value-int-rel
                      (int-rel-primop-geq))))
         (cons "i->f" (expr-value-primop (primop-value-int-to-float)))
         (cons "i->bool" (expr-value-primop (primop-value-int-to-bool)))
         (cons "f.+" (expr-value-primop
                      (primop-value-float-binary
                       (float-binary-primop-add))))
         (cons "f.-" (expr-value-primop
                      (primop-value-float-binary
                       (float-binary-primop-sub))))
         (cons "f.*" (expr-value-primop
                      (primop-value-float-binary
                       (float-binary-primop-mul))))
         (cons "f./" (expr-value-primop
                      (primop-value-float-binary
                       (float-binary-primop-div))))
         (cons "f.^" (expr-value-primop
                      (primop-value-float-binary
                       (float-binary-primop-expt))))
         (cons "f.max" (expr-value-primop
                        (primop-value-float-binary
                         (float-binary-primop-max))))
         (cons "f.min" (expr-value-primop
                        (primop-value-float-binary
                         (float-binary-primop-min))))
         (cons "sqrt" (expr-value-primop
                       (primop-value-float-unary
                        (float-unary-primop-sqrt))))
         (cons "f.sqrt" (expr-value-primop
                         (primop-value-float-unary
                          (float-unary-primop-sqrt))))
         (cons "f.==" (expr-value-primop
                       (primop-value-float-rel
                        (float-rel-primop-eq))))
         (cons "f.!=" (expr-value-primop
                       (primop-value-float-rel
                        (float-rel-primop-neq))))
         (cons "f.<" (expr-value-primop
                      (primop-value-float-rel
                       (float-rel-primop-lt))))
         (cons "f.>" (expr-value-primop
                      (primop-value-float-rel
                       (float-rel-primop-gt))))
         (cons "f.<=" (expr-value-primop
                       (primop-value-float-rel
                        (float-rel-primop-leq))))
         (cons "f.>=" (expr-value-primop
                       (primop-value-float-rel
                        (float-rel-primop-geq))))
         (cons "truncate" (expr-value-primop (primop-value-float-truncate)))
         (cons "round" (expr-value-primop (primop-value-float-round)))
         (cons "ceiling" (expr-value-primop (primop-value-float-ceiling)))
         (cons "floor" (expr-value-primop (primop-value-float-floor)))
         (cons "not" (expr-value-primop
                      (primop-value-bool-unary
                       (bool-unary-primop-not))))
         (cons "and" (expr-value-primop
                      (primop-value-bool-binary
                       (bool-binary-primop-and))))
         (cons "or" (expr-value-primop
                     (primop-value-bool-binary
                      (bool-binary-primop-or))))
         (cons "bool.==" (expr-value-primop
                          (primop-value-bool-rel
                           (bool-rel-primop-eq))))
         (cons "bool.!=" (expr-value-primop
                          (primop-value-bool-rel
                           (bool-rel-primop-neq))))
         (cons "bool->i" (expr-value-primop (primop-value-bool-to-int)))
         (cons "bool->f" (expr-value-primop (primop-value-bool-to-float)))
         (cons "head" (expr-value-primop (primop-value-head)))
         (cons "tail" (expr-value-primop (primop-value-tail)))
         (cons "length" (expr-value-primop (primop-value-length)))
         (cons "append" (expr-value-primop (primop-value-append)))
         (cons "reverse" (expr-value-primop (primop-value-reverse)))
         (cons "index" (expr-value-primop (primop-value-index)))
         (cons "index2d" (expr-value-primop (primop-value-index2d)))
         (cons "sum" (expr-value-primop (primop-value-sum))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-expr-denv ()
  :returns (denv expr-denvp)
  :short "Initial expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the initial, i.e. top-level, expression dynamic environment.
     It only contains the primitive operations in scope.
     It is the dynamic counterpart of @(tsee init-senv)."))
  (make-expr-denv :tenv (make-type-denv :ienv (make-ispace-denv :ispaces nil)
                                        :types nil)
                  :exprs (primop-values))

  ///

  (defret expr-denv-wfp-of-init-expr-denv
    (expr-denv-wfp denv)))
