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
(include-book "primitive-operation-values")
(include-book "unit-types")

(include-book "kestrel/fty/nat-list-list-list" :dir :system)
(include-book "kestrel/fty/nat-list-result" :dir :system)
(include-book "kestrel/fty/nat-list-list-result" :dir :system)
(include-book "std/typed-lists/cons-listp" :dir :system)

(local (include-book "arithmetic"))

(local (include-book "std/basic/nfix" :dir :system))
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
     and their associated expression values."))
  :order-subtopics (base-values
                    primitive-operation-values
                    t)
  :default-parent t)

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
      "The parameters of a lambda value associate
       type values, not types, to the variables:
       the parameter types are evaluated
       when the lambda abstraction is evaluated,
       while the body is evaluated
       when the lambda abstraction is applied.
       The same goes for the optional type of the body of the lambda value,
       which mirrors the one in the AST for lambda abstraction atoms.")
     (xdoc::p
      "An ispace lambda value binds exactly one parameter:
       consistently with the curried view of ispace applications
       (see @(tsee expr)),
       an ispace lambda abstraction with two or more parameters
       evaluates to the unary ispace lambda value
       that binds the first parameter,
       whose body is the ispace lambda abstraction
       over the remaining parameters.
       The other two kinds of lambda values
       still bind all their parameters at once;
       they will be similarly made unary.")
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
    (:lambda ((params var+typevalue-list)
              (body expr)
              (type? type-value-option)
              (denv expr-denv)))
    (:tlambda ((params type-var-list)
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
     (and on the underlying maps)."))

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
     :primop nil
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

  (defrule expr-value-wfp-of-expr-value-lambda
    (implies (expr-denv-wfp denv)
             (expr-value-wfp (expr-value-lambda params body type? denv)))
    :enable (expr-value-wfp
             expr-denv-wfp-alt-def)
    :expand (check-dims-of-expr-value
             (expr-value-lambda params body type? denv)))

  (defrule expr-denv-wfp-of-expr-value-lambda->denv
    (implies (and (expr-value-wfp val)
                  (expr-value-case val :lambda))
             (expr-denv-wfp (expr-value-lambda->denv val)))
    :enable (expr-value-wfp
             expr-denv-wfp-alt-def)
    :expand (check-dims-of-expr-value val))

  (defrule expr-value-wfp-of-expr-value-tlambda
    (implies (expr-denv-wfp denv)
             (expr-value-wfp (expr-value-tlambda params body denv)))
    :enable (expr-value-wfp
             expr-denv-wfp-alt-def)
    :expand (check-dims-of-expr-value (expr-value-tlambda params body denv)))

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
     expected for each argument of a function value,
     one list of dimensions per argument.
     These determine how each argument array
     is split into a frame and cells,
     and hence the frames over which the application is lifted.")
   (xdoc::p
    "We obtain a representative function leaf
     (see @(tsee expr-value-first-fun)),
     and read its signature.
     For a lambda abstraction,
     the parameters must all have array types,
     whose dimensions are returned.
     For a primitive operation,
     we likewise read the input types of its function type
     (see @(tsee type-of-primop-value-fun)),
     which are all array types,
     and return their dimensions.
     It is an error if the value is not a function value,
     or if a lambda abstraction's parameters
     do not all have array types."))
  (b* ((fval (expr-value-first-fun funval))
       ((when (reserrp fval)) (reserr nil)))
    (expr-value-case
     fval
     :lambda (b* ((tvals (var+typevalue-list->type
                          (expr-value-lambda->params fval))))
               (dims-of-type-value-list tvals))
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
   (list (cons "+" (expr-value-primop (primop-value-int-add)))
         (cons "-" (expr-value-primop (primop-value-int-sub)))
         (cons "*" (expr-value-primop (primop-value-int-mul)))
         (cons "/" (expr-value-primop (primop-value-int-div)))
         (cons "^" (expr-value-primop (primop-value-int-expt)))
         (cons "mod" (expr-value-primop (primop-value-int-mod)))
         (cons "max" (expr-value-primop (primop-value-int-max)))
         (cons "min" (expr-value-primop (primop-value-int-min)))
         (cons "bit-and" (expr-value-primop (primop-value-int-bit-and)))
         (cons "bit-or" (expr-value-primop (primop-value-int-bit-or)))
         (cons "bit-xor" (expr-value-primop (primop-value-int-bit-xor)))
         (cons "shl" (expr-value-primop (primop-value-int-shl)))
         (cons "shr" (expr-value-primop (primop-value-int-shr)))
         (cons "bit-not" (expr-value-primop (primop-value-int-bit-not)))
         (cons "popc" (expr-value-primop (primop-value-int-popc)))
         (cons "==" (expr-value-primop (primop-value-int-eq)))
         (cons "!=" (expr-value-primop (primop-value-int-neq)))
         (cons "<" (expr-value-primop (primop-value-int-lt)))
         (cons ">" (expr-value-primop (primop-value-int-gt)))
         (cons "<=" (expr-value-primop (primop-value-int-leq)))
         (cons ">=" (expr-value-primop (primop-value-int-geq)))
         (cons "i->f" (expr-value-primop (primop-value-int-to-float)))
         (cons "i->bool" (expr-value-primop (primop-value-int-to-bool)))
         (cons "f.+" (expr-value-primop (primop-value-float-add)))
         (cons "f.-" (expr-value-primop (primop-value-float-sub)))
         (cons "f.*" (expr-value-primop (primop-value-float-mul)))
         (cons "f./" (expr-value-primop (primop-value-float-div)))
         (cons "f.^" (expr-value-primop (primop-value-float-expt)))
         (cons "f.max" (expr-value-primop (primop-value-float-max)))
         (cons "f.min" (expr-value-primop (primop-value-float-min)))
         (cons "sqrt" (expr-value-primop (primop-value-float-sqrt)))
         (cons "f.sqrt" (expr-value-primop (primop-value-float-sqrt)))
         (cons "f.==" (expr-value-primop (primop-value-float-eq)))
         (cons "f.!=" (expr-value-primop (primop-value-float-neq)))
         (cons "f.<" (expr-value-primop (primop-value-float-lt)))
         (cons "f.>" (expr-value-primop (primop-value-float-gt)))
         (cons "f.<=" (expr-value-primop (primop-value-float-leq)))
         (cons "f.>=" (expr-value-primop (primop-value-float-geq)))
         (cons "truncate" (expr-value-primop (primop-value-float-truncate)))
         (cons "round" (expr-value-primop (primop-value-float-round)))
         (cons "ceiling" (expr-value-primop (primop-value-float-ceiling)))
         (cons "floor" (expr-value-primop (primop-value-float-floor)))
         (cons "not" (expr-value-primop (primop-value-bool-not)))
         (cons "and" (expr-value-primop (primop-value-bool-and)))
         (cons "or" (expr-value-primop (primop-value-bool-or)))
         (cons "bool.==" (expr-value-primop (primop-value-bool-eq)))
         (cons "bool.!=" (expr-value-primop (primop-value-bool-neq)))
         (cons "bool->i" (expr-value-primop (primop-value-bool-to-int)))
         (cons "bool->f" (expr-value-primop (primop-value-bool-to-float)))
         (cons "head" (expr-value-primop (primop-value-head)))
         (cons "tail" (expr-value-primop (primop-value-tail)))
         (cons "length" (expr-value-primop (primop-value-length)))
         (cons "append" (expr-value-primop (primop-value-append))))))

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
