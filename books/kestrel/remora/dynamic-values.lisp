; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")
(include-book "abstract-syntax-structurals")

(include-book "kestrel/fty/nat-list-list-list" :dir :system)
(include-book "kestrel/fty/nat-list-result" :dir :system)
(include-book "kestrel/fty/nat-list-list-result" :dir :system)

(local (include-book "arithmetic"))

(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))
(local (include-book "std/basic/ifix" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/basic/rfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable acl2::nat-listp-when-result-not-error
                          acl2::nat-list-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-values
  :parents (dynamic-semantics)
  :short "Values used in the dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define fixtypes for the values that
     Remora expressions and atoms evaluate to,
     as well as other categories of values
     that ispaces and types evaluate to.
     [thesis], [arxiv], and [esop],
     in line with much programming language literature,
     define values as subsets of expressions and atoms,
     namely the ones that cannot be further reduced.
     While we could follow the same approach here,
     instead we start by defining separate fixtypes for values.")
   (xdoc::p
    "This separation seems a bit cleaner,
     also given the higher level of detail of our formalization
     (compared to the aforementioned publications).
     For instance, base literals in @(tsee base-lit)
     contain syntactic information that is semantically irrelevant.
     We normally think of integer values as mathematical integers,
     not as ASTs with optional signs and sequences of digits
     (although the mapping from the latter to the former
     is fairly straightforward).
     The difference is even more pronounced for floats.")
   (xdoc::p
    "Nonetheless, if we discover that it is more convenient
     to define values as subsets of expressions and atoms,
     we will switch to that approach."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum ispace-value
  :short "Fixtype of ispace values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like a normalized ground form of ispace ASTs:
     if there are no free variables,
     a dimension can be reduced to a natural number,
     and a shape can be reduced to a list of natural numbers."))
  (:dim ((val nat)))
  (:shape ((val nat-list)))
  :pred ispace-valuep)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispace-value-result
  :short "Fixtype of ispace values and errors."
  :ok ispace-value
  :pred ispace-value-resultp
  :prepwork ((local (in-theory (enable ispace-value-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist ispace-value-list
  :short "Fixtype of lists of ispace values."
  :elt-type ispace-value
  :true-listp t
  :elementp-of-nil nil
  :pred ispace-value-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispace-value-list-result
  :short "Fixtype of (i) lists of ispace values and (ii) errors."
  :ok ispace-value-list
  :pred ispace-value-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes type-values
  :short "Fixtypes of type values and lists of type values."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum type-value
    :parents (dynamic-values type-values)
    :short "Fixtype of type values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is like a normalized ground form of type ASTs:
       if there are no free variables,
       a type is a base type,
       or an array with a type value element
       and a list of natural numbers as shape
       (like a shape ispace value, see @(tsee ispace-value)),
       or a function type with input and output type values,
       or a universal, product, or sum type.
       The latter three categories of types do not use type values in bodies,
       but they have the full type ASTs,
       because the bindings ``shield'' the body,
       like common lambda abstractions."))
    (:base ((type base-type)))
    (:array ((elem type-value)
             (shape nat-list)))
    (:fun ((in type-value-list)
           (out type-value)))
    (:forall ((params type-var-list)
              (body type)))
    (:pi ((params ispace-var-list)
          (body type)))
    (:sigma ((params ispace-var-list)
             (body type)))
    :pred type-valuep)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist type-value-list
    :parents (dynamic-values type-values)
    :short "Fixtype of lists of type values."
    :elt-type type-value
    :true-listp t
    :elementp-of-nil nil
    :pred type-value-listp))

;;;;;;;;;;;;;;;;;;;;

(std::deflist type-value-list-case-array (x)
  :short "Check if all the type values in a list
          are in the @(':array') summand."
  :guard (type-value-listp x)
  (type-value-case x :array))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-value-array-list->shape ((x type-value-listp))
  :guard (type-value-list-case-array x)
  :returns (shapes nat-list-listp)
  :short "Lift @(tsee type-value-array->shape) to lists."
  (type-value-array->shape x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-value-result
  :short "Fixtype of type values and errors."
  :ok type-value
  :pred type-value-resultp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-value-list-result
  :short "Fixtype of (i) lists of type values and (ii) errors."
  :ok type-value-list
  :pred type-value-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod var+typevalue
  :short "Fixtype of variables with type values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart of @(tsee var+type):
     a pair consisting of a variable name and an associated type value.
     In the name of this fixtype,
     we join `type' and `value' into `typevalue',
     so that the name reads better in terms of visual grouping.
     The field for the type value is named just @('type'),
     which is clear in the context of this fixtype."))
  ((var string)
   (type type-value))
  :pred var+typevalue-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist var+typevalue-list
  :short "Fixtype of lists of variables with type values."
  :elt-type var+typevalue
  :true-listp t
  :elementp-of-nil nil
  :pred var+typevalue-listp)

;;;;;;;;;;

(std::defprojection var+typevalue-list->var ((x var+typevalue-listp))
  :returns (strings string-listp)
  :short "Lift @(tsee var+typevalue->var) to lists."
  (var+typevalue->var x))

;;;;;;;;;;

(std::defprojection var+typevalue-list->type ((x var+typevalue-listp))
  :returns (tvals type-value-listp)
  :short "Lift @(tsee var+typevalue->type) to lists."
  (var+typevalue->type x))

;;;;;;;;;;;;;;;;;;;;

(fty::defresult var+typevalue-result
  :short "Fixtype of (i) variables with type values and (ii) errors."
  :ok var+typevalue
  :pred var+typevalue-resultp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult var+typevalue-list-result
  :short "Fixtype of (i) lists of variables with type values and (ii) errors."
  :ok var+typevalue-list
  :pred var+typevalue-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod int-value
  :short "Fixtype of integer values."
  :long
  (xdoc::topstring
   (xdoc::p
    "[thesis] does not pin down the details of integer values,
     leaving them abstract.
     [impl] uses Haskell's @('Int'),
     which consists of fixed-precision integers with at least 30 bits.")
   (xdoc::p
    "We do not yet know the definite intention for integer in Remora,
     e.g. whether it should prescribe one portable integer format,
     or allow a range of formats,
     or even allow multiple integer types.
     For now, we use ACL2 integers."))
  ((int int))
  :pred int-valuep)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist int-value-list
  :short "Fixtype of lists of integer values."
  :elt-type int-value
  :true-listp t
  :elementp-of-nil nil
  :pred int-value-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult int-value-result
  :short "Fixtype of (i) integer values and (ii) errors."
  :ok int-value
  :pred int-value-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum float-value
  :short "Fixtype of float values."
  :long
  (xdoc::topstring
   (xdoc::p
    "[thesis] does not pin down the details of float values,
     leaving them abstract.
     [impl] uses Haskell's @('Float'),
     which consists of single-precision floating-point numbers,
     ``desired'' (according to the Haskell documentation)
     to comply with the IEEE standard.")
   (xdoc::p
    "We do not yet know the definite intention for floats in Remora,
     e.g. whether it should prescribe one portable float format,
     or allow a range of formats,
     or even allow multiple float types.
     For now, we use ACL2 rationals,
     with the addition of negative zero (rational 0 being the positive one),
     negative and positive infinities, and not-a-number.
     This is really a placeholder for
     a more realistic representation of float values,
     e.g. in terms of IEEE floatings from @('[books]/kestrel/floats'),
     which we plan to use once the Remora design is clarified."))
  (:ratio ((ratio rational)))
  ;; no :pos0, which is just :ratio 0
  (:neg0 ())
  (:posinf ())
  (:neginf ())
  (:nan ())
  :pred float-valuep)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult float-value-result
  :short "Fixtype of (i) float values and (ii) errors."
  :ok float-value
  :pred float-value-resultp
  :prepwork ((local (in-theory (enable float-value-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum base-value
  :short "Fixtype of base values."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are booleans, integers, and floats."))
  (:bool ((val bool)))
  (:int ((val int-value)))
  (:float ((val float-value)))
  :pred base-valuep)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist base-value-list
  :short "Fixtype of lists of base values."
  :elt-type base-value
  :true-listp t
  :elementp-of-nil nil
  :pred base-value-listp)

;;;;;;;;;;

(std::defprojection base-value-int-list ((x int-value-listp))
  :returns (vals base-value-listp)
  :short "Lift @(tsee base-value-int) to lists."
  (base-value-int x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes values
  :short "Fixtypes of values and lists of values."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum value
    :parents (dynamic-values values)
    :short "Fixtype of values."
    :long
    (xdoc::topstring
     (xdoc::p
      "In Remora, every value, which an expression may evaluate to, is an array.
       Scalar values are zero-rank arrays, consisting of single atom values,
       but we do not define a distinct notion of atom value,
       folding them into the first five summands of this fixtype of values
       (described in more detail below).
       Non-scalar values are positive-rank arrays,
       consisting of zero or more values of rank immediately lower
       (i.e. the rank of the containing array decremented by one);
       we call non-scalars `vectors' in our model of values.
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
       see @(tsee check-dims-of-value))
       and (ii) an (atom) type value;
       together, (i) and (ii) determine the array type of the value.")
     (xdoc::p
      "The atoms that form scalar values are
       base values,
       lambda abstractions,
       and boxed values.
       Our current definition of box values follows [thesis],
       but we may be able to derive ispaces and types
       from the array value itself;
       this will be investigated soon.
       Scalar values correspond to atom values @($\\mathit{Atval}$) in [thesis],
       with the difference that we do not have @($\\mathfrak{o}$) here,
       because in our ASTs, as in [impl],
       primitive operations are represented as variables
       (whose values are predefined).
       However, as already noted, we fold atom values into (array) values.
       Our fixtype of values loosely corresponds
       to @($\\mathit{Val}$) in [thesis],
       but with a different yet equivalent structure.")
     (xdoc::p
      "The parameters of a lambda value associate
       type values, not types, to the variables:
       the parameter types are evaluated
       when the lambda abstraction is evaluated,
       while the body is evaluated
       when the lambda abstraction is applied.")
     (xdoc::p
      "This fixtype does not capture constraints like
       the non-emptiness of the value list in @(':vector'),
       and the dimension and type consistency of the elements of a @(':vector').
       These constraints are captured separately."))
    (:base ((val base-value)))
    (:lambda ((params var+typevalue-list)
              (body expr)))
    (:tlambda ((params type-var-list)
               (body expr)))
    (:ilambda ((params ispace-var-list)
               (body expr)))
    (:box ((ispaces ispace-list)
           (array value)
           (type type)))
    (:vector ((elems value-list)))
    (:vector-empty ((dims nat-list)
                    (elem type-value)))
    :pred valuep)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist value-list
    :parents (dynamic-values values)
    :short "Fixtype of lists of values."
    :elt-type value
    :true-listp t
    :elementp-of-nil nil
    :pred value-listp

    ///

    (defrule value-listp-of-repeat-each
      (implies (value-listp vals)
               (value-listp (repeat-each n vals)))
      :induct (repeat-each n vals)
      :enable (repeat-each value-listp))))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection value-base-list ((x base-value-listp))
  :returns (vals value-listp)
  :short "Lift @(tsee value-base) to lists."
  (value-base x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist value-list-list
  :short "Fixtype of lists of lists of values."
  :elt-type value-list
  :true-listp t
  :elementp-of-nil t
  :pred value-list-listp

  ///

  (defruled true-list-listp-when-value-list-listp
    (implies (value-list-listp x)
             (true-list-listp x))
    :induct t
    :enable true-list-listp)

  (defrule value-list-listp-of-list-split
    (implies (and (value-listp vals)
                  (posp n)
                  (integerp (/ (len vals) n)))
             (value-list-listp (list-split vals n)))
    :induct t
    :enable (list-split
             value-list-listp
             lt-to-zero-when-divided-by-pos
             nfix
             posp)
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defrule value-list-listp-of-cdr-list
    (implies (value-list-listp x)
             (value-list-listp (cdr-list x)))
    :induct t
    :enable cdr-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult value-result
  :short "Fixtype of values and errors."
  :ok value
  :pred value-resultp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult value-list-result
  :short "Fixtype of (i) lists of values and (ii) errors."
  :ok value-list
  :pred value-list-resultp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult value-list-list-result
  :short "Fixtype of (i) lists of lists of values and (ii) errors."
  :ok value-list-list
  :pred value-list-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-dims-of-values
  :short "Check dimension constraints on values and lists of values."
  :long
  (xdoc::topstring
   (xdoc::p
    "As discussed in @(tsee value),
     that fixtype does not capture many of the constraints of values.
     We do that in these functions,
     which also return the dimensions of the values
     if the values satisfy the constraints:
     the dimensions are needed to check the containing values.
     So these functions define, simultaneously,
     predicates on values saying whether the values are well-formed,
     and functions returning dimensions of well-formed values."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dims-of-value ((val valuep))
    :returns (dims nat-list-resultp)
    :parents (dynamic-values check-dims-of-values)
    :short "Check dimension constraints on values."
    :long
    (xdoc::topstring
     (xdoc::p
      "Scalar values always satisfy dimension constraints
       and have the empty list of dimensions.")
     (xdoc::p
      "For a (non-empty) vector, there must be at least one element.
       We recursively check its element values,
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
      "An empty vector, as noted in @(tsee value),
       carries the dimensions of its non-existent elements,
       which otherwise could not be determined.
       The dimensions of the whole vector are obtained
       by adding 0 in front of the elements' dimensions.
       It may seem strange to have dimensions for non-existent elements,
       but that matches the Remora type system:
       in particular, the syntax for empty arrays."))
    (value-case
     val
     :base nil
     :lambda nil
     :tlambda nil
     :ilambda nil
     :box nil
     :vector (b* (((ok dimss) (check-dims-of-value-list val.elems))
                  ((unless (consp dimss)) (reserr nil))
                  ((unless (list-repeatp dimss)) (reserr nil)))
               (cons (len val.elems) (car dimss)))
     :vector-empty (cons 0 val.dims))
    :measure (value-count val))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dims-of-value-list ((vals value-listp))
    :returns (dimss nat-list-list-resultp)
    :parents (dynamic-values check-dims-of-values)
    :short "Check dimension constraints on lists of values."
    :long
    (xdoc::topstring
     (xdoc::p
      "Each list element is checked in turn.
       If they all check successfully,
       we return the dimensions of each, in the same order as the list."))
    (b* (((when (endp vals)) nil)
         ((ok dims) (check-dims-of-value (car vals)))
         ((ok dimss) (check-dims-of-value-list (cdr vals))))
      (cons dims dimss))
    :measure (value-list-count vals)

    ///

    (defret consp-of-check-dims-of-value-list-when-not-error
      (implies (not (reserrp dimss))
               (equal (consp dimss)
                      (consp vals)))
      :hints (("Goal"
               :induct (len vals)
               :in-theory (enable len))))

    (defret len-of-check-dims-of-value-list-when-not-error
      (implies (not (reserrp dimss))
               (equal (len dimss)
                      (len vals)))
      :hints (("Goal"
               :induct (len vals)
               :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork
  ((local (in-theory (enable acl2::true-listp-when-nat-list-listp
                             acl2::nat-listp-of-car-when-nat-list-listp))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual check-dims-of-values)

  (defruled check-dims-of-value-list-of-repeat
    (b* ((dims (check-dims-of-value val))
         (dimss (check-dims-of-value-list (repeat n val))))
      (implies (not (reserrp dims))
               (and (not (reserrp dimss))
                    (equal dimss (repeat n dims)))))
    :induct (repeat n dims)
    :enable (repeat
             acl2::not-reserrp-when-nat-list-listp))

  (defruled check-dims-of-value-list-of-value-base-list
    (equal (check-dims-of-value-list (value-base-list bvals))
           (repeat (len bvals) nil))
    :induct (value-base-list bvals)
    :enable (value-base-list
             check-dims-of-value-list
             check-dims-of-value
             repeat
             len
             acl2::not-reserrp-when-nat-list-listp)
    :prep-books ((local (include-book "arithmetic-3/top" :dir :system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-wfp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value must satisfy the dimension constraints.
     We will extend this to also add the satisfaction of type constraints."))
  (not (reserrp (check-dims-of-value val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist value-list-wfp (x)
  :guard (value-listp x)
  :short "Lift @(tsee value-wfp) to lists."
  (value-wfp x)

  ///

  (defruled value-list-wfp-alt-def
    (equal (value-list-wfp x)
           (not (reserrp (check-dims-of-value-list x))))
    :induct t
    :enable (check-dims-of-value-list
             value-wfp
             acl2::not-reserrp-when-nat-list-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist value-list-list-wfp (x)
  :guard (value-list-listp x)
  :short "Lift @(tsee value-list-wfp) to lists."
  (value-list-wfp x)

  ///

  (defrule value-list-list-wfp-of-list-split
    (implies (value-list-wfp vals)
             (value-list-list-wfp (list-split vals n)))
    :induct t
    :enable list-split))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dims-of-value ((val valuep))
  :guard (value-wfp val)
  :returns (dims nat-listp :hints (("Goal" :in-theory (enable value-wfp))))
  :short "Dimensions of a well-formed value."
  (if (mbt (value-wfp val))
      (check-dims-of-value val)
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection dims-of-value-list ((x value-listp))
  :guard (value-list-wfp x)
  :returns (dimss nat-list-listp)
  :short "Lift @(tsee dims-of-value) to lists."
  (dims-of-value x)
  :nil-preservingp t

  ///

  (defrule dims-of-value-list-of-repeat
    (equal (dims-of-value-list (repeat n val))
           (repeat n (dims-of-value val)))
    :induct t
    :enable repeat)

  (defruled dims-of-value-list-when-value-list-wfp
    (implies (value-list-wfp vals)
             (equal (dims-of-value-list vals)
                    (check-dims-of-value-list vals)))
    :induct t
    :enable (dims-of-value-list
             check-dims-of-value-list
             value-list-wfp
             dims-of-value
             value-wfp
             acl2::not-reserrp-when-nat-list-listp))

  (defruled check-dims-of-value-list-when-value-list-wfp
    (implies (value-list-wfp vals)
             (equal (check-dims-of-value-list vals)
                    (dims-of-value-list vals)))
    :enable dims-of-value-list-when-value-list-wfp)

  (theory-invariant
   (incompatible
    (:rewrite dims-of-value-list-when-value-list-wfp)
    (:rewrite check-dims-of-value-list-when-value-list-wfp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection dims-of-value-list-list ((x value-list-listp))
  :guard (value-list-list-wfp x)
  :returns (dimss nat-list-list-listp)
  :short "Lift @(tsee dims-of-value-list) to lists."
  (dims-of-value-list x)
  :nil-preservingp t

  ///

  (defruled dims-of-value-list-list-of-cdr
    (equal (dims-of-value-list-list (cdr valss))
           (cdr (dims-of-value-list-list valss))))

  (theory-invariant (incompatible (:rewrite dims-of-value-list-list-of-cdr)
                                  (:rewrite cdr-of-dims-of-value-list-list)))

  (defrule dims-of-value-list-list-of-list-split
    (equal (dims-of-value-list-list (list-split vals n))
           (list-split (dims-of-value-list vals) n))
    :induct t
    :enable (list-split
             dims-of-value-list-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-wfp-theorems
  :short "Theorems about the well-formedness of certain values."

  (defrule value-wfp-of-value-base
    (value-wfp (value-base base))
    :enable (value-wfp check-dims-of-value))

  (defrule value-wfp-of-value-lambda
    (value-wfp (value-lambda params body))
    :enable (value-wfp check-dims-of-value))

  (defrule value-wfp-of-value-tlambda
    (value-wfp (value-tlambda params body))
    :enable (value-wfp check-dims-of-value))

  (defrule value-wfp-of-value-ilambda
    (value-wfp (value-ilambda params body))
    :enable (value-wfp check-dims-of-value))

  (defrule value-wfp-of-value-vector-empty
    (value-wfp (value-vector-empty dims elem))
    :enable (value-wfp
             check-dims-of-value
             acl2::not-reserrp-when-nat-listp))

  (defrule value-wfp-of-value-vector-of-value-base-list
    (implies (consp bvals)
             (value-wfp (value-vector (value-base-list bvals))))
    :enable (value-wfp
             check-dims-of-value
             check-dims-of-value-list-of-value-base-list
             acl2::consp-of-repeat
             car-of-repeat
             list-repeatp-of-repeat
             acl2::not-reserrp-when-nat-listp
             acl2::not-reserrp-when-nat-list-listp))

  (defrule value-wfp-of-value-vector
    (implies (and (consp vals)
                  (value-list-wfp vals)
                  (list-repeatp (dims-of-value-list vals)))
             (value-wfp (value-vector vals)))
    :enable (value-wfp
             check-dims-of-value-list-when-value-list-wfp
             consp-of-dims-of-value-list
             acl2::not-reserrp-when-nat-listp
             acl2::not-reserrp-when-nat-list-listp)
    :expand (check-dims-of-value (value-vector vals)))

  (defrule value-list-wfp-of-value-vector->elems
    (implies (and (value-wfp val)
                  (value-case val :vector))
             (value-list-wfp (value-vector->elems val)))
    :enable (value-wfp
             value-list-wfp-alt-def)
    :expand (check-dims-of-value val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-first-lambda ((val valuep))
  :returns (lval value-resultp)
  :short "First lambda leaf value of a value, in row-major order."
  :long
  (xdoc::topstring
   (xdoc::p
    "A term function value is an array, of any rank,
     whose elements are (term) lambda abstractions,
     all with equivalent types if the value is well-formed.
     This descends into the first element of each vector
     until it reaches a scalar lambda abstraction, which it returns.
     A representative lambda is used by term application (see @(tsee eval-expr))
     to read the function's parameter type values,
     which determine the expected cell shapes of the arguments
     and hence the frames over which the application is lifted.")
   (xdoc::p
    "It is an error if a non-lambda leaf is reached,
     or if an empty vector is reached, which has no lambda to return.")
   (xdoc::p
    "It should be an invariant that, in a well-formed value,
     all elements (if the value is not scalar) have equivalent types,
     which implies that it makes no difference that this function
     picks the first scalar value rather than any of the others.
     Our current notion of well-formedness of values
     does not capture the invariant about equivalent types,
     but we plan to add it;
     then we might consider replacing the use of this function
     with something that returns, under well-formedness guards,
     the shape that @(tsee eval-expr) needs."))
  (value-case
   val
   :base (reserr nil)
   :lambda (value-fix val)
   :tlambda (reserr nil)
   :ilambda (reserr nil)
   :box (reserr nil)
   :vector (if (consp val.elems)
               (value-first-lambda (car val.elems))
             (reserr nil))
   :vector-empty (reserr nil))
  :measure (value-count val)

  ///

  (defret value-kind-of-value-first-lambda
    (implies (not (reserrp lval))
             (equal (value-kind lval) :lambda))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines cells-at-depth-in-values
  :short "Cells of a value, or list of values, at a given frame depth."

  (define cells-at-depth-in-value ((val valuep) (depth natp))
    :returns (cells value-list-resultp)
    :parents (dynamic-values cells-at-depth-in-values)
    :short "Cells of a value at a given frame depth, in row-major order."
    :long
    (xdoc::topstring
     (xdoc::p
      "A value is an array, whose dimensions may be split into
       a frame (a prefix) and a cell shape (the remaining suffix);
       the exact point of splitting depends on the purpose.
       Given the frame depth, i.e. the number of frame dimensions,
       this function returns the cells in row-major order:
       the sub-arrays reached by descending @('depth') levels into the value.
       Note that this returns a flat list of cell values:
       as we descend into the depth of the frame,
       the nested vector structure is discarded.")
     (xdoc::p
      "At depth 0 there is no frame,
       so the whole value is the single cell,
       which we return as a singleton.
       At a positive depth the value must be a non-empty vector,
       and we collect the cells of each element at one less depth, in order.
       It is an error if the depth exceeds the rank,
       i.e. if a non-vector value is reached before the depth is exhausted.
       It is also an error if we reach an empty vector;
       this function only operates on values without 0 dimensions.")
     (xdoc::p
      "This is used as part of the rank lifting in the dynamic semantics.
       It is used on the values that
       the arguments of an application expression evaluate to.
       It roughly corresponds to
       @($\\mathit{Split}_{n_{\\mathit{ac}}}
          \\llbracket \\mathfrak{v}_a \\ldots \\rrbracket$)
       in [thesis],
       where values, unlike our @(tsee value) fixtype,
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
        (list (value-fix val))
      (value-case
       val
       :base (reserr nil)
       :lambda (reserr nil)
       :tlambda (reserr nil)
       :ilambda (reserr nil)
       :box (reserr nil)
       :vector (cells-at-depth-in-value-list val.elems (1- depth))
       :vector-empty (reserr nil)))
    :measure (value-count val))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define cells-at-depth-in-value-list ((vals value-listp) (depth natp))
    :returns (cells value-list-resultp)
    :parents (dynamic-values cells-at-depth-in-values)
    :short "Concatenation of
            the cells of a list of values at a given frame depth,
            in the same order as the list."
    (b* (((when (endp vals)) nil)
         ((ok cells1) (cells-at-depth-in-value (car vals) depth))
         ((ok cells2) (cells-at-depth-in-value-list (cdr vals) depth)))
      (append cells1 cells2))
    :measure (value-list-count vals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork ((local (in-theory (enable value-listp-when-result-not-error))))

  ///

  (fty::deffixequiv-mutual cells-at-depth-in-values
    :hints (("Goal" :in-theory (enable nfix))))

  (defret-mutual value-list-wfp-of-cells-at-depth-in-values
    (defret value-list-wfp-of-cells-at-depth-in-value
      (implies (and (value-wfp val)
                    (not (reserrp cells)))
               (value-list-wfp cells))
      :fn cells-at-depth-in-value)
    (defret value-list-wfp-of-cells-at-depth-in-value-list
      (implies (and (value-list-wfp vals)
                    (not (reserrp cells)))
               (value-list-wfp cells))
      :fn cells-at-depth-in-value-list)
    :mutual-recursion cells-at-depth-in-values))
