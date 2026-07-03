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

(defxdoc+ values
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
     define expression values as subsets of expressions and atoms,
     namely the ones that cannot be further reduced.
     While we could follow the same approach here,
     instead we start by defining separate fixtypes for expression values.")
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
     to define expression values as subsets of expressions and atoms,
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

(define ispace-value-to-dims ((ival ispace-valuep))
  :returns (dims nat-listp)
  :short "Turn an ispace value into a list of dimensions."
  (ispace-value-case
   ival
   :dim (list ival.val)
   :shape ival.val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection ispace-value-list-to-dims ((x ispace-value-listp))
  :returns (dimss nat-list-listp)
  :short "Lift @(tsee ispace-value-to-dims) to lists."
  (ispace-value-to-dims x))

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

(fty::deftypes type-values
  :short "Fixtypes of type values and lists of type values."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum type-value
    :parents (values type-values)
    :short "Fixtype of type values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is like a normalized ground form of type ASTs:
       if there are no free variables,
       a type is a base type,
       or an array with a type value element with a list of dimensions,
       or a function type with input and output type values,
       or a universal, product, or sum type.
       The latter three categories of types do not use type values in bodies,
       but they have the full type ASTs,
       because the bindings ``shield'' the body,
       like common lambda abstractions."))
    (:base ((type base-type)))
    (:array ((elem type-value)
             (dims nat-list)))
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
    :parents (values type-values)
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

(std::defprojection type-value-array-list->dims ((x type-value-listp))
  :guard (type-value-list-case-array x)
  :returns (shapes nat-list-listp)
  :short "Lift @(tsee type-value-array->dims) to lists."
  (type-value-array->dims x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption type-value-option
  type-value
  :short "Fixtype of optional type values."
  :pred type-value-optionp)

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

(fty::defprod var+typevalue
  :short "Fixtype of variables with type values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart of @(tsee var+type?),
     but with the type being present:
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

(fty::deftagsum primop-value
  :short "Fixtype of primitive operation values."
  :long
  (xdoc::topstring
   (xdoc::p
    "In Remora, the primitive operations (i.e. built-in functions)
     are denoted by certain variables implicitly in scope,
     whose types are given by @(tsee primop-types).
     This fixtype currently enumerates the operations themselves,
     one summand per operation,
     in correspondence with the entries of @(tsee primop-types);
     but we will extend this soon to include summands
     that correspond to partially instantiated primitive operations
     (more details below).")
   (xdoc::p
    "A value of this fixtype represents a primitive operation
     as a scalar (zero-rank array) function value,
     analogously to how a lambda abstraction is a function value.
     These are incorporated into @(tsee expr-value)
     as its @(':primop') summand;
     the operations they denote will be evaluated via
     the ACL2 functions in @(see primitives-evaluation).")
   (xdoc::p
    "The operations currently in this fixtype are all monomorphic:
     the element type of each operation's zero-rank array type
     is a function type between base types.
     Remora also has polymorphic primitive operations,
     such as @('length'),
     where the element type of the zero-rank array type
     involves universal and product types;
     [impl] calls these operations `intrinsics',
     reserving `primitives' for the monomorphic ones,
     but we call both `primitive operations',
     in the sense that they are not defined with Remora code,
     but are built-in.
     (The current division between `primitives' and `intrinsics' in [impl]
     as monomorphic and polymorphic functions is actually incidental:
     by `primitive' [impl] means on integers and similar types,
     and by `intrinsic' [impl] means the other built-ins;
     but as mentioned already, we just use the term `primitive' for all.)
     Since a polymorphic operation cannot be
     directly applied to expression values,
     but must first be applied to type values and/or ispace values,
     we will extend this fixtype with,
     for each polymorphic operation,
     a summand for each instantiation stage of the operation,
     whose fields hold the instantiation values received so far.
     This fixtype will then contain
     not only primitive operations proper (the uninstantiated stages),
     but more generally values related to primitive operations."))
  (:int-add ())
  (:int-sub ())
  (:int-mul ())
  (:int-div ())
  (:int-mod ())
  (:int-max ())
  (:int-min ())
  (:int-bit-and ())
  (:int-bit-or ())
  (:int-bit-xor ())
  (:int-shl ())
  (:int-shr ())
  (:int-bit-not ())
  (:int-popc ())
  (:int-eq ())
  (:int-neq ())
  (:int-lt ())
  (:int-gt ())
  (:int-leq ())
  (:int-geq ())
  (:int-to-float ())
  (:int-to-bool ())
  (:float-add ())
  (:float-sub ())
  (:float-mul ())
  (:float-div ())
  (:float-expt ())
  (:float-max ())
  (:float-min ())
  (:float-sqrt ())
  (:float-eq ())
  (:float-neq ())
  (:float-lt ())
  (:float-gt ())
  (:float-leq ())
  (:float-geq ())
  (:float-truncate ())
  (:float-round ())
  (:float-ceiling ())
  (:float-floor ())
  (:bool-not ())
  (:bool-and ())
  (:bool-or ())
  (:bool-eq ())
  (:bool-neq ())
  (:bool-to-int ())
  (:bool-to-float ())
  :pred primop-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
    "All the current values of @(tsee primop-value)
     are applicable to expression values:
     thus, this predicate currently holds on all the values.
     When summands for the instantiation stages
     of polymorphic primitive operations are added,
     this predicate will hold on
     exactly the stages that may be applied to expression values,
     i.e. the fully instantiated ones."))
  (declare (ignore op))
  t)

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
    "The current values of @(tsee primop-value),
     i.e. the monomorphic primitive operations,
     are not applied to type values:
     thus, this predicate currently holds on no value.
     When summands for the instantiation stages
     of polymorphic primitive operations are added,
     this predicate will hold on
     exactly the stages that expect type values next
     (e.g. an uninstantiated @('length'))."))
  (declare (ignore op))
  nil)

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
    "The current values of @(tsee primop-value),
     i.e. the monomorphic primitive operations,
     are not applied to ispace values:
     thus, this predicate currently holds on no value.
     When summands for the instantiation stages
     of polymorphic primitive operations are added,
     this predicate will hold on
     exactly the stages that expect ispace values next
     (e.g. a @('length') already applied to a type value)."))
  (declare (ignore op))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
    :enable primop-value-funp)

  (defrule primop-value-applicability-non-overlapping
    (and (not (and (primop-value-funp op)
                   (primop-value-tfunp op)))
         (not (and (primop-value-funp op)
                   (primop-value-ifunp op)))
         (not (and (primop-value-tfunp op)
                   (primop-value-ifunp op))))
    :rule-classes nil
    :enable (primop-value-tfunp
             primop-value-ifunp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     When summands for the instantiation stages
     of polymorphic primitive operations are added,
     this ACL2 function will also cover the fully instantiated stages,
     whose function type values will be constructed
     from the instantiation values in the fields."))
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
     :int-add int-binop-tv
     :int-sub int-binop-tv
     :int-mul int-binop-tv
     :int-div int-binop-tv
     :int-mod int-binop-tv
     :int-max int-binop-tv
     :int-min int-binop-tv
     :int-bit-and int-binop-tv
     :int-bit-or int-binop-tv
     :int-bit-xor int-binop-tv
     :int-shl int-binop-tv
     :int-shr int-binop-tv
     :int-bit-not int-unop-tv
     :int-popc int-unop-tv
     :int-eq int-relop-tv
     :int-neq int-relop-tv
     :int-lt int-relop-tv
     :int-gt int-relop-tv
     :int-leq int-relop-tv
     :int-geq int-relop-tv
     :int-to-float int-to-float-tv
     :int-to-bool int-to-bool-tv
     :float-add float-binop-tv
     :float-sub float-binop-tv
     :float-mul float-binop-tv
     :float-div float-binop-tv
     :float-expt float-binop-tv
     :float-max float-binop-tv
     :float-min float-binop-tv
     :float-sqrt float-unop-tv
     :float-eq float-relop-tv
     :float-neq float-relop-tv
     :float-lt float-relop-tv
     :float-gt float-relop-tv
     :float-leq float-relop-tv
     :float-geq float-relop-tv
     :float-truncate float-to-int-tv
     :float-round float-to-int-tv
     :float-ceiling float-to-int-tv
     :float-floor float-to-int-tv
     :bool-not bool-unop-tv
     :bool-and bool-binop-tv
     :bool-or bool-binop-tv
     :bool-eq bool-binop-tv
     :bool-neq bool-binop-tv
     :bool-to-int bool-to-int-tv
     :bool-to-float bool-to-float-tv))

  ///

  (defret type-value-kind-of-type-of-primop-value-fun
    (implies (primop-value-funp op)
             (equal (type-value-kind type) :array)))

  (defret type-value-kind-of-elem-of-type-of-primop-value-fun
    (implies (primop-value-funp op)
             (equal (type-value-kind (type-value-array->elem type)) :fun))))

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

(fty::deftypes expr-values
  :short "Fixtypes of expression values and lists of expression values."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum expr-value
    :parents (values expr-values)
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
      "This fixtype does not capture constraints like
       the non-emptiness of the expression value list in @(':vector'),
       and the dimension and type consistency of the elements of a @(':vector').
       These constraints are captured separately."))
    (:base ((val base-value)))
    (:primop ((val primop-value)))
    (:lambda ((params var+typevalue-list)
              (body expr)
              (type? type-value-option)))
    (:tlambda ((params type-var-list)
               (body expr)))
    (:ilambda ((params ispace-var-list)
               (body expr)))
    (:box ((ispaces ispace-value-list)
           (array expr-value)
           (type type-value)))
    (:vector ((elems expr-value-list)))
    (:vector-empty ((dims nat-list)
                    (elem type-value)))
    :pred expr-valuep)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist expr-value-list
    :parents (values expr-values)
    :short "Fixtype of lists of expression values."
    :elt-type expr-value
    :true-listp t
    :elementp-of-nil nil
    :pred expr-value-listp

    ///

    (defrule expr-value-listp-of-repeat-each
      (implies (expr-value-listp vals)
               (expr-value-listp (repeat-each n vals)))
      :induct (repeat-each n vals)
      :enable (repeat-each expr-value-listp))))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-value-base-list ((x base-value-listp))
  :returns (vals expr-value-listp)
  :short "Lift @(tsee expr-value-base) to lists."
  (expr-value-base x))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-dims-of-expr-values
  :short "Check dimension constraints on
          expression values and lists of expression values."
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
     and functions returning dimensions of well-formed expression values."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dims-of-expr-value ((val expr-valuep))
    :returns (dims nat-list-resultp)
    :parents (values check-dims-of-expr-values)
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
     :lambda nil
     :tlambda nil
     :ilambda nil
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
    :parents (values check-dims-of-expr-values)
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

  :prepwork
  ((local (in-theory (enable acl2::true-listp-when-nat-list-listp
                             acl2::nat-listp-of-car-when-nat-list-listp))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual check-dims-of-expr-values)

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
             acl2::not-reserrp-when-nat-list-listp)))

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

  (theory-invariant (incompatible (:rewrite dims-of-expr-value-list-list-of-cdr)
                                  (:rewrite cdr-of-dims-of-expr-value-list-list)))

  (defrule dims-of-expr-value-list-list-of-list-split
    (equal (dims-of-expr-value-list-list (list-split vals n))
           (list-split (dims-of-expr-value-list vals) n))
    :induct t
    :enable (list-split
             dims-of-expr-value-list-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection expr-value-wfp-theorems
  :short "Theorems about the well-formedness of certain expression values."

  (defrule expr-value-wfp-of-expr-value-base
    (expr-value-wfp (expr-value-base base))
    :enable (expr-value-wfp check-dims-of-expr-value))

  (defrule expr-value-wfp-of-expr-value-lambda
    (expr-value-wfp (expr-value-lambda params body type?))
    :enable (expr-value-wfp check-dims-of-expr-value))

  (defrule expr-value-wfp-of-expr-value-tlambda
    (expr-value-wfp (expr-value-tlambda params body))
    :enable (expr-value-wfp check-dims-of-expr-value))

  (defrule expr-value-wfp-of-expr-value-ilambda
    (expr-value-wfp (expr-value-ilambda params body))
    :enable (expr-value-wfp check-dims-of-expr-value))

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
    :expand (check-dims-of-expr-value val)))

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
                          (expr-value-lambda->params fval)))
                  ((unless (type-value-list-case-array tvals)) (reserr nil)))
               (type-value-array-list->dims tvals))
     :primop (b* ((tvals (type-value-fun->in
                          (type-value-array->elem
                           (type-of-primop-value-fun
                            (expr-value-primop->val fval)))))
                  ((unless (type-value-list-case-array tvals)) (reserr nil)))
               (type-value-array-list->dims tvals))
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
    :parents (values cells-at-depth-in-expr-values)
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
    :parents (values cells-at-depth-in-expr-values)
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
