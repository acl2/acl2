; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "types")
(include-book "uid")
(include-book "unambiguity")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (in-theory (enable* abstract-syntax-unambp-rules)))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validation-information
  :parents (validation)
  :short "Information calculated and used by the validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(see validator) calculates and uses information, such as types,
     and annotates the abstract syntax with some of this information.
     Here we introduce fixtypes for this information,
     and operations on those fixtypes.")
   (xdoc::p
    "We also introduce predicates over the abstract syntax,
     to check that the annotations from the validator are present.
     This is not the same as saying that the constructs are validated;
     the predicates just say that information of the right type is present."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-null-pointer-constp ((expr exprp) (type typep))
  (declare (ignore expr))
  :returns (yes/no booleanp)
  :short "Check whether an expression of a given type is potentially a null
          pointer constant [C17:6.3.2.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Due to the approximate representation of types
     and our lack of constant expression evaluation,
     this recognizer is highly overappoximating.
     It will recognize any unknown,
     @('void')/unknown pointer,
     or integer type."))
  (type-case
   type
   :unknown t
   :pointer (or (type-case type.to :void)
                (type-case type.to :unknown))
   :otherwise (type-integerp type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define const-expr-null-pointer-constp ((const-expr const-exprp) (type typep))
  :returns (yes/no booleanp)
  :short "Check whether a constant expression of a given type is potentially a
          null pointer constant [C17:6.3.2.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee expr-null-pointer-constp)."))
  (b* (((const-expr const-expr) const-expr))
    (expr-null-pointer-constp const-expr.expr type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum linkage
  :short "Fixtype of linkages."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are three kinds of linkages: external, internal, and none
     [C17:6.2.2/1]."))
  (:external ())
  (:internal ())
  (:none ())
  :pred linkagep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-linkage
  :short "An irrelevant linkage."
  :type linkagep
  :body (linkage-none))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption linkage-option
  linkage
  :short "Fixtype of optional linkages."
  :long
  (xdoc::topstring
   (xdoc::p
    "Linkages are defined in @(tsee linkage)."))
  :pred linkage-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum lifetime
  :short "Fixtype of lifetimes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This represents a storage duration [C17:6.2.4],
     but only three kinds, excluding the allocated kind.
     We use the term `liftetime' because it is just one word,
     and also to avoid implying that there are only three storage durations,
     when there are in fact four.
     Since a storage duration defines the kind of lifetime of an object,
     one could argue that there are four kinds of lifetimes too;
     however, for practicality, we need a fixtype for
     only these three kinds of lifetimes (or storage durations),
     and so we use the term `lifetime'.
     This must be thought as the possible kinds of lifetime of declared objects;
     allocated objects are not declared, but just created via library calls."))
  (:static ())
  (:thread ())
  (:auto ())
  :pred lifetimep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-lifetime
  :short "An irrelevant lifetime."
  :type lifetimep
  :body (lifetime-auto))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption lifetime-option
  lifetime
  :short "Fixtype of optional lifetimes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lifetimes are defined in @(tsee lifetime)."))
  :pred lifetime-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum valid-defstatus
  :short "Fixtype of definition statuses for validation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to objects and functions, which may be
     undefined, defined, or tentatively defined [C17:6.7/5] [C17:6.9.2],
     with the latter actually only applying to objects, not functions."))
  (:undefined ())
  (:tentative ())
  (:defined ())
  :pred valid-defstatusp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum valid-ord-info
  :short "Fixtype of validation information about ordinary identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Ordinary identifiers [C17:6.2.3/1] denote
     objects, functions, enumeration constants, and @('typedef') names;
     Ordinary identifiers form their own name space.
     The other entities denoted by identifiers [C17:6.2.1/1]
     are in other name spaces, disjoint from the one of ordinary identifiers.")
   (xdoc::p
    "This fixtype formalizes the information about ordinary identifiers
     tracked by our current validator.
     Since our model of types includes both object and function types,
     the information for both objects and functions includes (different) types;
     that information also includes the linkage [C17:6.2.2],
     as well as definition status (see @(tsee valid-defstatus)).
     We also assign a "
    (xdoc::seetopic "uid" "unique identifier")
    ". For enumeration constants names,
     for now we only track that they are enumeration constants.
     For @('typedef') names, we track the type corresponding to its
     definition.")
   (xdoc::p
    "We will refine this fixtype as we refine our validator."))
  (:objfun ((type type)
            (linkage linkage)
            (defstatus valid-defstatus)
            (uid uid)))
  (:enumconst ())
  (:typedef ((def type)))
  :pred valid-ord-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-ord-info-option
  valid-ord-info
  :short "Fixtype of
          optional validation information about ordinary identifiers."
  :pred valid-ord-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist valid-ord-scope
  :short "Fixtype of validation scopes of ordinary identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifiers have scopes [C17:6.2.1], which the validator tracks.
     In each scope, for each name space,
     each identifier must have one meaning (if any) [C17:6.2.1/2].
     Thus, we use an alist from identifiers
     to the validation information about ordinary identifiers,
     to track each scope in the name space of ordinary identifiers."))
  :key-type ident
  :val-type valid-ord-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred valid-ord-scopep
  :prepwork ((set-induction-depth-limit 1))
  ///

  (defrule valid-ord-infop-of-cdr-assoc-when-valid-ord-scopep
    (implies (and (valid-ord-scopep scope)
                  (assoc-equal ident scope))
             (valid-ord-infop (cdr (assoc-equal ident scope))))
    :induct t
    :enable (valid-ord-scopep assoc-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum tag-kind
  :short "Fixtype of the different kinds of tags."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now, we include cases for just @(':struct') and @(':union').
     We omit @(':enum'), whose tags are not yet being tracked."))
  (:struct ())
  (:union ())
  :pred tag-kind)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-tag-info
  :short "Fixtype of validation information about tags."
  :long
  (xdoc::topstring
   (xdoc::p
    "Tags [C17:6.2.3/1] identify a structure, union, or enumeration type.
     Tags form their own name space,
     disambiguated by the @('struct'), @('union'), or @('enum') keywords.")
   (xdoc::p
    "We store just the @(see UID) associated with the tag
     in the current scope.
     The @(see UID) can be used to lookup the completion
     under a separate @(tsee type-completions) map."))
  ((kind tag-kind)
   (uid uid))
  :pred valid-tag-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-tag-info-option
  valid-tag-info
  :short "Fixtype of optional validation information about tags."
  :pred valid-tag-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist valid-tag-scope
  :short "Fixtype of validation scopes of tags."
  :long
  (xdoc::topstring
   (xdoc::p
    "The same tag may refer to different types in different scopes.
     Therefore, we use an alist from identifiers
     to the validation information for tags
     to track the meaning of tags in each scope."))
  :key-type ident
  :val-type valid-tag-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred valid-tag-scopep
  :prepwork ((set-induction-depth-limit 1))
  ///

  (defrule valid-tag-infop-of-cdr-assoc-when-valid-tag-scopep
    (implies (and (valid-tag-scopep scope)
                  (assoc-equal ident scope))
             (valid-tag-infop (cdr (assoc-equal ident scope))))
    :induct t
    :enable (valid-tag-scopep assoc-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-scope
  :short "Fixtype of validation scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifiers have scopes [C17:6.2.1], which the validator tracks.
     This fixtype contains all the information about a scope,
     which considers the name space of ordinary identifiers
     and the name space of tags."))
  ((ord valid-ord-scope)
   (tag valid-tag-scope))
  :pred valid-scopep
  ///

  (defrule alistp-of-valid-scope->ord
    (alistp (valid-scope->ord x))
    :enable alistp-when-valid-ord-scopep-rewrite)

  (defrule alistp-of-valid-scope->tag
    (alistp (valid-scope->tag x))
    :enable alistp-when-valid-tag-scopep-rewrite))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist valid-scope-list
  :short "Fixtype of lists of validation scopes."
  :elt-type valid-scope
  :true-listp t
  :elementp-of-nil nil
  :pred valid-scope-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-ext-info
  :short "Fixtype of validation information about identifiers with external
          linkage."
  :long
  (xdoc::topstring
   (xdoc::p
    "We store the following information about identifiers
     with external linkage for the purpose of validation
     across unrelated scopes and across different translation units
     (by ``unrelated,'' we mean neither scope is nested within the other).")
   (xdoc::p
    "Each declaration of a given identifier with external linkage
     must agree on the type [C17:6.2.2/2] [C17:6.2.7/2].
     Therefore, we store the type to check type compatibility
     of any declaration after the first.")
   (xdoc::p
    "We also store the set of translation units
     (represented by their @(see filepath)s)
     in which the identifier has been declared.
     This is used to ensure the same identifier has not been declared
     with both internal and external linkage in the same translation unit
     [C17:6.2.2/7].")
   (xdoc::p
    "Finally, we store a "
    (xdoc::seetopic "uid" "unique identifier")
    " for the object.
      All identifiers of the same name with external linkage
      refer to the same object and therefore possess
      the same unique identifier.")
   (xdoc::p
    "Eventually, we may wish to store a boolean flag indicating
     whether the identifier has been externally defined.
     This would be used to ensure
     that externally linked identifiers are defined at most once
     (or exactly once, if the identifier is used in an expression) [C17:6.9/5].
     For now, we conservatively allow any number of definitions."))
  ((type type)
   (declared-in filepath-set)
   (uid uid))
  :pred valid-ext-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-ext-info-option
  valid-ext-info
  :short "Fixtype of optional validation information
          about identifiers with external linkage."
  :pred valid-ext-info-optionp)

;;;;;;;;;;;;;;;;;;;;

(fty::defomap valid-externals
  :short "Fixtype of validation information associated with identifiers with
          external linkage."
  :key-type ident
  :val-type valid-ext-info
  :pred valid-externalsp
  ///

  (defrule valid-ext-info-optionp-of-cdr-assoc-when-valid-externalsp
    (implies (valid-externalsp externals)
             (valid-ext-info-optionp (cdr (omap::assoc ident externals))))
    :induct t
    :enable (valid-externalsp omap::assoc valid-ext-info-optionp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-table
  :short "Fixtype of validation tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "A validation table is a collection of validation information
     for translation units and ensembles.")
   (xdoc::p
    "The @('filepath') field stores the name of the translation unit
     which we are validating.")
   (xdoc::p
    "Scopes are treated in a stack-like manner [C17:6.2.1].
     Thus, a validation table contains a list (i.e. stack) of scopes.
     The stack grows from right to left:
     the leftmost scope is the top, and the rightmost scope is the bottom;
     in other words, in the nesting of scopes in the stack,
     the leftmost scope is the innermost,
     and the rightmost scope is the outermost
     (i.e. the file scope [C17:6.2.1/4].)")
   (xdoc::p
    "We also track information about identifiers with external linkage,
     which we use for cross-checking across disjoint scopes
     and different translation units.
     This information accumulates
     as we validate each translation unit in the ensemble.")
   (xdoc::p
    "The @('next-uid') field stores the next unused "
    (xdoc::seetopic "uid" "unique identifier")
    "."))
  ((filepath filepath)
   (scopes valid-scope-list)
   (externals valid-externals)
   (completions type-completions)
   (next-uid uidp))
  :pred valid-tablep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-valid-table
  :short "An irrelevant validation table."
  :type valid-tablep
  :body (valid-table (irr-filepath) nil nil nil (irr-uid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-table-option
  valid-table
  :short "Fixtype of optional validation tables."
  :pred valid-table-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-composite-with-table ((x typep)
                                   (y typep)
                                   (table valid-tablep)
                                   (ienv ienvp))
  :returns (mv (composite typep)
               (new-table valid-tablep))
  :short "Construct a composite @(see type) with a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This wraps @(tsee type-composite),
     extracting the @('completions') @('next-uid') from the validation table,
     and updating the values accordingly."))
  (b* (((valid-table table) table)
       ((mv composite completions next-uid)
        (type-composite x y table.completions table.next-uid ienv)))
    (mv composite
        (change-valid-table
          table
          :completions completions
          :next-uid next-uid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod iconst-info
  :short "Fixtype of validation information for integer constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to integer constants,
     i.e. the @(tsee iconst) constructs.
     The information consists of the type of the constant
     (which for now we do not constrain to be an integer type),
     and the numeric value of the constant, as an ACL2 natural number."))
  ((type type)
   (value nat))
  :pred iconst-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod var-info
  :short "Fixtype of validation information for variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that the validator adds to variables,
     i.e. identifiers used as expressions,
     i.e. the @(':ident') case of @(tsee expr).
     The information for a variable consists of
     the type and linkage of the object denoted by the variable,
     as well as the variable's"
    (xdoc::seetopic "uid" "unique identifier")
    "."))
  ((type type)
   (linkage linkage)
   (uid uid))
  :pred var-infop)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-var-info
  :short "An irrelevant validation information for variables."
  :type var-infop
  :body (make-var-info :type (irr-type)
                       :linkage (irr-linkage)
                       :uid (irr-uid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-var-info (x)
  :returns (info var-infop)
  :short "Coerce a value to @(tsee var-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (var-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy VAR-INFOP." x)
            (irr-var-info)))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-const-info
  :short "Fixtype of validation information for constant expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations
     that the validator adds to constant expressions,
     i.e. the @('const') case of @(tsee expr).
     The information for a constant consists of the type."))
  ((type type))
  :pred expr-const-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-string-info
  :short "Fixtype of validation information for string literal expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations
     that the validator adds to string literal expressions,
     i.e. the @('string') case of @(tsee expr).
     The information for a string literal consists of the type."))
  ((type type))
  :pred expr-string-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-arrsub-info
  :short "Fixtype of validation information for array subscript expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations
     that the validator adds to array subscript expressions,
     i.e. the @('arrsub') case of @(tsee expr).
     The information for an array subscript consists of the type."))
  ((type type))
  :pred expr-arrsub-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-funcall-info
  :short "Fixtype of validation information for function call expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations
     that the validator adds to function call expressions,
     i.e. the @('funcall') case of @(tsee expr).
     The information for a function call consists of the type."))
  ((type type))
  :pred expr-funcall-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-unary-info
  :short "Fixtype of validation information for unary expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to unary expressions,
     i.e. the @(':unary') case of @(tsee expr).
     The information for a unary expression consists of its type."))
  ((type type))
  :pred expr-unary-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-binary-info
  :short "Fixtype of validation information for binary expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to binary expressions,
     i.e. the @(':binary') case of @(tsee expr).
     The information for a binary expression consists of its type."))
  ((type type))
  :pred expr-binary-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod param-declor-nonabstract-info
  :short "Fixtype of validation information for
          non-abstract parameter declarators."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to non-abstract parameter declarators,
     i.e. the @(tsee param-declor) fixtype with kind @(':nonabstract').
     The information consists of the type of the declared identifier and a "
    (xdoc::seetopic "uid" "unique identifier")
    "."))
  ((type type)
   (uid uid))
  :pred param-declor-nonabstract-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tyname-info
  :short "Fixtype of validation information for type names."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to type names,
     i.e. the @(tsee tyname) fixtype.
     The information for a type name consists of its denoted type."))
  ((type type))
  :pred tyname-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod init-declor-info
  :short "Fixtype of validation information for initializer declarators."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to initializer declarators,
     i.e. the @(tsee init-declor) fixtype.")
   (xdoc::p
    "The information for an initializer declarator consists of
     the type of (or denoted by) the declared identifier,
     a flag saying whether the identifier is a @('typdef') or not
     (if the flag is @('t') the type is the one denoted by the identifier),
     and an "
    (xdoc::seetopic "uid-option" "optional unique identifier")
    ". Currently, we only assign unique identifiers to
     ordinary identifiers representing an object or function.
     Therefore, only initializer declarators corresponding
     to those such identifiers are annotated with unique identifiers.
     Initializer declarators which correspond to @('typedef') declarations
     are not annotated with a unique identifier."))
  ((type type)
   (typedefp bool)
   (uid? uid-option))
  :pred init-declor-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fundef-info
  :short "Fixtype of validation information for function definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to function definitions.
     The information consists of
     the type of the function (not just the result; the function type),
     and a "
    (xdoc::seetopic "uid" "unique identifier")
    "."))
  ((type type)
   (uid uid))
  :pred fundef-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transunit-info
  :short "Fixtype of validation information for translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to translation units.
     The information consists of
     the final validation table for the translation unit."))
  ((table-end valid-table))
  :pred transunit-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transunit-ensemble-info
  :short "Fixtype of validation information for translation unit ensembles."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to translation unit ensembles.
     The information consists of
     the final validation table for the translation unit ensemble."))
  ((table-end valid-table))
  :pred transunit-ensemble-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  ()
  (std::make-define-config :no-function nil)

  (fty::deffold-reduce annop
    :short "Definition of the predicates that check whether
            the abstract syntax is annotated with validation information."
    :long
    (xdoc::topstring
     (xdoc::p
      "We use @(tsee fty::deffold-reduce) to define these predicates concisely.")
     (xdoc::p
      "The @(':default') value is @('t'),
       meaning that there are no constraints by default.")
     (xdoc::p
      "The @(':combine') operator is @(tsee and),
       because we need to check all the constructs, recursively.")
     (xdoc::p
      "We override the predicate for
       the constructs for which the validator adds information.")
     (xdoc::p
      "Since for now the validator accepts GCC attribute and other extensions
       without actually checking them and their constituents,
       we also have the annotation predicates accept those constructs,
       by overriding those cases to return @('t').")
     (xdoc::p
      "The validator operates on unambiguous abstract syntax,
       which satisfies the @(see unambiguity) predicates.
       Ideally, the annotation predicates should use
       the unambiguity predicates as guards,
       but @(tsee fty::deffold-reduce) does not support that feature yet.
       Thus, for now we add run-time checks, in the form of @(tsee raise),
       for the cases in which the unambiguity predicates do not hold;
       note that @(tsee raise) is logically @('nil'),
       so the annotation predicates are false on ambiguous constructs."))
    :types (ident
            ident-list
            ident-option
            iconst
            iconst-option
            const
            const-option
            attrib-name
            exprs/decls/stmts
            fundef
            ext-declon
            ext-declon-list
            transunit
            filepath-transunit-map
            transunit-ensemble
            code-ensemble)
    :result booleanp
    :default t
    :combine and
    :override
    ((iconst (iconst-infop (iconst->info iconst)))
     (expr :ident (var-infop expr.info))
     (expr :const (and (const-annop expr.const)
                       (expr-const-infop expr.info)))
     (expr :string (expr-string-infop expr.info))
     (expr :arrsub (and (expr-annop expr.arg1)
                        (expr-annop expr.arg2)
                        (expr-arrsub-infop expr.info)))
     (expr :funcall (and (expr-annop expr.fun)
                         (expr-list-annop expr.args)
                         (expr-funcall-infop expr.info)))
     (expr :unary (and (expr-annop expr.arg)
                       (expr-unary-infop expr.info)))
     (expr :sizeof-ambig (raise "Internal error: ambiguous ~x0."
                                (expr-fix expr)))
     (expr :alignof-ambig (raise "Internal error: ambiguous ~x0."
                                 (expr-fix expr)))
     (expr :binary (and (expr-annop expr.arg1)
                        (expr-annop expr.arg2)
                        (expr-binary-infop expr.info)))
     (expr :cast/call-ambig (raise "Internal error: ambiguous ~x0."
                                   (expr-fix expr)))
     (expr :cast/mul-ambig (raise "Internal error: ambiguous ~x0."
                                  (expr-fix expr)))
     (expr :cast/add-ambig (raise "Internal error: ambiguous ~x0."
                                  (expr-fix expr)))
     (expr :cast/sub-ambig (raise "Internal error: ambiguous ~x0."
                                  (expr-fix expr)))
     (expr :cast/and-ambig (raise "Internal error: ambiguous ~x0."
                                  (expr-fix expr)))
     (expr :cast/logand-ambig (raise "Internal error: ambiguous ~x0."
                                     (expr-fix expr)))
     (type-spec :typeof-ambig (raise "Internal error: ambiguous ~x0."
                                     (type-spec-fix type-spec)))
     (align-spec :alignas-ambig (raise "Internal error: ambiguous ~x0."
                                       (align-spec-fix align-spec)))
     (dirabsdeclor :dummy-base (raise "Internal error: ~
                                       dummy base case of ~
                                       direct abstract declarator."))
     (tyname (and (spec/qual-list-annop (tyname->specquals tyname))
                  (absdeclor-option-annop (tyname->declor? tyname))
                  (tyname-infop (tyname->info tyname))))
     (param-declor :nonabstract (and (declor-annop
                                      (param-declor-nonabstract->declor
                                       param-declor))
                                     (param-declor-nonabstract-infop
                                      (param-declor-nonabstract->info
                                       param-declor))))
     (attrib t)
     (attrib-spec t)
     (init-declor (and (declor-annop (init-declor->declor init-declor))
                       (initer-option-annop (init-declor->initer? init-declor))
                       (init-declor-infop (init-declor->info init-declor))))
     (asm-output t)
     (asm-input t)
     (asm-stmt t)
     (stmt :for-ambig (raise "Internal error: ambiguous ~x0."
                             (stmt-fix stmt)))
     (block-item :ambig (raise "Internal error: ambiguous ~x0."
                               (block-item-fix block-item)))
     (amb-expr/tyname (raise "Internal error: ambiguous ~x0."
                             (amb-expr/tyname-fix amb-expr/tyname)))
     (amb-declor/absdeclor (raise "Internal error: ambiguous ~x0."
                                  (amb-declor/absdeclor-fix
                                   amb-declor/absdeclor)))
     (amb-declon/stmt (raise "Internal error: ambiguous ~x0."
                             (amb-declon/stmt-fix amb-declon/stmt)))
     (fundef (and (decl-spec-list-annop (fundef->specs fundef))
                  (declor-annop (fundef->declor fundef))
                  (declon-list-annop (fundef->declons fundef))
                  (comp-stmt-annop (fundef->body fundef))
                  (fundef-infop (fundef->info fundef))))
     (transunit (and (ext-declon-list-annop (transunit->declons transunit))
                     (transunit-infop (transunit->info transunit))))
     (transunit-ensemble (and (filepath-transunit-map-annop
                                (transunit-ensemble->units transunit-ensemble))
                              (transunit-ensemble-infop
                                (transunit-ensemble->info transunit-ensemble)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection abstract-syntax-anno-additional-theroems
  :short "Additional theorems about the annotation predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are in addition to the ones
     generated by @(tsee fty::deffold-reduce).
     These are needed for actual proofs involving the annotation predicates.
     In particular, @(tsee fty::deffold-reduce) does not generate theorems
     for constructs in the @(':override') input;
     so we must supply theorems for those cases."))

  ;; The following theorems are not auto-generated by FTY::DEFFOLD-REDUCE
  ;; because the corresponding constructs are in the :OVERRIDE input.

  ;; theorems about constructors:

  (defruled iconst-annop-of-iconst
    (equal (iconst-annop (iconst core suffix? info))
           (iconst-infop info))
    :enable (iconst-annop identity))

  (defruled expr-annop-of-expr-ident
    (equal (expr-annop (expr-ident ident info))
           (var-infop info))
    :enable (expr-annop identity))

  (defruled expr-annop-of-expr-const
    (equal (expr-annop (expr-const const info))
           (and (const-annop const)
                (expr-const-infop info)))
    :enable (expr-annop identity))

  (defruled expr-annop-of-expr-string
    (equal (expr-annop (expr-string strings info))
           (expr-string-infop info))
    :enable (expr-annop identity))

  (defruled expr-annop-of-expr-arrsub
    (equal (expr-annop (expr-arrsub arg1 arg2 info))
           (and (expr-annop arg1)
                (expr-annop arg2)
                (expr-arrsub-infop info)))
    :expand (expr-annop (expr-arrsub arg1 arg2 info))
    :enable identity)

  (defruled expr-annop-of-expr-funcall
    (equal (expr-annop (expr-funcall fun args info))
           (and (expr-annop fun)
                (expr-list-annop args)
                (expr-funcall-infop info)))
    :expand (expr-annop (expr-funcall fun args info))
    :enable identity)

  (defruled expr-annop-of-expr-unary
    (equal (expr-annop (expr-unary op arg info))
           (and (expr-annop arg)
                (expr-unary-infop info)))
    :expand (expr-annop (expr-unary op arg info))
    :enable identity)

  (defruled expr-annop-of-expr-binary
    (equal (expr-annop (expr-binary op arg1 arg2 info))
           (and (expr-annop arg1)
                (expr-annop arg2)
                (expr-binary-infop info)))
    :expand (expr-annop (expr-binary op arg1 arg2 info))
    :enable identity)

  (defruled tyname-annop-of-tyname
    (equal (tyname-annop (tyname specquals declor? info))
           (and (spec/qual-list-annop specquals)
                (absdeclor-option-annop declor?)
                (tyname-infop info)))
    :expand (tyname-annop (tyname specquals declor? info))
    :enable identity)

  (defruled param-declor-annop-of-param-declor-nonabstract
    (equal (param-declor-annop (param-declor-nonabstract declor info))
           (and (declor-annop declor)
                (param-declor-nonabstract-infop info)))
    :expand (param-declor-annop (param-declor-nonabstract declor info))
    :enable identity)

  (defruled init-declor-annop-of-init-declor
    (equal (init-declor-annop (init-declor declor asm? attribs initer? info))
           (and (declor-annop declor)
                (initer-option-annop initer?)
                (init-declor-infop info)))
    :expand (init-declor-annop (init-declor declor asm? attribs initer? info))
    :enable identity)

  (defruled fundef-annop-of-fundef
    (equal (fundef-annop
            (fundef extension specs declor asm? attribs declons body info))
           (and (decl-spec-list-annop specs)
                (declor-annop declor)
                (declon-list-annop declons)
                (comp-stmt-annop body)
                (fundef-infop info)))
    :expand (fundef-annop
             (fundef extension specs declor asm? attribs declons body info))
    :enable identity)

  (defruled transunit-annop-of-transunit
    (equal (transunit-annop (transunit comment declons info))
           (and (ext-declon-list-annop declons)
                (transunit-infop info)))
    :expand (transunit-annop (transunit comment declons info))
    :enable identity)

  (defruled transunit-ensemble-annop-of-transunit-ensemble
    (equal (transunit-ensemble-annop (transunit-ensemble units info))
           (and (filepath-transunit-map-annop units)
                (transunit-ensemble-infop info)))
    :expand (transunit-ensemble-annop (transunit-ensemble units info))
    :enable identity)

  ;; theorems about accessors:

  (defruled iconst-infop-of-iconst->info
    (implies (iconst-annop iconst)
             (iconst-infop (iconst->info iconst)))
    :enable iconst-annop)

  (defruled var-infop-of-expr-ident->info
    (implies (and (expr-annop expr)
                  (expr-case expr :ident))
             (var-infop (expr-ident->info expr)))
    :enable expr-annop)

  (defruled const-annop-of-expr-const->const
    (implies (and (expr-annop expr)
                  (expr-case expr :const))
             (const-annop (expr-const->const expr)))
    :enable expr-annop)

  (defruled expr-const-infop-of-expr-const->info
    (implies (and (expr-annop expr)
                  (expr-case expr :const))
             (expr-const-infop (expr-const->info expr)))
    :enable expr-annop)

  (defruled expr-string-infop-of-expr-string->info
    (implies (and (expr-annop expr)
                  (expr-case expr :string))
             (expr-string-infop (expr-string->info expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-arrsub->arg1
    (implies (and (expr-annop expr)
                  (expr-case expr :arrsub))
             (expr-annop (expr-arrsub->arg1 expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-arrsub->arg2
    (implies (and (expr-annop expr)
                  (expr-case expr :arrsub))
             (expr-annop (expr-arrsub->arg2 expr)))
    :enable expr-annop)

  (defruled expr-arrsub-infop-of-expr-arrsub->info
    (implies (and (expr-annop expr)
                  (expr-case expr :arrsub))
             (expr-arrsub-infop (expr-arrsub->info expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-funcall->fun
    (implies (and (expr-annop expr)
                  (expr-case expr :funcall))
             (expr-annop (expr-funcall->fun expr)))
    :enable expr-annop)

  (defruled expr-list-annop-of-expr-funcall->args
    (implies (and (expr-annop expr)
                  (expr-case expr :funcall))
             (expr-list-annop (expr-funcall->args expr)))
    :enable expr-annop)

  (defruled expr-funcall-infop-of-expr-funcall->info
    (implies (and (expr-annop expr)
                  (expr-case expr :funcall))
             (expr-funcall-infop (expr-funcall->info expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-unary->arg
    (implies (and (expr-annop expr)
                  (expr-case expr :unary))
             (expr-annop (expr-unary->arg expr)))
    :enable expr-annop)

  (defruled expr-unary-infop-of-expr-unary->info
    (implies (and (expr-annop expr)
                  (expr-case expr :unary))
             (expr-unary-infop (expr-unary->info expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-binary->arg1
    (implies (and (expr-annop expr)
                  (expr-case expr :binary))
             (expr-annop (expr-binary->arg1 expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-binary->arg2
    (implies (and (expr-annop expr)
                  (expr-case expr :binary))
             (expr-annop (expr-binary->arg2 expr)))
    :enable expr-annop)

  (defruled expr-binary-infop-of-expr-binary->info
    (implies (and (expr-annop expr)
                  (expr-case expr :binary))
             (expr-binary-infop (expr-binary->info expr)))
    :enable expr-annop)

  (defruled declor-annop-of-init-declor->declor
    (implies (init-declor-annop init-declor)
             (declor-annop (init-declor->declor init-declor)))
    :enable init-declor-annop)

  (defruled initer-option-annop-of-init-declor->initer?
    (implies (init-declor-annop init-declor)
             (initer-option-annop (init-declor->initer? init-declor)))
    :enable init-declor-annop)

  (defruled init-declor-infop-of-init-declor->info
    (implies (init-declor-annop init-declor)
             (init-declor-infop (init-declor->info init-declor)))
    :enable init-declor-annop)

  (defruled spec/qual-list-annop-of-tyname->specquals
    (implies (tyname-annop tyname)
             (spec/qual-list-annop (tyname->specquals tyname)))
    :enable tyname-annop)

  (defruled absdeclor-option-annop-of-tyname->declor?
    (implies (tyname-annop tyname)
             (absdeclor-option-annop (tyname->declor? tyname)))
    :enable tyname-annop)

  (defruled tyname-infop-of-tyname->info
    (implies (tyname-annop tyname)
             (tyname-infop (tyname->info tyname)))
    :enable tyname-annop)

  (defruled declor-annop-of-param-declor-nonabstract->declor
    (implies (and (param-declor-annop param-declor)
                  (param-declor-case param-declor :nonabstract))
             (declor-annop (param-declor-nonabstract->declor param-declor)))
    :enable param-declor-annop)

  (defruled param-declor-nonabstract-infop-of-param-declor-nonabstract->info
    (implies (and (param-declor-annop param-declor)
                  (param-declor-case param-declor :nonabstract))
             (param-declor-nonabstract-infop
              (param-declor-nonabstract->info param-declor)))
    :enable param-declor-annop)

  (defruled decl-spec-list-annop-of-fundef->specs
    (implies (fundef-annop fundef)
             (decl-spec-list-annop (fundef->specs fundef)))
    :enable fundef-annop)

  (defruled declor-annop-of-fundef->declor
    (implies (fundef-annop fundef)
             (declor-annop (fundef->declor fundef)))
    :enable fundef-annop)

  (defruled declon-list-annop-of-fundef->declons
    (implies (fundef-annop fundef)
             (declon-list-annop (fundef->declons fundef)))
    :enable fundef-annop)

  (defruled comp-stmt-annop-of-fundef->body
    (implies (fundef-annop fundef)
             (comp-stmt-annop (fundef->body fundef)))
    :enable fundef-annop)

  (defruled fundef-infop-of-fundef->info
    (implies (fundef-annop fundef)
             (fundef-infop (fundef->info fundef)))
    :enable fundef-annop)

  (defruled ext-declon-list-annop-of-transunit->declons
    (implies (transunit-annop transunit)
             (ext-declon-list-annop (transunit->declons transunit)))
    :enable transunit-annop)

  (defruled transunit-annop-of-cdr-assoc
    (implies (and (filepath-transunit-map-annop map)
                  (filepath-transunit-mapp map)
                  (omap::assoc filepath map))
             (transunit-annop (cdr (omap::assoc filepath map))))
    :induct t
    :enable (omap::assoc
             filepath-transunit-map-annop))

  (defruled transunit-infop-of-transunit->info
    (implies (transunit-annop transunit)
             (transunit-infop (transunit->info transunit)))
    :enable transunit-annop)

  (defruled filepath-transunit-map-annop-of-transunit-ensemble->units
    (implies (transunit-ensemble-annop ensemble)
             (filepath-transunit-map-annop (transunit-ensemble->units ensemble)))
    :enable transunit-ensemble-annop)

  (defruled transunit-ensemble-infop-of-transunit-ensemble->info
    (implies (transunit-ensemble-annop ensemble)
             (transunit-ensemble-infop (transunit-ensemble->info ensemble)))
    :enable transunit-ensemble-annop)

  ;; Add the above theorems to the rule set.

  (add-to-ruleset
   abstract-syntax-annop-rules
   '(iconst-annop-of-iconst
     expr-annop-of-expr-ident
     expr-annop-of-expr-const
     expr-annop-of-expr-string
     expr-annop-of-expr-arrsub
     expr-annop-of-expr-funcall
     expr-annop-of-expr-unary
     expr-annop-of-expr-binary
     tyname-annop-of-tyname
     param-declor-annop-of-param-declor-nonabstract
     param-declor-nonabstract-infop-of-param-declor-nonabstract->info
     init-declor-annop-of-init-declor
     fundef-annop-of-fundef
     transunit-annop-of-transunit
     transunit-ensemble-annop-of-transunit-ensemble
     iconst-infop-of-iconst->info
     var-infop-of-expr-ident->info
     const-annop-of-expr-const->const
     expr-const-infop-of-expr-const->info
     expr-string-infop-of-expr-string->info
     expr-annop-of-expr-arrsub->arg1
     expr-annop-of-expr-arrsub->arg2
     expr-arrsub-infop-of-expr-arrsub->info
     expr-annop-of-expr-funcall->fun
     expr-list-annop-of-expr-funcall->args
     expr-funcall-infop-of-expr-funcall->info
     expr-annop-of-expr-unary->arg
     expr-unary-infop-of-expr-unary->info
     expr-annop-of-expr-binary->arg1
     expr-annop-of-expr-binary->arg2
     expr-binary-infop-of-expr-binary->info
     declor-annop-of-init-declor->declor
     initer-option-annop-of-init-declor->initer?
     init-declor-infop-of-init-declor->info
     spec/qual-list-annop-of-tyname->specquals
     absdeclor-option-annop-of-tyname->declor?
     tyname-infop-of-tyname->info
     declor-annop-of-param-declor-nonabstract->declor
     decl-spec-list-annop-of-fundef->specs
     declor-annop-of-fundef->declor
     declon-list-annop-of-fundef->declons
     comp-stmt-annop-of-fundef->body
     fundef-infop-of-fundef->info
     ext-declon-list-annop-of-transunit->declons
     transunit-annop-of-cdr-assoc
     transunit-infop-of-transunit->info
     filepath-transunit-map-annop-of-transunit-ensemble->units
     transunit-ensemble-infop-of-transunit-ensemble->info)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-type ((expr exprp))
  :guard (and (expr-unambp expr)
              (expr-annop expr))
  :returns (type typep)
  :short "Type of an expression, from the validation information."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type is calculated from
     the validation information present in the expression,
     without performing any type calculation
     of the kind performed by the validator
     (e.g. this function does not attempt to calculate
     the type of a binary expression based on
     the operator and the types of the operands).
     If there is not enough information,
     the unknown type is returned.")
   (xdoc::p
    "For a conditional information,
     we look at the types of the two branches,
     and if they have exactly the same type,
     we return that type, otherwise we return the unkwnon type.
     If there is no `then' branch, we also return the unknown type.
     This is an approximation."))
  (expr-case
   expr
   :ident (var-info->type expr.info)
   :const (expr-const-info->type expr.info)
   :string (expr-string-info->type expr.info)
   :paren (expr-type expr.inner)
   :gensel (type-unknown)
   :arrsub (expr-arrsub-info->type expr.info)
   :funcall (expr-funcall-info->type expr.info)
   :member (type-unknown)
   :memberp (type-unknown)
   :complit (type-unknown)
   :unary (expr-unary-info->type expr.info)
   :label-addr (type-pointer (type-void))
   :sizeof (type-unknown)
   :alignof (type-unknown)
   :cast (tyname-info->type (tyname->info expr.type))
   :binary (expr-binary-info->type expr.info)
   :cond (b* (((when (expr-option-case expr.then :none)) (type-unknown))
              (expr.then (expr-option-some->val expr.then))
              (then-type (expr-type expr.then))
              (else-type (expr-type expr.else)))
           (if (equal then-type else-type)
               then-type ; = else-type
             (type-unknown)))
   :comma (expr-type expr.next)
   :stmt (type-unknown)
   :tycompat (type-unknown)
   :offsetof (type-unknown)
   :va-arg (type-unknown)
   :extension (expr-type expr.expr)
   :otherwise (prog2$ (impossible) (type-unknown)))
  :measure (expr-count expr)
  :guard-hints (("Goal" :in-theory (enable* abstract-syntax-annop-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initer-type ((initer initerp))
  :guard (and (initer-unambp initer)
              (initer-annop initer))
  :returns (type typep)
  :short "Type of an initializer, from the validation information."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only cover the case of a single initializer,
     for which we return the type of the underlying expression.
     We return the unknown type for a non-single initializer for now."))
  (initer-case
   initer
   :single (expr-type initer.expr)
   :list (type-unknown))
  :guard-hints (("Goal" :in-theory (enable* abstract-syntax-annop-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines stmts-types
  :short "Types of statements and related entities,
          from the validation information."

  (define stmt-types ((stmt stmtp))
    :guard (and (stmt-unambp stmt)
                (stmt-annop stmt))
    :returns (types type-option-setp)
    :parents (validation-information stmts-types)
    :short "Types of a statement, from the validation information."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return a set of optional types:
       a @('nil') means that the statement's may terminate
       without a @('return') (e.g. an expression statement);
       a @('void') means that the statement may terminate
       with a @('return') without an expression;
       and a non-@('void') type means that the statemetn may terminate
       with a @('return') with an expression of that type.")
     (xdoc::p
      "Similarly to @(tsee expr-type),
       the types calculated by this function are an approximation.
       We return the empty set in cases that we do not handle yet.
       This is adequate for the current use of this function,
       but it will need to be suitably extended."))
    (stmt-case
     stmt
     :labeled (stmt-types stmt.stmt)
     :compound (comp-stmt-types stmt.stmt)
     :expr (set::insert nil nil)
     :null-attrib (set::insert nil nil)
     :if (set::insert nil (stmt-types stmt.then))
     :ifelse (set::union (stmt-types stmt.then)
                         (stmt-types stmt.else))
     :switch nil
     :while (set::insert nil (stmt-types stmt.body))
     :dowhile (set::insert nil (stmt-types stmt.body))
     :for-expr nil
     :for-declon nil
     :for-ambig (impossible)
     :goto nil
     :gotoe nil
     :continue nil
     :break nil
     :return (expr-option-case
              stmt.expr?
              :some (set::insert (expr-type stmt.expr?.val) nil)
              :none (set::insert (type-void) nil))
     :return-attrib (set::insert (expr-type stmt.expr) nil)
     :asm nil)
    :measure (stmt-count stmt))

  (define comp-stmt-types ((cstmt comp-stmtp))
    :guard (and (comp-stmt-unambp cstmt)
                (comp-stmt-annop cstmt))
    :returns (types type-option-setp)
    :parents (validation-information stmts/types)
    :short "Types of a compound statement, from the validation information."
    (block-item-list-types (comp-stmt->items cstmt))
    :measure (comp-stmt-count cstmt))

  (define block-item-types ((item block-itemp))
    :guard (and (block-item-unambp item)
                (block-item-annop item))
    :returns (types type-option-setp)
    :parents (validation-information stmts-types)
    :short "Types of a block item, from the validation information."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return a set of optional types, as in @(tsee stmt-types):
       see the documentation of that function for a rationale."))
    (block-item-case
     item
     :declon (set::insert nil nil)
     :stmt (stmt-types item.stmt)
     :ambig (impossible))
    :measure (block-item-count item))

  (define block-item-list-types ((items block-item-listp))
    :guard (and (block-item-list-unambp items)
                (block-item-list-annop items))
    :returns (types type-option-setp)
    :parents (validation-information stmts-types)
    :short "Types of a list of block items, from the validation information."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return a set of optional types, as in @(tsee stmt-types):
       see the documentation of that function for a rationale.")
     (xdoc::p
      "If the list is empty, we return the singleton set with @('nil').
       If the list is not empty,
       we take the union of the types of the first and remaining block items,
       but first we remove @('nil') from the first set (if present).
       The removal is because,
       if the first block item terminates without @('return'),
       the whole list of block items does not necessarily do so;
       it happens only if the rest of the block items in the list does,
       which is accounted for in the set of optional types
       for the rest of the list."))
    (b* (((when (endp items)) (set::insert nil nil))
         (item-types (block-item-types (car items)))
         (items-types (block-item-list-types (cdr items))))
      (set::union (set::delete nil item-types) items-types))
    :measure (block-item-list-count items))

  :verify-guards :after-returns

  :guard-hints (("Goal" :in-theory (enable* abstract-syntax-annop-rules)))

  ///

  (fty::deffixequiv-mutual stmts-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-types ((fundef fundefp))
  :guard (and (fundef-unambp fundef)
              (fundef-annop fundef))
  :returns (types type-setp
                  :hints
                  (("Goal"
                    :in-theory
                    (enable
                     type-setp-when-type-option-setp-and-nil-not-member))))
  :short "Types of the values returned by a function,
          from the validation information."
  :long
  (xdoc::topstring
   (xdoc::p
    "The set of possible types returned by the function is
     the set of possible types returned by the body,
     roughly speaking.
     More precisely, the latter is a set of optional types,
     where @('nil') means that the body terminates without a @('return').
     For a function, this is equivalent to a @('return') without expression.
     Thus, we turn the @('nil') in the set of types, if any, into @('void') type,
     obtaining the set of types (not optional types) of the function's result.
     We use that in the theorem about the function,
     which says that the result,
     which is an optional value in our formal semantics,
     has a type in the set;
     we use @(tsee c::type-of-value-option) to map values to their types,
     and @('nil') to @('void').")
   (xdoc::p
    "Although a function definition has one return type (possibly @('void')),
     its body may return values of slightly different types,
     possibly subject to conversions.
     However, our formal semantics of C does not cover those conversions yet,
     so we adopt the more general view here."))
  (b* ((types (comp-stmt-types (fundef->body fundef)))
       (types (if (set::in nil types)
                  (set::insert (type-void) (set::delete nil types))
                types)))
    types)
  :guard-hints (("Goal" :in-theory (enable* abstract-syntax-annop-rules))))
