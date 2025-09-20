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
(include-book "unambiguity")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (in-theory (enable* abstract-syntax-unambp-rules)))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (:e tau-system))))
(set-induction-depth-limit 0)

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
   :otherwise (type-integerp type))
  :hooks (:fix))

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
    (expr-null-pointer-constp const-expr.expr type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uid
  :short "Fixtype of unique identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are numerical identifiers which are intended
     to be unique to a given variable, function, type name, etc.
     E.g., there may be many variables throughout a program
     with the name @('x'), but all such distinct variables
     will have distinct unique identifiers.")
   (xdoc::p
    "Unique identifiers are assigned during validation
     to aid subsequent analysis.
     By annotating identifiers with their unique alias,
     disambiguation of variables becomes trivial."))
  ((uid nat))
  :pred uidp)

(defirrelevant irr-uid
  :short "An irrelevant unique identifier."
  :type uidp
  :body (uid 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption uid-option
  uid
  :short "Fixtype of optional unique identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unique identifiers are defined in @(tsee uid)."))
  :pred uid-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uid-increment ((uid uidp))
  :returns (new-uid uidp)
  :short "Create a fresh unique identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "This simply increments the numerical value of the unique identifier."))
  (b* (((uid uid) uid))
    (uid (1+ uid.uid)))
  :hooks (:fix))

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

(fty::defprod valid-scope
  :short "Fixtype of validation scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifiers have scopes [C17:6.2.1], which the validator tracks.
     This fixtype contains all the information about a scope,
     which currently only considers the name space of ordinary identifiers.
     We will extend this fixtype to contain additional information,
     particularly about tag of structure, union, and enumeration types."))
  ((ord valid-ord-scope))
  :pred valid-scopep
  ///

  (defrule alistp-of-valid-scope->ord
    (alistp (valid-scope->ord x))
    :enable alistp-when-valid-ord-scopep-rewrite))

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
   (next-uid uidp))
  :pred valid-tablep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-valid-table
  :short "An irrelevant validation table."
  :type valid-tablep
  :body (valid-table (irr-filepath) nil nil (irr-uid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-table-option
  valid-table
  :short "Fixtype of optional validation tables."
  :pred valid-table-optionp)

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
            (irr-var-info))))

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

(fty::defprod initdeclor-info
  :short "Fixtype of validation information for initializer declarators."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to initializer declarators,
     i.e. the @(tsee initdeclor) fixtype.")
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
  :pred initdeclor-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fundef-info
  :short "Fixtype of validation information for function definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to function definitions.
     The information consists of
     the validation table at the start of the function definition,
     the validation table at the start of the body
     (i.e. just after the opening curly brace),
     the type of the function (not just the result; the function type),
     and a "
    (xdoc::seetopic "uid" "unique identifier")
    "."))
  ((table-start valid-table)
   (table-body-start valid-table)
   (type type)
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
          extdecl
          extdecl-list
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
   (expr :unary (and (expr-annop expr.arg)
                     (expr-unary-infop expr.info)))
   (expr :sizeof-ambig (raise "Internal error: ambiguous ~x0."
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
   (initdeclor (and (declor-annop (initdeclor->declor initdeclor))
                    (initer-option-annop (initdeclor->init? initdeclor))
                    (initdeclor-infop (initdeclor->info initdeclor))))
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
   (amb-decl/stmt (raise "Internal error: ambiguous ~x0."
                         (amb-decl/stmt-fix amb-decl/stmt)))
   (fundef (and (decl-spec-list-annop (fundef->spec fundef))
                (declor-annop (fundef->declor fundef))
                (decl-list-annop (fundef->decls fundef))
                (block-item-list-annop (fundef->body fundef))
                (fundef-infop (fundef->info fundef))))
   (transunit (and (extdecl-list-annop (transunit->decls transunit))
                   (transunit-infop (transunit->info transunit))))))

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

  (defruled initdeclor-annop-of-initdeclor
    (equal (initdeclor-annop (initdeclor declor asm? attribs init? info))
           (and (declor-annop declor)
                (initer-option-annop init?)
                (initdeclor-infop info)))
    :expand (initdeclor-annop (initdeclor declor asm? attribs init? info))
    :enable identity)

  (defruled fundef-annop-of-fundef
    (equal (fundef-annop
            (fundef extension spec declor asm? attribs decls body info))
           (and (decl-spec-list-annop spec)
                (declor-annop declor)
                (decl-list-annop decls)
                (block-item-list-annop body)
                (fundef-infop info)))
    :expand (fundef-annop
             (fundef extension spec declor asm? attribs decls body info))
    :enable identity)

  (defruled transunit-annop-of-transunit
    (equal (transunit-annop (transunit decls info))
           (and (extdecl-list-annop decls)
                (transunit-infop info)))
    :expand (transunit-annop (transunit decls info))
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

  (defruled declor-annop-of-initdeclor->declor
    (implies (initdeclor-annop initdeclor)
             (declor-annop (initdeclor->declor initdeclor)))
    :enable initdeclor-annop)

  (defruled initer-option-annop-of-initdeclor->init?
    (implies (initdeclor-annop initdeclor)
             (initer-option-annop (initdeclor->init? initdeclor)))
    :enable initdeclor-annop)

  (defruled initdeclor-infop-of-initdeclor->info
    (implies (initdeclor-annop initdeclor)
             (initdeclor-infop (initdeclor->info initdeclor)))
    :enable initdeclor-annop)

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

  (defruled decl-spec-list-annop-of-fundef->spec
    (implies (fundef-annop fundef)
             (decl-spec-list-annop (fundef->spec fundef)))
    :enable fundef-annop)

  (defruled declor-annop-of-fundef->declor
    (implies (fundef-annop fundef)
             (declor-annop (fundef->declor fundef)))
    :enable fundef-annop)

  (defruled decl-list-annop-of-fundef->decls
    (implies (fundef-annop fundef)
             (decl-list-annop (fundef->decls fundef)))
    :enable fundef-annop)

  (defruled block-item-list-annop-of-fundef->body
    (implies (fundef-annop fundef)
             (block-item-list-annop (fundef->body fundef)))
    :enable fundef-annop)

  (defruled fundef-infop-of-fundef->info
    (implies (fundef-annop fundef)
             (fundef-infop (fundef->info fundef)))
    :enable fundef-annop)

  (defruled extdecl-list-annop-of-transunit->decls
    (implies (transunit-annop transunit)
             (extdecl-list-annop (transunit->decls transunit)))
    :enable transunit-annop)

  (defruled transunit-infop-of-transunit->info
    (implies (transunit-annop transunit)
             (transunit-infop (transunit->info transunit)))
    :enable transunit-annop)

  ;; Add the above theorems to the rule set.

  (add-to-ruleset
   abstract-syntax-annop-rules
   '(iconst-annop-of-iconst
     expr-annop-of-expr-ident
     expr-annop-of-expr-unary
     expr-annop-of-expr-binary
     tyname-annop-of-tyname
     param-declor-annop-of-param-declor-nonabstract
     param-declor-nonabstract-infop-of-param-declor-nonabstract->info
     initdeclor-annop-of-initdeclor
     fundef-annop-of-fundef
     transunit-annop-of-transunit
     iconst-infop-of-iconst->info
     var-infop-of-expr-ident->info
     expr-annop-of-expr-unary->arg
     expr-unary-infop-of-expr-unary->info
     expr-annop-of-expr-binary->arg1
     expr-annop-of-expr-binary->arg2
     expr-binary-infop-of-expr-binary->info
     declor-annop-of-initdeclor->declor
     initer-option-annop-of-initdeclor->init?
     initdeclor-infop-of-initdeclor->info
     spec/qual-list-annop-of-tyname->specquals
     absdeclor-option-annop-of-tyname->declor?
     tyname-infop-of-tyname->info
     declor-annop-of-param-declor-nonabstract->declor
     decl-spec-list-annop-of-fundef->spec
     declor-annop-of-fundef->declor
     decl-list-annop-of-fundef->decls
     block-item-list-annop-of-fundef->body
     fundef-infop-of-fundef->info
     extdecl-list-annop-of-transunit->decls
     transunit-infop-of-transunit->info)))

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
   :const (if (const-case expr.const :int)
              (iconst-info->type
               (iconst->info
                (const-int->unwrap expr.const)))
            (type-unknown))
   :string (type-unknown)
   :paren (expr-type expr.inner)
   :gensel (type-unknown)
   :arrsub (type-unknown)
   :funcall (type-unknown)
   :member (type-unknown)
   :memberp (type-unknown)
   :complit (type-unknown)
   :unary (expr-unary-info->type expr.info)
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
  :guard-hints (("Goal" :in-theory (enable* abstract-syntax-annop-rules)))
  :hooks (:fix))

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
  :guard-hints (("Goal" :in-theory (enable* abstract-syntax-annop-rules)))
  :hooks (:fix))

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
     :compound (block-item-list-types stmt.items)
     :expr (set::insert nil nil)
     :if (set::insert nil (stmt-types stmt.then))
     :ifelse (set::union (stmt-types stmt.then)
                         (stmt-types stmt.else))
     :switch nil
     :while nil
     :dowhile nil
     :for-expr nil
     :for-decl nil
     :for-ambig (impossible)
     :goto nil
     :continue nil
     :break nil
     :return (expr-option-case
              stmt.expr?
              :some (set::insert (expr-type stmt.expr?.val) nil)
              :none (set::insert (type-void) nil))
     :asm nil)
    :measure (stmt-count stmt))

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
     :decl (set::insert nil nil)
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
     More precisely, the latter is a set of optional types
     (see @(tsee block-item-list-types)),
     where @('nil') means that the list of block items
     terminates without a @('return').
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
  (b* ((types (block-item-list-types (fundef->body fundef)))
       (types (if (set::in nil types)
                  (set::insert (type-void) (set::delete nil types))
                types)))
    types)
  :guard-hints (("Goal" :in-theory (enable* abstract-syntax-annop-rules)))
  :hooks (:fix))
