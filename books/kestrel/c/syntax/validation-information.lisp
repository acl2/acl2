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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validation-information
  :parents (syntax-for-tools)
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
    "Due to the approximate representation of types and our lack of constant
     expression evaluation,
     this recognizer is highly overappoximating.
     It will recognize any pointer or integer type."))
  (or (type-case type :pointer)
      (type-integerp type))
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
     For enumeration constants names,
     for now we only track that they are enumeration constants.
     For @('typedef') names, we track the type corresponding to its
     definition.")
   (xdoc::p
    "We will refine this fixtype as we refine our validator."))
  (:objfun ((type type)
            (linkage linkage)
            (defstatus valid-defstatus)))
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

(fty::defprod valid-table
  :short "Fixtype of validation tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "Scopes are treated in a stack-like manner [C17:6.2.1].
     Thus, we define a validation table as
     containing a list (i.e. stack) of scopes.
     The stack grows from right to left:
     the leftmost scope is the top, and the rightmost scope is the bottom;
     in other words, in the nesting of scopes in the stack,
     the leftmost scope is the innermost,
     and the rightmost scope is the outermost
     (i.e. the file scope [C17:6.2.1/4].)")
   (xdoc::p
    "We wrap the list of scopes into a @(tsee fty::defprod)
     for abstraction and extensibility."))
  ((scopes valid-scope-list))
  :pred valid-tablep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-valid-table
  :short "An irrelevant validation table."
  :type valid-tablep
  :body (valid-table nil))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-iconst-info
  :short "An irrelevant validation information for integer constants."
  :type iconst-infop
  :body (make-iconst-info :type (irr-type)
                          :value 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-iconst-info (x)
  :returns (info iconst-infop)
  :short "Coerce a valud to @(tsee iconst-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (iconst-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy ICONST-INFOP." x)
            (irr-iconst-info))))

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
     the type and linkage of the object denoted by the variable."))
  ((type type)
   (linkage linkage))
  :pred var-infop)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-var-info
  :short "An irrelevant validation information for variables."
  :type var-infop
  :body (make-var-info :type (irr-type)
                       :linkage (irr-linkage)))

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

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-expr-unary-info
  :short "An irrelevant validation information for unary expressions."
  :type expr-unary-infop
  :body (make-expr-unary-info :type (irr-type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-expr-unary-info (x)
  :returns (info expr-unary-infop)
  :short "Coerce a value to @(tsee expr-unary-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (expr-unary-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy EXPR-UNARY-INFOP." x)
            (irr-expr-unary-info))))

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

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-expr-binary-info
  :short "An irrelevant validation information for binary expressions."
  :type expr-binary-infop
  :body (make-expr-binary-info :type (irr-type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-expr-binary-info (x)
  :returns (info expr-binary-infop)
  :short "Coerce a value to @(tsee expr-binary-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (expr-binary-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy EXPR-BINARY-INFOP." x)
            (irr-expr-binary-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod block-item-info
  :short "Fixtype of validation information for block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of annotations that
     the validator adds to (for now only some kinds of) block items.
     This information currently consists of
     the validation table at the beginning of the block item."))
  ((table-start valid-table))
  :pred block-item-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-block-item-info
  :short "An irrelevant validation information for block items."
  :type block-item-infop
  :body (block-item-info (irr-valid-table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-block-item-info (x)
  :returns (info block-item-infop)
  :short "Coerce a value to @(tsee block-item-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (block-item-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy BLOCK_ITEM-INFOP." x)
            (irr-block-item-info))))

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

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-tyname-info
  :short "An irrelevant validation information for type names."
  :type tyname-infop
  :body (make-tyname-info :type (irr-type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-tyname-info (x)
  :returns (info tyname-infop)
  :short "Coerce a value to @(tsee tyname-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (tyname-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy TYNAME-INFOP." x)
            (irr-tyname-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fundef-info
  :short "Fixtype of validation information for function definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to function definitions.
     The information consists of
     the validation table at the start of the function definition
     and the validation table at the start of the body
     (i.e. just after the opening curly brace)."))
  ((table-start valid-table)
   (table-body-start valid-table))
  :pred fundef-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-fundef-info
  :short "An irrelevant validation information for function definitions."
  :type fundef-infop
  :body (make-fundef-info :table-start (irr-valid-table)
                          :table-body-start (irr-valid-table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-fundef-info (x)
  :returns (info fundef-infop)
  :short "Coerce a value to @(tsee fundef-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (fundef-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy FUNDEF-INFOP." x)
            (irr-fundef-info))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-transunit-info
  :short "An irrelevant validation information for translation units."
  :type transunit-infop
  :body (make-transunit-info :table-end (irr-valid-table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-transunit-info (x)
  :returns (info transunit-infop)
  :short "Coerce a value to @(tsee transunit-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (transunit-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy TRANSUNIT-INFOP." x)
            (irr-transunit-info))))

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
          transunit-ensemble)
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
   (attrib t)
   (attrib-spec t)
   (asm-output t)
   (asm-input t)
   (asm-stmt t)
   (stmt :for-ambig (raise "Internal error: ambiguous ~x0."
                           (stmt-fix stmt)))
   (block-item :decl (and (decl-annop (block-item-decl->decl block-item))
                          (block-item-infop
                           (block-item-decl->info block-item))))
   (block-item :stmt (and (stmt-annop (block-item-stmt->stmt block-item))
                          (block-item-infop
                           (block-item-stmt->info block-item))))
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

(defruled filepath-transunit-map-annop-when-not-emptyp
  (implies (and (filepath-transunit-mapp map)
                (not (omap::emptyp map)))
           (equal (filepath-transunit-map-annop map)
                  (and (transunit-annop (omap::head-val map))
                       (filepath-transunit-map-annop (omap::tail map)))))
  :enable filepath-transunit-map-annop)

(add-to-ruleset abstract-syntax-annop-rules
                '(filepath-transunit-map-annop-when-not-emptyp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-ensemble-annop ((code code-ensemblep))
  :returns (yes/no booleanp)
  :short "Check if a code ensemble is annotated with validation information."
  (transunit-ensemble-annop (code-ensemble->transunits code))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-type ((expr exprp))
  :guard (expr-unambp expr)
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
   :ident (var-info->type (coerce-var-info expr.info))
   :const (if (const-case expr.const :int)
              (iconst-info->type
               (coerce-iconst-info
                (iconst->info
                 (const-int->unwrap expr.const))))
            (type-unknown))
   :string (type-unknown)
   :paren (expr-type expr.inner)
   :gensel (type-unknown)
   :arrsub (type-unknown)
   :funcall (type-unknown)
   :member (type-unknown)
   :memberp (type-unknown)
   :complit (type-unknown)
   :unary (expr-unary-info->type (coerce-expr-unary-info expr.info))
   :sizeof (type-unknown)
   :alignof (type-unknown)
   :cast (tyname-info->type (coerce-tyname-info (tyname->info expr.type)))
   :binary (expr-binary-info->type (coerce-expr-binary-info expr.info))
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
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stmt-type ((stmt stmtp))
  :guard (stmt-unambp stmt)
  :returns (type? type-optionp)
  :short "Type of a statement, from the validation information."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an optional type:
     @('nil') means that the statement's execution falls through,
     while the @('void') type means that
     the statement terminates execution with a @('return') without expression.")
   (xdoc::p
    "Similarly to @(tsee expr-type),
     the type calculated by this function is an approximation.
     We return the unknown type in cases that we do not handle yet.")
   (xdoc::p
    "If the statement is a return statement with an expression,
     the type of the expression is returned;
     if the return statement has no expression, @('void') is returned.
     For the other kinds of statement, the unknown type is returned.")
   (xdoc::p
    "This is adequate for the current use of this function,
     but it will need to be suitably extended.
     In particular, a statement may have multiple types,
     in the sense of returning values of possibly different types;
     cf. @(tsee valid-stmt).")
   (xdoc::p
    "We relax the return theorem of this function to an optional type,
     as a step towards generalizing this function
     to actually return optional types."))
  (stmt-case
   stmt
   :labeled (stmt-type stmt.stmt)
   :compound (type-unknown)
   :expr nil
   :if (type-unknown)
   :ifelse (type-unknown)
   :switch (type-unknown)
   :while (type-unknown)
   :dowhile (type-unknown)
   :for-expr (type-unknown)
   :for-decl (type-unknown)
   :for-ambig (prog2$ (impossible) (type-unknown))
   :goto (type-unknown)
   :continue (type-unknown)
   :break (type-unknown)
   :return (expr-option-case
            stmt.expr?
            :some (expr-type stmt.expr?.val)
            :none (type-void))
   :asm (type-unknown))
  :measure (stmt-count stmt)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define block-item-type ((item block-itemp))
  :guard (block-item-unambp item)
  :returns (type? type-optionp)
  :short "Type of a block item, from the validation information."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an optional type:
     @('nil') means that the block item's execution falls through,
     while the @('void') type means that
     the block item terminates execution
     with a @('return') without expression."))
  (block-item-case
   item
   :decl nil
   :stmt (stmt-type item.stmt)
   :ambig (prog2$ (impossible) (type-unknown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define block-item-list-type ((items block-item-listp))
  :guard (block-item-list-unambp items)
  :returns (type? type-optionp)
  :short "Type of a list of block items, from the validation information."
  :long
  (xdoc::topstring
   (xdoc::p
    "An empty list returns nothing, so its type is @('nil').
     For a non-empty list, we look at the types of
     the first block items and the rest of the block items.
     If the former is @('nil'), we return the latter.
     If the former is not @('nil'), we return it."))
  (b* (((when (endp items)) nil)
       (item-type? (block-item-type (car items)))
       (items-type? (block-item-list-type (cdr items))))
    (if item-type?
        item-type?
      items-type?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define block-item-valid-table ((item block-itemp))
  :guard (block-item-unambp item)
  :returns (table valid-tablep)
  :short "Validation table at the start of a block item."
  :long
  (xdoc::topstring
   (xdoc::p
    "Validated block items are unambiguous and always contain annotations
     that include the validation table at the beginning of the block item.
     For now we perform a runtime check that should never fail,
     but eventually we should use an annotation guard."))
  (b* ((info (block-item-case
              item
              :decl item.info
              :stmt item.info
              :ambig (impossible)))
       (info (coerce-block-item-info info)))
    (block-item-info->table-start info))
  :hooks (:fix))
