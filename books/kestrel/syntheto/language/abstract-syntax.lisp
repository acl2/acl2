; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/defset" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/nth" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (language)
  :short "Abstract syntax of Syntheto."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the abstract syntax of the language
     via recursive fixtypes, as commonly done.")
   (xdoc::p
    "This is just for an initial version of the language,
     which is expected to be extended and improved over time."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod identifier
  :short "Fixtype of Syntheto identifiers."
  :long
  (xdoc::topstring-p
   "For now we allow any ACL2 string, which is okay for abstract syntax.
    We will add more restrictions eventually.")
  ((name string))
  :tag :identifier
  :pred identifierp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist identifier-list
  :short "Fixtype of lists of Syntheto identifiers."
  :elt-type identifier
  :true-listp t
  :elementp-of-nil nil
  :pred identifier-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset identifier-set
  :short "Fixtype of osets of identifiers."
  :elt-type identifier
  :elementp-of-nil nil
  :pred identifier-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type
  :short "Fixtype of Syntheto types."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are primitive types for
     booleans (the usual two),
     characters (ISO 8851-1, 8-bit, as in ACL2),
     strings (of the above characters, any length), and
     integers (all of them, unbounded.")
   (xdoc::p
    "There are collection types for
     finite sets of elements of another type,
     finite sequences of elements of another type, and
     finite maps with another type as domain and another type as range.
     These are like built-in polymorphic types.")
   (xdoc::p
    "There is an option type,
     which consists of the values of a base type
     plus an additional distinct value.
     This is like a built-in polymorphic sum type.")
   (xdoc::p
    "There are types with explicit definitions,
     which are referenced by name.
     Note that the primitive and collection types have implicit definitions.
     The actual explicit type definitions
     are formalized elsewhere in the abstract syntax.")
   (xdoc::p
    "Here we capture the types, as syntactic entities,
     that can be used, for instance, as types of variables.
     There are other syntactic types, such as product types,
     that can only be used to define types;
     these are defined elsewhere in the abstract syntax."))
  (:boolean ())
  (:character ())
  (:string ())
  (:integer ())
  (:set ((element type)))
  (:sequence ((element type)))
  (:map ((domain type) (range type)))
  (:option ((base type)))
  (:defined ((name identifier)))
  :pred typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type-list
  :short "Fixtype of lists of Syntheto types."
  :elt-type type
  :true-listp t
  :elementp-of-nil nil
  :pred type-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-type
  type
  :short "Fixtype of optional Syntheto types."
  :pred maybe-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod typed-variable
  :short "Fixtype of Syntheto typed variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "A typed variable consists of
     the name of the variable
     and the type of the variable."))
  ((name identifier)
   (type type))
  :pred typed-variablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist typed-variable-list
  :short "Fixtype of lists of Syntheto typed variables."
  :elt-type typed-variable
  :true-listp t
  :elementp-of-nil nil
  :pred typed-variable-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-typed-variable
  typed-variable
  :short "Fixtype of optional Syntheto typed-variables."
  :pred maybe-typed-variablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection typed-variable-list->name-list ((x typed-variable-listp))
  :result-type identifier-listp
  :short "Lift @(tsee typed-variable->name) to lists."
  (typed-variable->name x)
  ///
  (fty::deffixequiv typed-variable-list->name-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection typed-variable-list->type-list ((x typed-variable-listp))
  :result-type type-listp
  :short "Lift @(tsee typed-variable->type) to lists."
  (typed-variable->type x)
  ///
  (fty::deffixequiv typed-variable-list->type-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum literal
  :short "Fixtype of Syntheto literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are literals for all the primitive types.")
   (xdoc::p
    "We plan to restrict the characters usable in character and string literals
     and also to add certain escapes.")
   (xdoc::p
    "Note that integer literals are non-negative, for simplicity.
     One can use unary minus to negate an integer literal."))
  (:boolean ((value bool)))
  (:character ((value character)))
  (:string ((value string)))
  (:integer ((value nat)))
  :pred literalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum unary-op
  :short "Fixtype of Syntheto unary operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are negation on booleans and negation on integers."))
  (:not ())
  (:minus ())
  :pred unary-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum binary-op
  :short "Fixtype of Syntheto binary operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are
     equality and inequality (for all types),
     orderings (for integers, characters, and strings),
     logical boolean connectives
     (conjunction,
     disjunction,
     forward implication,
     backward implication,
     coimplication),
     and arithmetic (for integers),
     where division rounds towards zero
     and reminder is defined in the usual way."))
  (:eq ())
  (:ne ())
  (:gt ())
  (:ge ())
  (:lt ())
  (:le ())
  (:and ())
  (:or ())
  (:implies ())
  (:implied ())
  (:iff ())
  (:add ())
  (:sub ())
  (:mul ())
  (:div ())
  (:rem ())
  :pred binary-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes expression-fixtypes
  :short "Mutually recursive fixtypes for Syntheto expressions."

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum expression
    :parents (abstract-syntax expression-fixtypes)
    :short "Fixtype of Syntheto expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       literals,
       variables,
       if-then-else expressions (non-strict),
       and function calls.
       These all correspond to ACL2 translated terms.")
     (xdoc::p
      "The type list argument in the function call
       is non-empty for certain built-in Syntheto functions,
       which are polymorphic.
       Examples are functions that operate on sequences.
       The type list consists of actual type arguments
       for the function's formal type parameters:
       that is, it describes the (monomorphic) instance of the function
       used in the call.
       This will be useful also if and when we extend Syntheto
       with more general polymorphic user-defined types and functions.")
     (xdoc::p
      "We have variants when-then-else and unless-then-else of if-then-else:
       when-then-else is just like if-then-else,
       but it may be syntactically represented as
       an early exit in concrete syntax;
       unless-then-else is just liked a flipped if-then-else,
       but it may be syntactically represented as
       an early exit in concrete syntax.
       In ACL2, these are available as ``bindings'' in @(tsee b*),
       but they are not really bindings as such,
       so we do not represent them as bindings.")
     (xdoc::p
      "We have a more general form of ACL2's @(tsee let) bindings,
       which can either bind a single variable to a single-valued expression,
       or multiple variables to a multi-valued expression.
       The latter is like @(tsee mv-let),
       or an @(tsee mv) binder in @(tsee b*).")
     (xdoc::p
      "We also have conditional expressions,
       consisting of sequences of branches,
       where a branch consists of
       a condition expression and
       an expression that computes the value when the condition holds.
       These correspond to @(tsee cond) in ACL2.")
     (xdoc::p
      "In addition, there are unary and binary expressions.
       These are like function calls,
       but syntactically they use operators that are not identifiers
       and have an infix notation in the case of binary expressions.")
     (xdoc::p
      "We have expressions to build multi-valued expressions,
       corresponding to ACL2's @(tsee mv).
       And we have expressions to obtain single-valued components
       of multi-valued expressions, via numeric indices,
       corresponding to ACL2's @(tsee mv-nth).")
     (xdoc::p
      "There are also expressions to construct values of product types.
       There are expressions to obtain the value of a field of a product type.
       There are also expressions to ``update a value of a product type''
       by returning a copied value with some of its fields changed.")
     (xdoc::p
      "There are similar expressions for values of sum types.
       They include the name of an alternative,
       which ``selects'' the type product.
       Note, however, that there are no anonymous product types in Syntheto:
       the summands of a sum type are anonymous product types in a sense,
       but they are not actual Syntheto types.
       This is similar to how @(tsee fty::deftagsum) works.
       In addition, there are expressions to test whether
       a value of a sum type belongs to a named alternative."))
    (:literal ((get literal)))
    (:variable ((name identifier)))
    (:unary ((operator unary-op)
             (operand expression)))
    (:binary ((operator binary-op)
              (left-operand expression)
              (right-operand expression)))
    (:if ((test expression)
          (then expression)
          (else expression)))
    (:when ((test expression)
            (then expression)
            (else expression)))
    (:unless ((test expression)
              (then expression)
              (else expression)))
    (:cond ((branches branch-list)))
    (:call ((function identifier)
            (types type-list)
            (arguments expression-list)))
    (:multi ((arguments expression-list)))
    (:component ((multi expression)
                 (index nat)))
    (:bind ((variables typed-variable-list)
            (value expression)
            (body expression)))
    (:product-construct ((type identifier)
                         (fields initializer-list)))
    (:product-field ((type identifier)
                     (target expression)
                     (field identifier)))
    (:product-update ((type identifier)
                      (target expression)
                      (fields initializer-list)))
    (:sum-construct ((type identifier)
                     (alternative identifier)
                     (fields initializer-list)))
    (:sum-field ((type identifier)
                 (target expression)
                 (alternative identifier)
                 (field identifier)))
    (:sum-update ((type identifier)
                  (target expression)
                  (alternative identifier)
                  (fields initializer-list)))
    (:sum-test ((type identifier)
                (target expression)
                (alternative identifier)))
    (:bad-expression ((info any)))     ; Used by acl2-to-deep when it can't translate an acl2 s-expression
    :pred expressionp
    :measure (two-nats-measure (acl2-count x) 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist expression-list
    :parents (abstract-syntax expression-fixtypes)
    :short "Fixtype of lists of Syntheto expressions."
    :elt-type expression
    :true-listp t
    :elementp-of-nil nil
    :pred expression-listp
    :measure (two-nats-measure (acl2-count x) 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod branch
    :parents (abstract-syntax expression-fixtypes)
    :short "Fixtype of Syntheto branches."
    ((condition expression)
     (action expression))
    :pred branchp
    :measure (two-nats-measure (acl2-count x) 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist branch-list
    :parents (abstract-syntax expression-fixtypes)
    :short "Fixtype of lists of Syntheto branches."
    :elt-type branch
    :true-listp t
    :elementp-of-nil nil
    :pred branch-listp
    :measure (two-nats-measure (acl2-count x) 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod initializer
    :parents (abstract-syntax expression-fixtypes)
    :short "Fixtype of Syntheto field initializers."
    :long
    (xdoc::topstring
     (xdoc::p
      "These are used in expressions to build values of product and sum types.
       They assign (the value of) an expression to a field by name."))
    ((field identifier)
     (value expression))
    :pred initializerp
    :measure (two-nats-measure (acl2-count x) 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist initializer-list
    :parents (abstract-syntax expression-fixtypes)
    :short "Fixtype of lists of Syntheto field initializers."
    :elt-type initializer
    :true-listp t
    :elementp-of-nil nil
    :pred initializer-listp
    :measure (two-nats-measure (acl2-count x) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-expression
  expression
  :short "Fixtype of optional Syntheto expressions."
  :pred maybe-expressionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expression-variable-list ((x identifier-listp))
  :result-type expression-listp
  :short "Lift @(tsee expression-variable) to lists."
  (expression-variable x)
  ///
  (fty::deffixequiv expression-variable-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expression-product-field-list ((type identifierp)
                                                   (target expressionp)
                                                   (x identifier-listp))
  :result-type expression-listp
  :short "Lift @(tsee expression-product-field) to lists of field names."
  (expression-product-field type target x)
  ///
  (fty::deffixequiv expression-product-field-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expression-sum-field-list ((type identifierp)
                                               (target expressionp)
                                               (alternative identifierp)
                                               (x identifier-listp))
  :result-type expression-listp
  :short "Lift @(tsee expression-sum-field) to lists of field names."
  (expression-sum-field type target alternative x)
  ///
  (fty::deffixequiv expression-sum-field-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection branch-list->condition-list ((x branch-listp))
  :result-type expression-listp
  :short "Lift @(tsee branch->condition) to lists."
  (branch->condition x)
  ///
  (fty::deffixequiv branch-list->condition-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection initializer-list->value-list ((x initializer-listp))
  :result-type expression-listp
  :short "Lift @(tsee initializer->value) to lists."
  (initializer->value x)
  ///
  (fty::deffixequiv initializer-list->value-list)

  (defrule expression-count-of-initializer-list->value-list
    (<= (expression-list-count (initializer-list->value-list inits))
        (initializer-list-count inits))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable expression-list-count
                                       initializer-list-count)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod field
  :short "Fixtype of Syntheto fields."
  :long
  (xdoc::topstring
   (xdoc::p
    "Product types have fields.
     Each field has a name and a type."))
  ((name identifier)
   (type type))
  :pred fieldp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist field-list
  :short "Fixtype of lists of Syntheto type fields."
  :elt-type field
  :true-listp t
  :elementp-of-nil nil
  :pred field-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection field-list->name-list ((x field-listp))
  :result-type identifier-listp
  :short "Lift @(tsee field->name) to lists."
  (field->name x)
  ///
  (fty::deffixequiv field-list->name-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection field-list->type-list ((x field-listp))
  :result-type type-listp
  :short "Lift @(tsee field->type) to lists."
  (field->type x)
  ///
  (fty::deffixequiv field-list->type-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type-product
  :short "Fixtype of Syntheto type products."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like a cartesian product of types,
     where each factor has a name,
     so it is in fact a list of type fields.
     In addition, there is an optional invariant expression,
     which, if present, must be boolean-valued
     and must have the field names as its only variables.
     The idea is that
     only the combinations of fields that satisfy the expression
     are part of the type.
     When the expression is absent, all combinations are part of the type."))
  ((fields field-list)
   (invariant maybe-expression))
  :pred type-productp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-type-product
  type-product
  :short "Fixtype of optional Syntheto type products."
  :pred maybe-type-productp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod alternative
  :short "Fixtype of Syntheto alternatives."
  :long
  (xdoc::topstring
   (xdoc::p
    "Sum types consist of alternatives.
     Each alternative has a name and a type product,
     which contains the fields, and optionally an invariant,
     for that alternative."))
  ((name identifier)
   (product type-product))
  :pred alternativep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist alternative-list
  :short "Fixtype of lists of Syntheto type alternatives."
  :elt-type alternative
  :true-listp t
  :elementp-of-nil nil
  :pred alternative-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection alternative-list->name-list ((x alternative-listp))
  :result-type identifier-listp
  :short "Lift @(tsee alternative->name) to lists."
  (alternative->name x)
  ///
  (fty::deffixequiv alternative-list->name-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type-sum
  :short "Fixtype of Syntheto type sums."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like a disjoint sum of types,
     where each summand has a name.
     Each summand also has fields an an optional invariant,
     i.e. it has a type product.")
   (xdoc::p
    "So a type sum is a sum of product types, specifically
     i.e. not a sum of arbitrary types.
     This is not a limitation of course,
     because one can have a singleton product type.
     This ``asymmetry'' between product and sum types
     is typical of this kind of type systems,
     including ACL2's FTY library,
     which Syntheto provides a wrapper for."))
  ((alternatives alternative-list))
  :pred type-sump)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-type-sum
  type-sum
  :short "Fixtype of optional Syntheto type sums."
  :pred maybe-type-sump)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type-subset
  :short "Fixtype of Syntheto type subsets."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a subset of another type.
     It consists, syntactically, of the supertype
     and an expression that must be boolean-valued
     and must have a single free variable of the supertype.")
   (xdoc::p
    "This is related to the invariants of type products,
     but it is convenient to have (optional) invariants in the type products,
     rather than forcing the user to
     give a name to the product without invariant
     and then define the subtype of the product type.")
   (xdoc::p
    "The field @('variable') must match the free variable in @('restriction').")
   (xdoc::p
    "A type subset also includes an optional witness expression.
     If present, this must be a ground expression
     that evaluates to a value satisfying the restriction.
     If absent, such an expression must be inferred in some way.
     This witness is needed to show that the subtype is inhabited,
     which is used to defined the fixer of the ACL2 fixtype
     generated for the Syntheto fixtype."))
  ((supertype type)
   (variable identifier)
   (restriction expression)
   (witness maybe-expression))
  :pred type-subsetp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-type-subset
  type-subset
  :short "Fixtype of optional Syntheto type subsets."
  :pred maybe-type-subsetp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type-definer
  :short "Fixtype of Syntheto type definers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the possible definers of Syntheto types;
     they are the ``right sides'' of a type definition,
     where the ``left side'' is the name of the type being defined.")
   (xdoc::p
    "The possible definers are
     type products, type sums, and type subsets.
     For now we do not allow other types (see @(tsee type)),
     and in particular we do not allow type synonyms."))
  (:product ((get type-product)))
  (:sum ((get type-sum)))
  (:subset ((get type-subset)))
  :pred type-definerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-type-definer
  type-definer
  :short "Fixtype of optional type definers."
  :pred maybe-type-definerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type-definition
  :short "Fixtype of Syntheto type definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type definition consists of
     the name of the type being defined
     and the definer for the type."))
  ((name identifier)
   (body type-definer))
  :pred type-definitionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type-definition-list
  :short "Fixtype of lists of Syntheto type definitions."
  :elt-type type-definition
  :true-listp t
  :elementp-of-nil nil
  :pred type-definition-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-type-definition
  type-definition
  :short "Fixtype of optional type definitions."
  :pred maybe-type-definitionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-definition-list->name-list ((x type-definition-listp))
  :result-type identifier-listp
  :short "Lift @(tsee type-definition->name) to lists."
  (type-definition->name x)
  ///
  (fty::deffixequiv type-definition-list->name-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type-recursion
  :short "Fixtype of Syntheto type recursions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These serve to group mutually recursive type definitions."))
  ((definitions type-definition-list))
  :pred type-recursionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod function-header
  :short "Fixtype of Syntheto function headers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function header consists of
     the name of the function,
     its inputs (a list of typed variables),
     and its outputs (a list of typed variables.")
   (xdoc::p
    "It is useful to introduce this notion because in Syntheto
     not all functions are defined;
     some are specified, sometimes intentionally under-specified,
     and the goal of the synthesis process is to
     generate definitions that provably meet the specifications."))
  ((name identifier)
   (inputs typed-variable-list)
   (outputs typed-variable-list))
  :pred function-headerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist function-header-list
  :short "Fixtype of lists of Syntheto function headers."
  :elt-type function-header
  :true-listp t
  :elementp-of-nil nil
  :pred function-header-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection function-header-list->name-list ((x function-header-listp))
  :result-type identifier-listp
  :short "Lift @(tsee function-header->name) to lists."
  (function-header->name x)
  ///
  (fty::deffixequiv function-header-list->name-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-function-header
  function-header
  :short "Fixtype of optional function headers."
  :pred maybe-function-headerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum quantifier
  :short "Fixtype of Syntheto quantifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the usual universal and existential quantifiers in logic.")
   (xdoc::p
    "While they have to be part of the language, and are needed in some cases,
     in many cases users may not explicitly need to use them,
     using instead constructs that expand into something with quantifiers
     behind the scenes."))
  (:forall ())
  (:exists ())
  :pred quantifierp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum function-definer
  :short "Fixtype of Syntheto function definers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the possible definers of Syntheto functions.
     They are associated to function headers
     (see @(tsee function-definition).")
   (xdoc::p
    "The possible definers are a regular one consisting of
     an expression that calculates the outputs from the inputs
     (this corresponds to a @(tsee defun) in ACL2),
     and a quantified one consisting of
     a universal or existential quantifier over a list of variables
     with a boolean expression as the matrix
     (this corresponds to a @(tsee defun-sk) in ACL2).
     The regular function definer also has an optional measure expression,
     which may be present only if the function is recursive."))
  (:regular ((body expression)
             (measure maybe-expression)))
  (:quantified ((quantifier quantifier)
                (variables typed-variable-list)
                (matrix expression)))
  :pred function-definerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod function-definition
  :short "Fixtype of Syntheto function definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function definition consists of a function header
     and a function definer.
     It also has an optional precondition
     and an optional postcondition.
     Both must be boolean expressions."))
  ((header function-header)
   (precondition maybe-expression)
   (postcondition maybe-expression)
   (definer function-definer))
  :pred function-definitionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist function-definition-list
  :short "Fixtype of lists of Syntheto function definitions."
  :elt-type function-definition
  :true-listp t
  :elementp-of-nil nil
  :pred function-definition-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection function-definition-list->header-list
  ((x function-definition-listp))
  :result-type function-header-listp
  :short "Lift @(tsee function-definition->header) to lists."
  (function-definition->header x)
  ///
  (fty::deffixequiv function-definition-list->header-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-function-definition
  function-definition
  :short "Fixtype of optional function definitions."
  :pred maybe-function-definitionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod function-recursion
  :short "Fixtype of Syntheto function recursions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These serve to group mutually recursive function definitions."))
  ((definitions function-definition-list))
  :pred function-recursionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum function-specifier
  :short "Fixtype of Syntheto function specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the possible specifiers of Syntheto functions.
     They are associated to function headers
     (see @(tsee function-specification)).")
   (xdoc::p
    "Function specifications correspond to second-order functions in ACL2
     (currently, represented via SOFT macros).
     Thus, functions in Syntheto can be specified via
     the equivalents of @(tsee soft::defun2) and @(tsee soft::defun-sk2),
     which are two possible specifiers.")
   (xdoc::p
    "We also allow, for the case of a specification over a single function,
     a specifier consisting of a boolean expression
     over the inputs and outputs of the function;
     this represents an input/output relation,
     which can be represented as a quantification,
     but it is such a common kind of specification
     that it is worth having a specialized construction for it.
     A particular kind of input/output relation is
     a pre/post-condition relation:
     this can be simply realized via an implication,
     but we might introduce an even more specialized construction
     in the future."))
  (:regular ((body expression)))
  (:quantified ((quantifier quantifier)
                (variables typed-variable-list)
                (matrix expression)))
  (:input-output ((relation expression)))
  :pred function-specifierp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod function-specification
  :short "Fixtype of Syntheto function specifications."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially a second-order predicate over Syntheto functions.
     A specification defines a set of possible choices for the functions:
     these are exactly the ones for which the second-order predicate is true.
     The synthesis process narrows down the set of choices,
     until a single choice is reached.")
   (xdoc::p
    "Thus, a function specification has a name (of the predicate),
     function headers (the arguments of the predicate),
     and a function specifier.
     The input/output function specifier may be used
     only if there is a single function.")
   (xdoc::p
    "The specifier may refer to the names of other specifications
     as if they were nullary Syntheto functions
     (because the function arguments are implicit).
     This is how these predicates are handled in ACL2."))
  ((name identifier)
   (functions function-header-list)
   (specifier function-specifier))
  :pred function-specificationp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-function-specification
  function-specification
  :short "Fixtype of optional function specifications."
  :pred maybe-function-specificationp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod theorem
  :short "Fixtype of Syntheto theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now this consists of a name,
     a list of universally quantified variables,
     and a formula (a boolean expressions).
     Unlike ACL2, the universally quantified variables
     are explicated, with types."))
  ((name identifier)
   (variables typed-variable-list)
   (formula expression))
  :pred theoremp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-theorem
  theorem
  :short "Fixtype of optional theorems."
  :pred maybe-theoremp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Transforms

(fty::deftagsum transform-argument-value
  :short "Fixtype of tagged transform argument value."
  (:identifier ((name identifier)))
  (:identifier-list ((names identifier-list)))
  (:term ((get expression)))
  (:bool ((val bool)))
  :pred transform-argument-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transform-argument
  :short "Fixtype of Syntheto transform arguments."
  ((name identifier)
   (value transform-argument-value))
  :pred transform-argumentp)

(fty::deflist transform-argument-list
  :short "Fixtype of lists of Syntheto transform arguments."
  :elt-type transform-argument
  :true-listp t
  :elementp-of-nil nil
  :pred transform-argument-listp)

(define lookup-transform-argument ((args transform-argument-listp) (arg-name stringp))
  (if (endp args)
      nil
    (b* (((transform-argument arg) (car args)))
      (if (equal arg-name (identifier->name arg.name))
          (let ((arg-val arg.value))
            (transform-argument-value-case arg-val
              :identifier arg-val.name
              :identifier-list arg-val.names
              :term arg-val.get
              :bool arg-val.val))
        (lookup-transform-argument (cdr args) arg-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transform
  :short "Fixtype of Syntheto transforms."
  :long
  (xdoc::topstring-p
   "Apply transform-name to old-function-name with arguments giving new-function-name.")
  ((new-function-name identifier)
   (old-function-name identifier)
   (transform-name string)
   (arguments transform-argument-list))
  :pred transformp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transform
  :short "Fixtype of Syntheto transforms."
  :long
  (xdoc::topstring-p
   "Apply transform-name to old-function-name with arguments giving new-function-name.")
  ((new-function-name identifier)
   (old-function-name identifier)
   (transform-name string)
   (arguments transform-argument-list))
  :pred transformp)

;; Map from transform names to parameter info
;; For each legal parameter it gives its type and, if optional, the default value
;; The old- identifiers must already exist and the new- must not currently exist
;; The var- identifiers are local variable identifiers
;; The type- identifiers are type identifiers
;; The function- identifiers are function identifiers
(defconst *transform-argument-table*
  '(("tail_recursion" ("new_parameter_name" new-var-identifier syndef::|r|)
                      ("make_wrapper?" bool nil)
                      ("wrapper_name" new-function-identifier nil))
    ("simplify")
    ("rename_param" ("old" old-var-identifier)
                    ("new" new-var-identifier))
    ("restrict" ("predicate" expression))
    ("flatten_param" ("old" old-var-identifier)
                     ("new" new-var-identifier-list))
    ("isomorphism" ("parameter" old-var-identifier)
                   ("new_parameter_name" new-var-identifier nil)
                   ("old_type" old-function-identifier)
                   ("new_type" old-function-identifier)
                   ("old_to_new" old-function-identifier)
                   ("new_to_old" old-function-identifier)
                   ("simplify" bool nil))
    ("wrap_output" ("wrap_function" old-function-identifier)
                   ("simplify" bool nil))
    ("finite_difference" ("expression" expression)
                         ("rules" old-identifier-list nil)
                         ("new_parameter_name" new-var-identifier syndef::|r|)
                         ("simplify" bool nil))
    ("drop_irrelevant_parameter" ("parameter" old-var-identifier)
                                 ("make_wrapper?" bool nil))))

(define extract-default-param-alist ((arg-info alistp))
  (if (or (endp arg-info)
          (< (len (car arg-info))
             2))
      ()
    (let ((r (extract-default-param-alist (cdr arg-info)))
          (param (caar arg-info))
          (val (cdar arg-info)))
      (if (or (null (consp val))
              (null (consp (cdr val))))
          r
        (cons (cons param (cadr val))
              r)))))

(define create-arg-defaults-table ((transfm-info alistp))
  (if (or (endp transfm-info)
          (not (alistp (cdar transfm-info))))
      ()
    (cons (cons (caar transfm-info)
                (extract-default-param-alist (cdar transfm-info)))
          (create-arg-defaults-table (cdr transfm-info)))))

(defconst *transform-argument-defaults-table*
  (create-arg-defaults-table *transform-argument-table*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum toplevel
  :short "Fixtype of Syntheto top-level constructs."
  :long
  (xdoc::topstring
   (xdoc::p
    "At the top level, Syntheto allows
     type definitions, function definitions, and function specifications."))
  (:type ((get type-definition)))
  (:types ((get type-recursion)))
  (:function ((get function-definition)))
  (:functions ((get function-recursion)))
  (:specification ((get function-specification)))
  (:theorem ((get theorem)))
  (:transform ((get transform)))
  :pred toplevelp)


(define toplevel-name ((top toplevelp))
  :returns (nm stringp)
  (if (toplevelp top)
      (toplevel-case top
        :type (identifier->name (type-definition->name top.get))
        :types (let ((tys (type-recursion->definitions top.get)))
                 (if (endp tys)             ; Shouldn't happen
                     ""
                   (identifier->name (type-definition->name (car tys)))))
        :function (identifier->name (function-header->name (function-definition->header top.get)))
        :functions (let ((fns (function-recursion->definitions top.get)))
                     (if (endp fns)         ; Shouldn't happen
                         ""
                       (identifier->name (function-header->name (function-definition->header (car fns))))))
        :specification (identifier->name (function-specification->name top.get))
        :theorem (identifier->name (theorem->name top.get))
        :transform (identifier->name (transform->new-function-name top.get)))
    ""))

(define function-definition-names ((fns function-definition-listp))
  :returns (nms string-listp)
  (if (endp fns)
      ()
    (cons (identifier->name (function-header->name (function-definition->header (car fns))))
          (function-definition-names (cdr fns)))))

(define toplevel-fn-names ((top toplevelp))
  :returns (nms string-listp)
  (if (toplevelp top)
     (case (toplevel-kind top)
       (:function
        (function-definition-names (list (toplevel-function->get top))))
       (:functions
        (function-definition-names (function-recursion->definitions (toplevel-functions->get top))))
       (otherwise ()))
    ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist toplevel-list
  :short "Fixtype of lists of Syntheto top-level constructs."
  :elt-type toplevel
  :true-listp t
  :elementp-of-nil nil
  :pred toplevel-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod program
  :short "Fixtype of Syntheto programs."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now this just consists of a list of top-level constructs.
     It may be extended with other information in the future."))
  ((tops toplevel-list))
  :pred programp)
