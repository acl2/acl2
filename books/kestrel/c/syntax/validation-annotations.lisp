; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "validation-tables")
(include-book "evaluation")
(include-book "unambiguity")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))

(local (in-theory (enable* abstract-syntax-unambp-rules)))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validation-annotations
  :parents (validation)
  :short "AST annotations generated during validation."
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

(fty::defprod type-vinfo
  :short "Fixtype of validator information consisting of a type."
  ((type type))
  :pred type-vinfop)

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

(fty::defprod const-expr-info
  :short "Fixtype of validation information for constant expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to constant expressions,
     i.e. the @(tsee const-expr) fixtype.
     The information for a constant expression consists of
     its value after evaluation."))
  ((value valuep))
  :pred const-expr-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type-spec-struct-info
  :short "Fixtype of validation information for struct type specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to struct type specifiers,
     i.e. the @(':struct') and @('struct-empty') cases of @(tsee type-spec).
     The information for a struct type specifier consists of
     the corresponding struct type."))
  ((type type
         :reqfix
         (type-case
           type
           :struct type
           :otherwise (make-type-struct
                        :uid (irr-uid)
                        :tunit? nil
                        :tag/members (make-type-struni-tag/members-tagged
                                       :tag (irr-ident))))))
  :require (type-case type :struct)
  :pred type-spec-struct-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type-spec-typedef-info
  :short "Fixtype of validation information for
          @('typedef') name type specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to @('typedef') name type specifiers,
     i.e. the @(':typedef') case of @(tsee type-spec).
     The information for a @('typedef') name type specifier consists of
     the type denoted by the @('typedef') name, as well as the "
    (xdoc::seetopic "uid" "unique identifier")
    " of the @('typedef') name.
     Note that this type is fully expanded:
     since the @(tsee type) fixtype has no case for @('typedef') names,
     the validator expands @('typedef') names to
     their @('typedef')-name-free types
     (see @(tsee valid-type-spec))."))
  ((type type)
   (uid uid))
  :pred type-spec-typedef-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod desiniter-info
  :short "Fixtype of validation information for initializers with optional
          designations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to initializers with optional designations,
     i.e. the @(tsee desiniter) fixtype.
     The information for a initializers with optional designations consists of
     an optional designation.
     When a designation is not present in the syntax,
     the validator may add a designation here
     corresponding to the implicitly initialized subobject."))
  ((designors designor-list))
  :pred desiniter-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod param-declon-info
  :short "Fixtype of validation information for parameter declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to parameter declarations.
     The information consists of the optional type of the declared parameter.
     The type is absent for the special @('(void)') syntax
     that denotes an empty parameter list,
     where the single parameter declaration
     does not actually declare a parameter."))
  ((type type-option))
  :pred param-declon-infop)

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
     and a "
    (xdoc::seetopic "uid" "unique identifier")
    ". An initializer declarator always declares an ordinary identifier
     representing an object, function, or @('typedef') name,
     each of which is assigned a unique identifier;
     thus the unique identifier is always present here."))
  ((type type)
   (typedefp bool)
   (uid uid))
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

(fty::defprod trans-unit-info
  :short "Fixtype of validation information for translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to translation units.
     The information consists of
     the final validation table for the translation unit.
     The table @('scopes') is expected to be a singleton,
     representing the file-scope at the end of the translation unit."))
  ((table-end valid-table))
  :pred trans-unit-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod trans-ensemble-info
  :short "Fixtype of validation information for translation ensembles."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to translation ensembles.
     The information consists of
     the validation information related to identifiers with external linkage,
     the map of structure and union type UIDs to their members,
     and the next unused "
    (xdoc::seetopic "uid" "unique identifier")
    "."))
  ((externals valid-externals)
   (completions type-completions)
   (next-uid uidp))
  :pred trans-ensemble-infop)

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
            hash-if/elif-expr
            hash-if/ifdef/ifndef
            trans-items
            trans-unit
            filepath-trans-unit-map
            trans-ensemble
            code-ensemble)
    :result booleanp
    :default t
    :combine and
    :override
    ((iconst (iconst-infop (iconst->info iconst)))
     (expr :ident (var-infop expr.info))
     (expr :const (and (const-annop expr.const)
                       (type-vinfop expr.info)))
     (expr :string (type-vinfop expr.info))
     (expr :arrsub (and (expr-annop expr.arg1)
                        (expr-annop expr.arg2)
                        (type-vinfop expr.info)))
     (expr :funcall (and (expr-annop expr.fun)
                         (expr-list-annop expr.args)
                         (type-vinfop expr.info)))
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
     (const-expr (and (expr-annop (const-expr->expr const-expr))
                      (const-expr-infop (const-expr->info const-expr))))
     (desiniter (and (designor-list-annop (desiniter->designors desiniter))
                     (initer-annop (desiniter->initer desiniter))
                     (desiniter-infop (desiniter->info desiniter))))
     (type-spec :struct (and (struni-spec-annop type-spec.spec)
                             (type-spec-struct-infop type-spec.info)))
     (type-spec :typedef (type-spec-typedef-infop type-spec.info))
     (type-spec :struct-empty (and (attrib-spec-list-annop type-spec.attribs)
                                   (type-spec-struct-infop type-spec.info)))
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
     (param-declon (and (decl-spec-list-annop
                          (param-declon->specs param-declon))
                        (param-declor-annop (param-declon->declor param-declon))
                        (attrib-spec-list-annop
                          (param-declon->attribs param-declon))
                        (param-declon-infop (param-declon->info param-declon))))
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
     (trans-unit (and (trans-item-list-annop (trans-unit->items trans-unit))
                      (trans-unit-infop (trans-unit->info trans-unit))))
     (trans-ensemble (and (filepath-trans-unit-map-annop
                           (trans-ensemble->units trans-ensemble))
                          (trans-ensemble-infop
                           (trans-ensemble->info
                            trans-ensemble)))))
    :name abstract-syntax-annop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection abstract-syntax-anno-additional-theorems
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
    :enable iconst-annop)

  (defruled expr-annop-of-expr-ident
    (equal (expr-annop (expr-ident ident info))
           (var-infop info))
    :enable expr-annop)

  (defruled expr-annop-of-expr-const
    (equal (expr-annop (expr-const const info))
           (and (const-annop const)
                (type-vinfop info)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-string
    (equal (expr-annop (expr-string strings info))
           (type-vinfop info))
    :enable expr-annop)

  (defruled expr-annop-of-expr-arrsub
    (equal (expr-annop (expr-arrsub arg1 arg2 info))
           (and (expr-annop arg1)
                (expr-annop arg2)
                (type-vinfop info)))
    :expand (expr-annop (expr-arrsub arg1 arg2 info)))

  (defruled expr-annop-of-expr-funcall
    (equal (expr-annop (expr-funcall fun args info))
           (and (expr-annop fun)
                (expr-list-annop args)
                (type-vinfop info)))
    :expand (expr-annop (expr-funcall fun args info)))

  (defruled expr-annop-of-expr-unary
    (equal (expr-annop (expr-unary op arg info))
           (and (expr-annop arg)
                (expr-unary-infop info)))
    :expand (expr-annop (expr-unary op arg info)))

  (defruled expr-annop-of-expr-binary
    (equal (expr-annop (expr-binary op arg1 arg2 info))
           (and (expr-annop arg1)
                (expr-annop arg2)
                (expr-binary-infop info)))
    :expand (expr-annop (expr-binary op arg1 arg2 info)))

  (defruled const-expr-annop-of-const-expr
    (equal (const-expr-annop (const-expr expr info))
           (and (expr-annop expr)
                (const-expr-infop info)))
    :expand (const-expr-annop (const-expr expr info)))

  (defruled desiniter-annop-of-desiniter
    (equal (desiniter-annop (desiniter designors initer info))
           (and (designor-list-annop designors)
                (initer-annop initer)
                (desiniter-infop info)))
    :expand (desiniter-annop (desiniter designors initer info))
    :enable identity)

  (defrule type-spec-annop-of-type-spec-struct
    (equal (type-spec-annop (type-spec-struct spec info))
           (and (struni-spec-annop spec)
                (type-spec-struct-infop info)))
    :expand (type-spec-annop (type-spec-struct spec info))
    :enable identity)

  (defrule type-spec-annop-of-type-spec-typedef
    (equal (type-spec-annop (type-spec-typedef name info))
           (type-spec-typedef-infop info))
    :expand (type-spec-annop (type-spec-typedef name info))
    :enable identity)

  (defrule type-spec-annop-of-type-spec-struct-empty
    (equal (type-spec-annop (type-spec-struct-empty attribs name? info))
           (and (attrib-spec-list-annop attribs)
                (type-spec-struct-infop info)))
    :expand (type-spec-annop (type-spec-struct-empty attribs name? info))
    :enable identity)

  (defruled tyname-annop-of-tyname
    (equal (tyname-annop (tyname specquals declor? info))
           (and (spec/qual-list-annop specquals)
                (absdeclor-option-annop declor?)
                (tyname-infop info)))
    :expand (tyname-annop (tyname specquals declor? info)))

  (defruled param-declon-annop-of-param-declon
    (equal (param-declon-annop (param-declon specs declor attribs info))
           (and (decl-spec-list-annop specs)
                (param-declor-annop declor)
                (attrib-spec-list-annop attribs)
                (param-declon-infop info)))
    :expand (param-declon-annop (param-declon specs declor attribs info)))

  (defruled param-declor-annop-of-param-declor-nonabstract
    (equal (param-declor-annop (param-declor-nonabstract declor info))
           (and (declor-annop declor)
                (param-declor-nonabstract-infop info)))
    :expand (param-declor-annop (param-declor-nonabstract declor info)))

  (defruled init-declor-annop-of-init-declor
    (equal (init-declor-annop (init-declor declor asm? attribs initer? info))
           (and (declor-annop declor)
                (initer-option-annop initer?)
                (init-declor-infop info)))
    :expand (init-declor-annop (init-declor declor asm? attribs initer? info)))

  (defruled fundef-annop-of-fundef
    (equal (fundef-annop
            (fundef extension specs declor asm? attribs declons body info))
           (and (decl-spec-list-annop specs)
                (declor-annop declor)
                (declon-list-annop declons)
                (comp-stmt-annop body)
                (fundef-infop info)))
    :expand (fundef-annop
             (fundef extension specs declor asm? attribs declons body info)))

  (defruled trans-unit-annop-of-trans-unit
    (equal (trans-unit-annop (trans-unit items info))
           (and (trans-item-list-annop items)
                (trans-unit-infop info)))
    :expand (trans-unit-annop (trans-unit items info)))

  (defruled trans-ensemble-annop-of-trans-ensemble
    (equal (trans-ensemble-annop
            (trans-ensemble units resolved-includes info))
           (and (filepath-trans-unit-map-annop units)
                (trans-ensemble-infop info)))
    :expand (trans-ensemble-annop
             (trans-ensemble units resolved-includes info)))

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

  (defruled type-vinfop-of-expr-const->info
    (implies (and (expr-annop expr)
                  (expr-case expr :const))
             (type-vinfop (expr-const->info expr)))
    :enable expr-annop)

  (defruled type-vinfop-of-expr-string->info
    (implies (and (expr-annop expr)
                  (expr-case expr :string))
             (type-vinfop (expr-string->info expr)))
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

  (defruled type-vinfop-of-expr-arrsub->info
    (implies (and (expr-annop expr)
                  (expr-case expr :arrsub))
             (type-vinfop (expr-arrsub->info expr)))
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

  (defruled type-vinfop-of-expr-funcall->info
    (implies (and (expr-annop expr)
                  (expr-case expr :funcall))
             (type-vinfop (expr-funcall->info expr)))
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

  (defruled expr-annop-of-const-expr->expr
    (implies (const-expr-annop const-expr)
             (expr-annop (const-expr->expr const-expr)))
    :enable const-expr-annop)

  (defruled const-expr-infop-of-const-expr->info
    (implies (const-expr-annop const-expr)
             (const-expr-infop (const-expr->info const-expr)))
    :enable const-expr-annop)

  (defruled designor-list-annop-of-desiniter->designors
    (implies (desiniter-annop desiniter)
             (designor-list-annop (desiniter->designors desiniter)))
    :enable desiniter-annop)

  (defruled initer-annop-of-desiniter->initer
    (implies (desiniter-annop desiniter)
             (initer-annop (desiniter->initer desiniter)))
    :enable desiniter-annop)

  (defruled desiniter-infop-of-desiniter->info
    (implies (desiniter-annop desiniter)
             (desiniter-infop (desiniter->info desiniter)))
    :enable desiniter-annop)

  (defrule struni-spec-annop-of-type-spec-struct->spec
    (implies (and (type-spec-annop type-spec)
                  (type-spec-case type-spec :struct))
             (struni-spec-annop (type-spec-struct->spec type-spec)))
    :enable type-spec-annop)

  (defrule type-spec-struct-infop-of-type-spec-struct->info
    (implies (and (type-spec-annop type-spec)
                  (type-spec-case type-spec :struct))
             (type-spec-struct-infop (type-spec-struct->info type-spec)))
    :enable type-spec-annop)

  (defrule type-spec-typedef-infop-of-type-spec-typedef->info
    (implies (and (type-spec-annop type-spec)
                  (type-spec-case type-spec :typedef))
             (type-spec-typedef-infop (type-spec-typedef->info type-spec)))
    :enable type-spec-annop)

  (defrule attrib-spec-list-annop-of-type-spec-struct-empty->attribs
    (implies (and (type-spec-annop type-spec)
                  (type-spec-case type-spec :struct-empty))
             (attrib-spec-list-annop
               (type-spec-struct-empty->attribs type-spec)))
    :enable type-spec-annop)

  (defrule type-spec-struct-infop-of-type-spec-struct-empty->info
    (implies (and (type-spec-annop type-spec)
                  (type-spec-case type-spec :struct-empty))
             (type-spec-struct-infop (type-spec-struct-empty->info type-spec)))
    :enable type-spec-annop)

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

  (defruled decl-spec-list-annop-of-param-declon->specs
    (implies (param-declon-annop param-declon)
             (decl-spec-list-annop (param-declon->specs param-declon)))
    :enable param-declon-annop)

  (defruled param-declor-annop-of-param-declon->declor
    (implies (param-declon-annop param-declon)
             (param-declor-annop (param-declon->declor param-declon)))
    :enable param-declon-annop)

  (defruled attrib-spec-list-annop-of-param-declon->attribs
    (implies (param-declon-annop param-declon)
             (attrib-spec-list-annop (param-declon->attribs param-declon)))
    :enable param-declon-annop)

  (defruled param-declon-infop-of-param-declon->info
    (implies (param-declon-annop param-declon)
             (param-declon-infop (param-declon->info param-declon)))
    :enable param-declon-annop)

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

  (defruled trans-item-list-annop-of-trans-unit->items
    (implies (trans-unit-annop trans-unit)
             (trans-item-list-annop (trans-unit->items trans-unit)))
    :enable trans-unit-annop)

  (defruled trans-unit-annop-of-cdr-assoc
    (implies (and (filepath-trans-unit-map-annop map)
                  (filepath-trans-unit-mapp map)
                  (omap::assoc filepath map))
             (trans-unit-annop (cdr (omap::assoc filepath map))))
    :induct t
    :enable (omap::assoc
             filepath-trans-unit-map-annop))

  (defruled trans-unit-infop-of-trans-unit->info
    (implies (trans-unit-annop trans-unit)
             (trans-unit-infop (trans-unit->info trans-unit)))
    :enable trans-unit-annop)

  (defruled filepath-trans-unit-map-annop-of-trans-ensemble->units
    (implies (trans-ensemble-annop ensemble)
             (filepath-trans-unit-map-annop (trans-ensemble->units ensemble)))
    :enable trans-ensemble-annop)

  (defruled trans-ensemble-infop-of-trans-ensemble->info
    (implies (trans-ensemble-annop ensemble)
             (trans-ensemble-infop (trans-ensemble->info ensemble)))
    :enable trans-ensemble-annop)

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
     const-expr-annop-of-const-expr
     desiniter-annop-of-desiniter
     type-spec-annop-of-type-spec-struct
     type-spec-annop-of-type-spec-typedef
     type-spec-annop-of-type-spec-struct-empty
     tyname-annop-of-tyname
     param-declon-annop-of-param-declon
     param-declor-annop-of-param-declor-nonabstract
     param-declor-nonabstract-infop-of-param-declor-nonabstract->info
     init-declor-annop-of-init-declor
     fundef-annop-of-fundef
     trans-unit-annop-of-trans-unit
     trans-ensemble-annop-of-trans-ensemble
     iconst-infop-of-iconst->info
     var-infop-of-expr-ident->info
     const-annop-of-expr-const->const
     type-vinfop-of-expr-const->info
     type-vinfop-of-expr-string->info
     expr-annop-of-expr-arrsub->arg1
     expr-annop-of-expr-arrsub->arg2
     type-vinfop-of-expr-arrsub->info
     expr-annop-of-expr-funcall->fun
     expr-list-annop-of-expr-funcall->args
     type-vinfop-of-expr-funcall->info
     expr-annop-of-expr-unary->arg
     expr-unary-infop-of-expr-unary->info
     expr-annop-of-expr-binary->arg1
     expr-annop-of-expr-binary->arg2
     expr-binary-infop-of-expr-binary->info
     expr-annop-of-const-expr->expr
     const-expr-infop-of-const-expr->info
     designor-list-annop-of-desiniter->designors
     initer-annop-of-desiniter->initer
     desiniter-infop-of-desiniter->info
     struni-spec-annop-of-type-spec-struct->spec
     type-spec-struct-infop-of-type-spec-struct->info
     type-spec-typedef-infop-of-type-spec-typedef->info
     attrib-spec-list-annop-of-type-spec-struct-empty->attribs
     type-spec-struct-infop-of-type-spec-struct-empty->info
     declor-annop-of-init-declor->declor
     initer-option-annop-of-init-declor->initer?
     init-declor-infop-of-init-declor->info
     spec/qual-list-annop-of-tyname->specquals
     absdeclor-option-annop-of-tyname->declor?
     tyname-infop-of-tyname->info
     declor-annop-of-param-declor-nonabstract->declor
     decl-spec-list-annop-of-param-declon->specs
     param-declor-annop-of-param-declon->declor
     attrib-spec-list-annop-of-param-declon->attribs
     param-declon-infop-of-param-declon->info
     decl-spec-list-annop-of-fundef->specs
     declor-annop-of-fundef->declor
     declon-list-annop-of-fundef->declons
     comp-stmt-annop-of-fundef->body
     fundef-infop-of-fundef->info
     trans-item-list-annop-of-trans-unit->items
     trans-unit-annop-of-cdr-assoc
     trans-unit-infop-of-trans-unit->info
     filepath-trans-unit-map-annop-of-trans-ensemble->units
     trans-ensemble-infop-of-trans-ensemble->info)))

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
   :const (type-vinfo->type expr.info)
   :string (type-vinfo->type expr.info)
   :paren (expr-type expr.inner)
   :gensel (type-unknown)
   :arrsub (type-vinfo->type expr.info)
   :funcall (type-vinfo->type expr.info)
   :member (type-unknown)
   :memberp (type-unknown)
   :complit (type-unknown)
   :unary (expr-unary-info->type expr.info)
   :label-addr (type-pointer (type-void))
   :sizeof (type-unknown-arithmetic)
   :alignof (type-unknown-arithmetic)
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
   :tycompat (type-sint)
   :offsetof (type-unknown-arithmetic)
   :va-arg (type-unknown)
   :extension (expr-type expr.expr)
   :otherwise (prog2$ (impossible) (irr-type)))
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
    :parents (validation-annotations stmts-types)
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
    :parents (validation-annotations stmts-types)
    :short "Types of a compound statement, from the validation information."
    (block-item-list-types (comp-stmt->items cstmt))
    :measure (comp-stmt-count cstmt))

  (define block-item-types ((item block-itemp))
    :guard (and (block-item-unambp item)
                (block-item-annop item))
    :returns (types type-option-setp)
    :parents (validation-annotations stmts-types)
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
    :parents (validation-annotations stmts-types)
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
     Thus, we turn the @('nil') in the set of types, if any,
     into @('void') type,
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
