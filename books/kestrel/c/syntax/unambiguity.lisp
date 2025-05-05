; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-operations")
(include-book "defpred")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unambiguity
  :parents (syntax-for-tools)
  :short "Unambiguity of the C abstract syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    " includes ambiguous constructs,
     i.e. constructs that capture syntactically ambiguous constructs;
     see the documentation of the abstract syntax for details.
     The @(see disambiguator), if successful,
     removes those constructs, leaving only the unambiguous ones.")
   (xdoc::p
    "Here we define predicates over the abstract syntax
     that say whether the constructs are unambiguous,
     i.e. whether there are no ambiguous constructs.")
   (xdoc::p
    "For now we do not make any checks on GCC extensions,
     even though they may contain expressions.
     This mirrors the treatment in the @(see disambiguator):
     the reason for this (temporary) limitation is explained there.")
   (xdoc::p
    "Besides defining the unambiguity predicates,
     we also provide rules to automate guard and return proofs
     that involve the unambiguity predicates.
     The rules about the fixtype deconstructors
     automate the guard proofs;
     the rules about the fixtype constructors
     automate the return proofs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpred unambp
  :short "Definition of the unambiguity predicates,
          with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee defpred) to define these predicates concisely.")
   (xdoc::p
    "The @(':default') value is @('t'),
     because constructs like identifiers and constants are unambiguous;
     ambiguities may only exist in expressions, type names, etc.")
   (xdoc::p
    "We override the boilerplate to return @('nil') on
     the fixtype cases with @('ambig') in their names,
     the fixtypes @('amb-...'),
     and the dummy base case of @(tsee dirabsdeclor);
     although the latter is not properly an ambiguous construct,
     we take the opportunity to exclude it here from consideration
     whenever unambiguous constructs are concerned
     (which is for most of the tools, except for parser and disambiguator).")
   (xdoc::p
    "We override the boilerplate to return @('t') on
     GCC attributes, attribute specifiers, and assembler constructs."))
  :default t
  :override
  ((expr :sizeof-ambig nil)
   (expr :cast/call-ambig nil)
   (expr :cast/mul-ambig nil)
   (expr :cast/add-ambig nil)
   (expr :cast/sub-ambig nil)
   (expr :cast/and-ambig nil)
   (type-spec :typeof-ambig nil)
   (align-spec :alignas-ambig nil)
   (dirabsdeclor :dummy-base nil)
   (attrib t)
   (attrib-spec t)
   (asm-output t)
   (asm-input t)
   (asm-stmt t)
   (stmt :for-ambig nil)
   (block-item :ambig nil)
   (amb-expr/tyname nil)
   (amb-declor/absdeclor nil)
   (amb-decl/stmt nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unambiguity-predicate-theorems
  :short "Theorems about the unambiguity predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are mentioned in @(see unambiguity):
     they support guard and return proofs.
     We plan to extend @(tsee defpred) to generate at least some of these."))

  ;; Theorems for option types (base implies option):

  (defrule expr-option-unambp-when-expr-unambp
    (implies (expr-unambp expr)
             (expr-option-unambp expr))
    :expand (expr-option-unambp expr)
    :enable expr-option-some->val)

  (defrule const-expr-option-unambp-when-const-expr-unambp
    (implies (const-expr-unambp expr)
             (const-expr-option-unambp expr))
    :expand (const-expr-option-unambp expr)
    :enable const-expr-option-some->val)

  (defrule initer-option-unambp-when-initer-unambp
    (implies (initer-unambp initer)
             (initer-option-unambp initer))
    :expand (initer-option-unambp initer)
    :enable initer-option-some->val)

  (defrule declor-option-unambp-when-declor-unambp
    (implies (declor-unambp declor)
             (declor-option-unambp declor))
    :expand (declor-option-unambp declor)
    :enable declor-option-some->val)

  (defrule absdeclor-option-unambp-when-absdeclor-unambp
    (implies (absdeclor-unambp absdeclor)
             (absdeclor-option-unambp absdeclor))
    :expand (absdeclor-option-unambp absdeclor)
    :enable absdeclor-option-some->val)

  (defrule dirabsdeclor-option-unambp-when-dirabsdeclor-unambp
    (implies (dirabsdeclor-unambp dirabsdeclor)
             (dirabsdeclor-option-unambp dirabsdeclor))
    :expand (dirabsdeclor-option-unambp dirabsdeclor)
    :enable dirabsdeclor-option-some->val)

  ;; Theorems for option types (option implies base if not nil):

  (defrule expr-unambp-when-expr-option-unambp-and-not-nil
    (implies (and (expr-option-unambp expr?)
                  expr?)
             (expr-unambp expr?))
    :expand (expr-option-unambp expr?)
    :enable expr-option-some->val)

  (defrule const-expr-unambp-when-const-expr-option-unambp-and-not-nil
    (implies (and (const-expr-option-unambp cexpr?)
                  cexpr?)
             (const-expr-unambp cexpr?))
    :expand (const-expr-option-unambp cexpr?)
    :enable const-expr-option-some->val)

  (defrule initer-unambp-when-initer-option-unambp-and-not-nil
    (implies (and (initer-option-unambp initer?)
                  initer?)
             (initer-unambp initer?))
    :expand (initer-option-unambp initer?)
    :enable initer-option-some->val)

  (defrule declor-unambp-when-declor-option-unambp-and-not-nil
    (implies (and (declor-option-unambp declor?)
                  declor?)
             (declor-unambp declor?))
    :expand (declor-option-unambp declor?)
    :enable declor-option-some->val)

  (defrule absdeclor-unambp-when-absdeclor-option-unambp-and-not-nil
    (implies (and (absdeclor-option-unambp absdeclor?)
                  absdeclor?)
             (absdeclor-unambp absdeclor?))
    :expand (absdeclor-option-unambp absdeclor?)
    :enable absdeclor-option-some->val)

  (defrule dirabsdeclor-unambp-when-dirabsdeclor-option-unambp-and-not-nil
    (implies (and (dirabsdeclor-option-unambp dirabsdeclor?)
                  dirabsdeclor?)
             (dirabsdeclor-unambp dirabsdeclor?))
    :expand (dirabsdeclor-option-unambp dirabsdeclor?)
    :enable dirabsdeclor-option-some->val)

  ;; Theorems for option types (unwrapper of base):

  (defrule expr-unambp-of-expr-option-some->val
    (implies (and (expr-option-unambp expr?)
                  (expr-option-case expr? :some))
             (expr-unambp (expr-option-some->val expr?)))
    :expand (expr-option-unambp expr?))

  (defrule const-expr-unambp-of-const-expr-option-some->val
    (implies (and (const-expr-option-unambp cexpr?)
                  (const-expr-option-case cexpr? :some))
             (const-expr-unambp (const-expr-option-some->val cexpr?)))
    :expand (const-expr-option-unambp cexpr?))

  (defrule initer-unambp-of-initer-option-some->val
    (implies (and (initer-option-unambp initer?)
                  (initer-option-case initer? :some))
             (initer-unambp (initer-option-some->val initer?)))
    :expand (initer-option-unambp initer?))

  (defrule declor-unambp-of-declor-option-some->val
    (implies (and (declor-option-unambp declor?)
                  (declor-option-case declor? :some))
             (declor-unambp (declor-option-some->val declor?)))
    :expand (declor-option-unambp declor?))

  (defrule absdeclor-unambp-of-absdeclor-option-some->val
    (implies (and (absdeclor-option-unambp absdeclor?)
                  (absdeclor-option-case absdeclor? :some))
             (absdeclor-unambp (absdeclor-option-some->val absdeclor?)))
    :expand (absdeclor-option-unambp absdeclor?))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-option-some->val
    (implies (and (dirabsdeclor-option-unambp dirabsdeclor?)
                  (dirabsdeclor-option-case dirabsdeclor? :some))
             (dirabsdeclor-unambp (dirabsdeclor-option-some->val dirabsdeclor?)))
    :expand (dirabsdeclor-option-unambp dirabsdeclor?))

  ;; Theorems for constructors:

  ;; The formulation of rules for
  ;; constructors that are always unambiguous,
  ;; e.g. the rule for constructor EXPR-IDENT,
  ;; are formulated differently from other rules.
  ;; For uniformity with other rules, they should have
  ;; a conclusion like (EXPR-UNAMBP (EXPR-IDENT IDENT INFO)).
  ;; But that fails to apply in proofs,
  ;; such as the ones for the disambiguator.
  ;; Thus, we formulate those rules with conclusion (EXPR-UNAMBP EXPR)
  ;; and hypothesis like (EXPR-CASE EXPR :IDENT),
  ;; which is not ideal because the conclusion is very generic.
  ;; Perhaps there are better ways to do this.

  (defrule expr-unambp-when-ident/const/string
    (implies (member-eq (expr-kind expr) '(:ident :const :string))
             (expr-unambp expr))
    :enable expr-unambp)

  (defrule expr-unambp-of-expr-paren
    (equal (expr-unambp (expr-paren expr))
           (expr-unambp expr))
    :expand (expr-unambp (expr-paren expr)))

  (defrule expr-unambp-of-expr-gensel
    (equal (expr-unambp (expr-gensel control assoc))
           (and (expr-unambp control)
                (genassoc-list-unambp assoc)))
    :expand (expr-unambp (expr-gensel control assoc)))

  (defrule expr-unambp-of-expr-arrsub
    (equal (expr-unambp (expr-arrsub arg1 arg2))
           (and (expr-unambp arg1)
                (expr-unambp arg2)))
    :expand (expr-unambp (expr-arrsub arg1 arg2)))

  (defrule expr-unambp-of-expr-funcall
    (equal (expr-unambp (expr-funcall fun args))
           (and (expr-unambp fun)
                (expr-list-unambp args)))
    :expand (expr-unambp (expr-funcall fun args)))

  (defrule expr-unambp-of-expr-member
    (equal (expr-unambp (expr-member arg name))
           (expr-unambp arg))
    :expand (expr-unambp (expr-member arg name)))

  (defrule expr-unambp-of-expr-memberp
    (equal (expr-unambp (expr-memberp arg name))
           (expr-unambp arg))
    :expand (expr-unambp (expr-memberp arg name)))

  (defrule expr-unambp-of-complit
    (equal (expr-unambp (expr-complit type elems final-comma))
           (and (tyname-unambp type)
                (desiniter-list-unambp elems)))
    :expand (expr-unambp (expr-complit type elems final-comma)))

  (defrule expr-unambp-of-expr-unary
    (equal (expr-unambp (expr-unary op arg info))
           (expr-unambp arg))
    :expand (expr-unambp (expr-unary op arg info)))

  (defrule expr-unambp-of-expr-sizeof
    (equal (expr-unambp (expr-sizeof type))
           (tyname-unambp type))
    :expand (expr-unambp (expr-sizeof type)))

  (defrule expr-unambp-of-expr-alignof
    (equal (expr-unambp (expr-alignof type uscores))
           (tyname-unambp type))
    :expand (expr-unambp (expr-alignof type uscores)))

  (defrule expr-unambp-of-expr-cast
    (equal (expr-unambp (expr-cast type arg))
           (and (tyname-unambp type)
                (expr-unambp arg)))
    :expand (expr-unambp (expr-cast type arg)))

  (defrule expr-unambp-of-expr-binary
    (equal (expr-unambp (expr-binary op arg1 arg2 info))
           (and (expr-unambp arg1)
                (expr-unambp arg2)))
    :expand (expr-unambp (expr-binary op arg1 arg2 info)))

  (defrule expr-unambp-of-expr-cond
    (equal (expr-unambp (expr-cond test then else))
           (and (expr-unambp test)
                (expr-option-unambp then)
                (expr-unambp else)))
    :expand (expr-unambp (expr-cond test then else)))

  (defrule expr-unambp-of-expr-comma
    (equal (expr-unambp (expr-comma first next))
           (and (expr-unambp first)
                (expr-unambp next)))
    :expand (expr-unambp (expr-comma first next)))

  (defrule expr-unambp-of-expr-stmt
    (equal (expr-unambp (expr-stmt items))
           (block-item-list-unambp items))
    :expand (expr-unambp (expr-stmt items)))

  (defrule expr-unambp-of-expr-tycompat
    (equal (expr-unambp (expr-tycompat type1 type2))
           (and (tyname-unambp type1)
                (tyname-unambp type2)))
    :expand (expr-unambp (expr-tycompat type1 type2)))

  (defrule expr-unambp-of-expr-offsetof
    (equal (expr-unambp (expr-offsetof type memdes))
           (and (tyname-unambp type)
                (member-designor-unambp memdes)))
    :expand (expr-unambp (expr-offsetof type memdes)))

  (defrule expr-unambp-of-expr-va-arg
    (equal (expr-unambp (expr-va-arg list type))
           (and (expr-unambp list)
                (tyname-unambp type)))
    :expand (expr-unambp (expr-va-arg list type)))

  (defrule expr-unambp-of-expr-extension
    (equal (expr-unambp (expr-extension expr))
           (expr-unambp expr))
    :expand (expr-unambp (expr-extension expr)))

  (defrule const-expr-unambp-of-const-expr
    (equal (const-expr-unambp (const-expr expr))
           (expr-unambp expr))
    :expand (const-expr-unambp (const-expr expr)))

  (defrule genassoc-unambp-of-genassoc-type
    (equal (genassoc-unambp (genassoc-type type expr))
           (and (tyname-unambp type)
                (expr-unambp expr)))
    :expand (genassoc-unambp (genassoc-type type expr)))

  (defrule genassoc-unambp-of-genassoc-default
    (equal (genassoc-unambp (genassoc-default expr))
           (expr-unambp expr))
    :expand (genassoc-unambp (genassoc-default expr)))

  (defrule member-designor-unambp-when-ident
    (implies (member-designor-case memdes :ident)
             (member-designor-unambp memdes))
    :enable member-designor-unambp)

  (defrule member-designor-unambp-of-member-designor-dot
    (equal (member-designor-unambp (member-designor-dot member name))
           (member-designor-unambp member))
    :expand (member-designor-unambp (member-designor-dot member name)))

  (defrule member-designor-unambp-of-member-designor-sub
    (equal (member-designor-unambp (member-designor-sub member index))
           (and (member-designor-unambp member)
                (expr-unambp index)))
    :expand (member-designor-unambp (member-designor-sub member index)))

  (defrule type-spec-unambp-when-not-atomic/struct/union/enum/typeof
    (implies (not (member-eq (type-spec-kind tyspec)
                             '(:atomic :struct :union :enum
                               :typeof-expr :typeof-type :typeof-ambig)))
             (type-spec-unambp tyspec))
    :enable type-spec-unambp)

  (defrule type-spec-unambp-of-type-spec-atomic
    (equal (type-spec-unambp (type-spec-atomic tyname))
           (tyname-unambp tyname))
    :expand (type-spec-unambp (type-spec-atomic tyname)))

  (defrule type-spec-unambp-of-type-spec-struct
    (equal (type-spec-unambp (type-spec-struct strunispec))
           (strunispec-unambp strunispec))
    :expand (type-spec-unambp (type-spec-struct strunispec)))

  (defrule type-spec-unambp-of-type-spec-union
    (equal (type-spec-unambp (type-spec-union strunispec))
           (strunispec-unambp strunispec))
    :expand (type-spec-unambp (type-spec-union strunispec)))

  (defrule type-spec-unambp-of-type-spec-enum
    (equal (type-spec-unambp (type-spec-enum enumspec))
           (enumspec-unambp enumspec))
    :expand (type-spec-unambp (type-spec-enum enumspec)))

  (defrule type-spec-unambp-of-type-spec-typeof-expr
    (equal (type-spec-unambp (type-spec-typeof-expr expr uscores))
           (expr-unambp expr))
    :expand (type-spec-unambp (type-spec-typeof-expr expr uscores)))

  (defrule type-spec-unambp-of-type-spec-typeof-type
    (equal (type-spec-unambp (type-spec-typeof-type tyname uscores))
           (tyname-unambp tyname))
    :expand (type-spec-unambp (type-spec-typeof-type tyname uscores)))

  (defrule spec/qual-unambp-of-spec/qual-typespec
    (equal (spec/qual-unambp (spec/qual-typespec tyspec))
           (type-spec-unambp tyspec))
    :expand (spec/qual-unambp (spec/qual-typespec tyspec)))

  (defrule spec/qual-unambp-when-typequal
    (implies (eq (spec/qual-kind spec/qual) :typequal)
             (spec/qual-unambp spec/qual))
    :enable spec/qual-unambp)

  (defrule spec/qual-unambp-of-spec/qual-align
    (equal (spec/qual-unambp (spec/qual-align alignspec))
           (align-spec-unambp alignspec))
    :expand (spec/qual-unambp (spec/qual-align alignspec)))

  (defrule spec/qual-unambp-of-spec/qual-attrib
    (equal (spec/qual-unambp (spec/qual-attrib attribspec))
           (attrib-spec-unambp attribspec))
    :expand (spec/qual-unambp (spec/qual-attrib attribspec)))

  (defrule spec/qual-unambp-when-attrib
    (implies (eq (spec/qual-kind spec/qual) :attrib)
             (spec/qual-unambp spec/qual))
    :expand (spec/qual-unambp spec/qual))

  (defrule align-spec-unambp-of-align-spec-alignas-type
    (equal (align-spec-unambp (align-spec-alignas-type tyname))
           (tyname-unambp tyname))
    :expand (align-spec-unambp (align-spec-alignas-type tyname)))

  (defrule align-spec-unambp-of-align-spec-alignas-expr
    (equal (align-spec-unambp (align-spec-alignas-expr cexpr))
           (const-expr-unambp cexpr))
    :expand (align-spec-unambp (align-spec-alignas-expr cexpr)))

  (defrule decl-spec-unambp-of-decl-spec-typespec
    (equal (decl-spec-unambp (decl-spec-typespec tyspec))
           (type-spec-unambp tyspec))
    :expand (decl-spec-unambp (decl-spec-typespec tyspec)))

  (defrule decl-spec-unambp-of-decl-spec-align
    (equal (decl-spec-unambp (decl-spec-align alignspec))
           (align-spec-unambp alignspec))
    :expand (decl-spec-unambp (decl-spec-align alignspec)))

  (defrule decl-spec-unambp-when-not-typespec/align
    (implies (and (not (decl-spec-case declspec :typespec))
                  (not (decl-spec-case declspec :align)))
             (decl-spec-unambp declspec))
    :expand (decl-spec-unambp declspec))

  (defrule initer-unambp-of-initer-single
    (equal (initer-unambp (initer-single expr))
           (expr-unambp expr))
    :expand (initer-unambp (initer-single expr)))

  (defrule initer-unambp-of-initer-list
    (equal (initer-unambp (initer-list elems final-comma))
           (desiniter-list-unambp elems))
    :expand (initer-unambp (initer-list elems final-comma)))

  (defrule desiniter-unambp-of-desiniter
    (equal (desiniter-unambp (desiniter designors init))
           (and (designor-list-unambp designors)
                (initer-unambp init)))
    :expand (desiniter-unambp (desiniter designors init)))

  (defrule designor-unambp-of-designor-sub
    (equal (designor-unambp (designor-sub index))
           (const-expr-unambp index))
    :expand (designor-unambp (designor-sub index)))

  (defrule designor-unambp-of-designor-dot
    (implies (designor-case designor :dot)
             (designor-unambp designor))
    :enable designor-unambp)

  (defrule declor-unambp-of-declor
    (equal (declor-unambp (declor pointers decl))
           (dirdeclor-unambp decl))
    :expand (declor-unambp (declor pointers decl)))

  (defrule dirdeclor-unambp-when-ident
    (implies (dirdeclor-case dirdeclor :ident)
             (dirdeclor-unambp dirdeclor))
    :enable dirdeclor-unambp)

  (defrule dirdeclor-unambp-of-dirdeclor-paren
    (equal (dirdeclor-unambp (dirdeclor-paren declor))
           (declor-unambp declor))
    :expand (dirdeclor-unambp (dirdeclor-paren declor)))

  (defrule dirdeclor-unambp-of-dirdeclor-array
    (equal (dirdeclor-unambp (dirdeclor-array decl quals size?))
           (and (dirdeclor-unambp decl)
                (expr-option-unambp size?)))
    :expand (dirdeclor-unambp (dirdeclor-array decl quals size?)))

  (defrule dirdeclor-unambp-of-dirdeclor-array-static1
    (equal (dirdeclor-unambp (dirdeclor-array-static1 decl quals size))
           (and (dirdeclor-unambp decl)
                (expr-unambp size)))
    :expand (dirdeclor-unambp (dirdeclor-array-static1 decl quals size)))

  (defrule dirdeclor-unambp-of-dirdeclor-array-static2
    (equal (dirdeclor-unambp (dirdeclor-array-static2 decl quals size))
           (and (dirdeclor-unambp decl)
                (expr-unambp size)))
    :expand (dirdeclor-unambp (dirdeclor-array-static2 decl quals size)))

  (defrule dirdeclor-unambp-of-dirdeclor-array-star
    (equal (dirdeclor-unambp (dirdeclor-array-star decl quals))
           (dirdeclor-unambp decl))
    :expand (dirdeclor-unambp (dirdeclor-array-star decl quals)))

  (defrule dirdeclor-unambp-of-dirdeclor-function-params
    (equal (dirdeclor-unambp (dirdeclor-function-params decl params ellipses))
           (and (dirdeclor-unambp decl)
                (param-declon-list-unambp params)))
    :expand (dirdeclor-unambp (dirdeclor-function-params decl params ellipses)))

  (defrule dirdeclor-unambp-of-dirdeclor-function-names
    (equal (dirdeclor-unambp (dirdeclor-function-names decl names))
           (dirdeclor-unambp decl))
    :expand (dirdeclor-unambp (dirdeclor-function-names decl names)))

  (defrule absdeclor-unambp-of-absdeclor
    (equal (absdeclor-unambp (absdeclor pointers direct?))
           (dirabsdeclor-option-unambp direct?))
    :expand (absdeclor-unambp (absdeclor pointers direct?)))

  (defrule not-dirabsdeclor-unambp-when-dummy-base
    (implies (dirabsdeclor-case dirabsdeclor :dummy-base)
             (not (dirabsdeclor-unambp dirabsdeclor)))
    :enable dirabsdeclor-unambp)

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-paren
    (equal (dirabsdeclor-unambp (dirabsdeclor-paren absdeclor))
           (absdeclor-unambp absdeclor))
    :expand (dirabsdeclor-unambp (dirabsdeclor-paren absdeclor)))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-array
    (equal (dirabsdeclor-unambp (dirabsdeclor-array declor? qualspecs size?))
           (and (dirabsdeclor-option-unambp declor?)
                (expr-option-unambp size?)))
    :expand (dirabsdeclor-unambp (dirabsdeclor-array declor? qualspecs size?)))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-array-static1
    (equal (dirabsdeclor-unambp
            (dirabsdeclor-array-static1 declor? qualspecs size))
           (and (dirabsdeclor-option-unambp declor?)
                (expr-unambp size)))
    :expand (dirabsdeclor-unambp
             (dirabsdeclor-array-static1 declor? qualspecs size)))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-array-static2
    (equal (dirabsdeclor-unambp
            (dirabsdeclor-array-static2 declor? qualspecs size))
           (and (dirabsdeclor-option-unambp declor?)
                (expr-unambp size)))
    :expand (dirabsdeclor-unambp
             (dirabsdeclor-array-static2 declor? qualspecs size)))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-array-star
    (equal (dirabsdeclor-unambp (dirabsdeclor-array-star declor?))
           (dirabsdeclor-option-unambp declor?))
    :expand (dirabsdeclor-unambp
             (dirabsdeclor-array-star declor?)))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-function
    (equal (dirabsdeclor-unambp (dirabsdeclor-function declor? params ellipses))
           (and (dirabsdeclor-option-unambp declor?)
                (param-declon-list-unambp params)))
    :expand (dirabsdeclor-unambp (dirabsdeclor-function declor? params ellipses)))

  (defrule param-declon-unambp-of-param-declon
    (equal (param-declon-unambp (param-declon specs decl))
           (and (decl-spec-list-unambp specs)
                (paramdeclor-unambp decl)))
    :expand (param-declon-unambp (param-declon specs decl)))

  (defrule paramdeclor-unambp-of-paramdeclor-declor
    (equal (paramdeclor-unambp (paramdeclor-declor declor))
           (declor-unambp declor))
    :expand (paramdeclor-unambp (paramdeclor-declor declor)))

  (defrule paramdeclor-unambp-of-paramdeclor-absdeclor
    (equal (paramdeclor-unambp (paramdeclor-absdeclor absdeclor))
           (absdeclor-unambp absdeclor))
    :expand (paramdeclor-unambp (paramdeclor-absdeclor absdeclor)))

  (defrule tyname-unambp-of-tyname
    (equal (tyname-unambp (tyname specqual decl?))
           (and (spec/qual-list-unambp specqual)
                (absdeclor-option-unambp decl?)))
    :expand (tyname-unambp (tyname specqual decl?)))

  (defrule strunispec-unambp-of-strunispec
    (equal (strunispec-unambp (strunispec name members))
           (structdecl-list-unambp members))
    :expand (strunispec-unambp (strunispec name members)))

  (defrule structdecl-unambp-of-structdecl-member
    (equal (structdecl-unambp
            (structdecl-member extension specqual declor attrib))
           (and (spec/qual-list-unambp specqual)
                (structdeclor-list-unambp declor)))
    :expand (structdecl-unambp
             (structdecl-member extension specqual declor attrib)))

  (defrule structdecl-unambp-of-structdecl-statassert
    (equal (structdecl-unambp (structdecl-statassert statassert))
           (statassert-unambp statassert))
    :expand (structdecl-unambp (structdecl-statassert statassert)))

  (defrule structdecl-unambp-when-empty
    (implies (structdecl-case sdecl :empty)
             (structdecl-unambp sdecl))
    :enable structdecl-unambp)

  (defrule structdeclor-unambp-of-structdeclor
    (equal (structdeclor-unambp (structdeclor declor? expr?))
           (and (declor-option-unambp declor?)
                (const-expr-option-unambp expr?)))
    :expand (structdeclor-unambp (structdeclor declor? expr?)))

  (defrule enumspec-unambp-of-enumspec
    (equal (enumspec-unambp (enumspec name list final-comma))
           (enumer-list-unambp list))
    :expand (enumspec-unambp (enumspec name list final-comma)))

  (defrule enumer-unambp-of-enumer
    (equal (enumer-unambp (enumer name value))
           (const-expr-option-unambp value))
    :expand (enumer-unambp (enumer name value)))

  (defrule statassert-unambp-of-statassert
    (equal (statassert-unambp (statassert test message))
           (const-expr-unambp test))
    :expand (statassert-unambp (statassert test message)))

  (defrule initdeclor-unambp-of-initdeclor
    (equal (initdeclor-unambp (initdeclor declor asm? attribs init?))
           (and (declor-unambp declor)
                (initer-option-unambp init?)))
    :expand (initdeclor-unambp (initdeclor declor asm? attribs init?)))

  (defrule decl-unambp-of-decl-decl
    (equal (decl-unambp (decl-decl extension specs init))
           (and (decl-spec-list-unambp specs)
                (initdeclor-list-unambp init)))
    :expand (decl-unambp (decl-decl extension specs init)))

  (defrule decl-unambp-of-decl-statassert
    (equal (decl-unambp (decl-statassert statassert))
           (statassert-unambp statassert))
    :expand (decl-unambp (decl-statassert statassert)))

  (defrule label-unambp-of-label-casexpr
    (equal (label-unambp (label-casexpr expr range?))
           (and (const-expr-unambp expr)
                (const-expr-option-unambp range?)))
    :expand (label-unambp (label-casexpr expr range?)))

  (defrule label-unambp-when-not-casexpr
    (implies (not (label-case label :casexpr))
             (label-unambp label))
    :enable label-unambp)

  (defrule label-unambp-of-label-default
    (label-unambp (label-default)))

  (defrule stmt-unambp-of-stmt-labeled
    (equal (stmt-unambp (stmt-labeled label stmt))
           (and (label-unambp label)
                (stmt-unambp stmt)))
    :expand (stmt-unambp (stmt-labeled label stmt)))

  (defrule stmt-unambp-of-stmt-compound
    (equal (stmt-unambp (stmt-compound items))
           (block-item-list-unambp items))
    :expand (stmt-unambp (stmt-compound items)))

  (defrule stmt-unambp-of-stmt-expr
    (equal (stmt-unambp (stmt-expr expr?))
           (expr-option-unambp expr?))
    :expand (stmt-unambp (stmt-expr expr?)))

  (defrule stmt-unambp-of-stmt-if
    (equal (stmt-unambp (stmt-if test then))
           (and (expr-unambp test)
                (stmt-unambp then)))
    :expand (stmt-unambp (stmt-if test then)))

  (defrule stmt-unambp-of-stmt-ifelse
    (equal (stmt-unambp (stmt-ifelse test then else))
           (and (expr-unambp test)
                (stmt-unambp then)
                (stmt-unambp else)))
    :expand (stmt-unambp (stmt-ifelse test then else)))

  (defrule stmt-unambp-of-stmt-switch
    (equal (stmt-unambp (stmt-switch target body))
           (and (expr-unambp target)
                (stmt-unambp body)))
    :expand (stmt-unambp (stmt-switch target body)))

  (defrule stmt-unambp-of-stmt-while
    (equal (stmt-unambp (stmt-while test body))
           (and (expr-unambp test)
                (stmt-unambp body)))
    :expand (stmt-unambp (stmt-while test body)))

  (defrule stmt-unambp-of-stmt-dowhile
    (equal (stmt-unambp (stmt-dowhile body test))
           (and (stmt-unambp body)
                (expr-unambp test)))
    :expand (stmt-unambp (stmt-dowhile body test)))

  (defrule stmt-unambp-of-stmt-for-expr
    (equal (stmt-unambp (stmt-for-expr init test next body))
           (and (expr-option-unambp init)
                (expr-option-unambp test)
                (expr-option-unambp next)
                (stmt-unambp body)))
    :expand (stmt-unambp (stmt-for-expr init test next body)))

  (defrule stmt-unambp-of-stmt-for-decl
    (equal (stmt-unambp (stmt-for-decl init test next body))
           (and (decl-unambp init)
                (expr-option-unambp test)
                (expr-option-unambp next)
                (stmt-unambp body)))
    :expand (stmt-unambp (stmt-for-decl init test next body)))

  (defrule stmt-unambp-when-goto
    (implies (stmt-case stmt :goto)
             (stmt-unambp stmt))
    :enable stmt-unambp)

  (defrule stmt-unambp-of-stmt-continue
    (stmt-unambp (stmt-continue))
    :expand (stmt-unambp (stmt-continue)))

  (defrule stmt-unambp-of-stmt-break
    (stmt-unambp (stmt-break))
    :expand (stmt-unambp (stmt-break)))

  (defrule stmt-unambp-of-stmt-return
    (equal (stmt-unambp (stmt-return expr?))
           (expr-option-unambp expr?))
    :expand (stmt-unambp (stmt-return expr?)))

  (defrule stmt-unambp-of-when-asm
    (implies (stmt-case stmt :asm)
             (stmt-unambp stmt))
    :expand (stmt-unambp stmt))

  (defrule block-item-unambp-of-block-item-decl
    (equal (block-item-unambp (block-item-decl decl))
           (decl-unambp decl))
    :expand (block-item-unambp (block-item-decl decl)))

  (defrule block-item-unambp-of-block-item-stmt
    (equal (block-item-unambp (block-item-stmt stmt))
           (stmt-unambp stmt))
    :expand (block-item-unambp (block-item-stmt stmt)))

  (defrule expr/tyname-unambp-of-expr/tyname-expr
    (equal (expr/tyname-unambp (expr/tyname-expr expr))
           (expr-unambp expr))
    :enable expr/tyname-unambp)

  (defrule expr/tyname-unambp-of-expr/tyname-tyname
    (equal (expr/tyname-unambp (expr/tyname-tyname tyname))
           (tyname-unambp tyname))
    :enable expr/tyname-unambp)

  (defrule declor/absdeclor-unambp-of-declor/absdeclor-declor
    (equal (declor/absdeclor-unambp (declor/absdeclor-declor declor))
           (declor-unambp declor))
    :enable declor/absdeclor-unambp)

  (defrule declor/absdeclor-unambp-of-declor/absdeclor-absdeclor
    (equal (declor/absdeclor-unambp (declor/absdeclor-absdeclor absdeclor))
           (absdeclor-unambp absdeclor))
    :enable declor/absdeclor-unambp)

  (defrule decl/stmt-unambp-of-decl/stmt-decl
    (equal (decl/stmt-unambp (decl/stmt-decl decl))
           (decl-unambp decl))
    :enable decl/stmt-unambp)

  (defrule decl/stmt-unambp-of-decl/stmt-stmt
    (equal (decl/stmt-unambp (decl/stmt-stmt expr))
           (expr-unambp expr))
    :enable decl/stmt-unambp)

  (defrule fundef-unambp-of-fundef
    (equal (fundef-unambp
            (fundef extension spec declor asm? attribs decls body))
           (and (decl-spec-list-unambp spec)
                (declor-unambp declor)
                (decl-list-unambp decls)
                (stmt-unambp body)))
    :enable fundef-unambp)

  (defrule extdecl-unambp-of-extdecl-fundef
    (equal (extdecl-unambp (extdecl-fundef fundef))
           (fundef-unambp fundef))
    :enable extdecl-unambp)

  (defrule extdecl-unambp-of-extdecl-decl
    (equal (extdecl-unambp (extdecl-decl decl))
           (decl-unambp decl))
    :enable extdecl-unambp)

  (defrule extdecl-unambp-when-not-fundef/decl
    (implies (not (member-eq (extdecl-kind edecl) '(:fundef :decl)))
             (extdecl-unambp edecl))
    :enable extdecl-unambp)

  (defrule transunit-unambp-of-transunit
    (equal (transunit-unambp (transunit edecls info))
           (extdecl-list-unambp edecls))
    :enable transunit-unambp)

  (defrule transunit-ensemble-unambp-of-transunit-ensemble
    (equal (transunit-ensemble-unambp (transunit-ensemble tumap))
           (filepath-transunit-map-unambp (filepath-transunit-map-fix tumap)))
    :enable transunit-ensemble-unambp)

  ;; Theorems for deconstructors:

  (defrule expr-unambp-of-expr-paren->inner
    (implies (and (expr-unambp expr)
                  (expr-case expr :paren))
             (expr-unambp (expr-paren->inner expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-gensel->control
    (implies (and (expr-unambp expr)
                  (expr-case expr :gensel))
             (expr-unambp (expr-gensel->control expr)))
    :expand (expr-unambp expr))

  (defrule genassoc-list-unambp-of-expr-gensel->assocs
    (implies (and (expr-unambp expr)
                  (expr-case expr :gensel))
             (genassoc-list-unambp (expr-gensel->assocs expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-arrsub->arg1
    (implies (and (expr-unambp expr)
                  (expr-case expr :arrsub))
             (expr-unambp (expr-arrsub->arg1 expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-arrsub->arg2
    (implies (and (expr-unambp expr)
                  (expr-case expr :arrsub))
             (expr-unambp (expr-arrsub->arg2 expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-funcall->fun
    (implies (and (expr-unambp expr)
                  (expr-case expr :funcall))
             (expr-unambp (expr-funcall->fun expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-funcall->args
    (implies (and (expr-unambp expr)
                  (expr-case expr :funcall))
             (expr-list-unambp (expr-funcall->args expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-member->arg
    (implies (and (expr-unambp expr)
                  (expr-case expr :member))
             (expr-unambp (expr-member->arg expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-memberp->arg
    (implies (and (expr-unambp expr)
                  (expr-case expr :memberp))
             (expr-unambp (expr-memberp->arg expr)))
    :expand (expr-unambp expr))

  (defrule tyname-unambp-of-expr-complit->type
    (implies (and (expr-unambp expr)
                  (expr-case expr :complit))
             (tyname-unambp (expr-complit->type expr)))
    :expand (expr-unambp expr))

  (defrule desiniter-list-unambp-of-expr-complit->elems
    (implies (and (expr-unambp expr)
                  (expr-case expr :complit))
             (desiniter-list-unambp (expr-complit->elems expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-unary->arg
    (implies (and (expr-unambp expr)
                  (expr-case expr :unary))
             (expr-unambp (expr-unary->arg expr)))
    :expand (expr-unambp expr))

  (defrule tyname-unambp-of-expr-sizeof->type
    (implies (and (expr-unambp expr)
                  (expr-case expr :sizeof))
             (tyname-unambp (expr-sizeof->type expr)))
    :expand (expr-unambp expr))

  (defrule tyname-unambp-of-expr-alignof->type
    (implies (and (expr-unambp expr)
                  (expr-case expr :alignof))
             (tyname-unambp (expr-alignof->type expr)))
    :expand (expr-unambp expr))

  (defrule tyname-unambp-of-expr-cast->type
    (implies (and (expr-unambp expr)
                  (expr-case expr :cast))
             (tyname-unambp (expr-cast->type expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-cast->arg
    (implies (and (expr-unambp expr)
                  (expr-case expr :cast))
             (expr-unambp (expr-cast->arg expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-binary->arg1
    (implies (and (expr-unambp expr)
                  (expr-case expr :binary))
             (expr-unambp (expr-binary->arg1 expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-binary->arg2
    (implies (and (expr-unambp expr)
                  (expr-case expr :binary))
             (expr-unambp (expr-binary->arg2 expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-cond->test
    (implies (and (expr-unambp expr)
                  (expr-case expr :cond))
             (expr-unambp (expr-cond->test expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-cond->then
    (implies (and (expr-unambp expr)
                  (expr-case expr :cond))
             (expr-option-unambp (expr-cond->then expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-cond->else
    (implies (and (expr-unambp expr)
                  (expr-case expr :cond))
             (expr-unambp (expr-cond->else expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-comma->first
    (implies (and (expr-unambp expr)
                  (expr-case expr :comma))
             (expr-unambp (expr-comma->first expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-comma->next
    (implies (and (expr-unambp expr)
                  (expr-case expr :comma))
             (expr-unambp (expr-comma->next expr)))
    :expand (expr-unambp expr))

  (defrule block-item-list-unambp-of-expr-stmt->items
    (implies (and (expr-unambp expr)
                  (expr-case expr :stmt))
             (block-item-list-unambp (expr-stmt->items expr)))
    :expand (expr-unambp expr))

  (defrule tyname-unambp-of-expr-tycompat->type1
    (implies (and (expr-unambp expr)
                  (expr-case expr :tycompat))
             (tyname-unambp (expr-tycompat->type1 expr)))
    :expand (expr-unambp expr))

  (defrule tyname-unambp-of-expr-tycompat->type2
    (implies (and (expr-unambp expr)
                  (expr-case expr :tycompat))
             (tyname-unambp (expr-tycompat->type2 expr)))
    :expand (expr-unambp expr))

  (defrule tyname-unambp-of-expr-offsetof->type
    (implies (and (expr-unambp expr)
                  (expr-case expr :offsetof))
             (tyname-unambp (expr-offsetof->type expr)))
    :expand (expr-unambp expr))

  (defrule member-designor-unambp-of-expr-offset->member
    (implies (and (expr-unambp expr)
                  (expr-case expr :offsetof))
             (member-designor-unambp (expr-offsetof->member expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-va-arg->list
    (implies (and (expr-unambp expr)
                  (expr-case expr :va-arg))
             (expr-unambp (expr-va-arg->list expr)))
    :expand (expr-unambp expr))

  (defrule tyname-unambp-of-expr-va-arg->type
    (implies (and (expr-unambp expr)
                  (expr-case expr :va-arg))
             (tyname-unambp (expr-va-arg->type expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-extension->expr
    (implies (and (expr-unambp expr)
                  (expr-case expr :extension))
             (expr-unambp (expr-extension->expr expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-const-expr->expr
    (implies (const-expr-unambp cexpr)
             (expr-unambp (const-expr->expr cexpr)))
    :expand (const-expr-unambp cexpr))

  (defrule tyname-unambp-of-genassoc-type->type
    (implies (and (genassoc-unambp assoc)
                  (genassoc-case assoc :type))
             (tyname-unambp (genassoc-type->type assoc)))
    :expand (genassoc-unambp assoc))

  (defrule expr-unambp-of-genassoc-type->expr
    (implies (and (genassoc-unambp assoc)
                  (genassoc-case assoc :type))
             (expr-unambp (genassoc-type->expr assoc)))
    :expand (genassoc-unambp assoc))

  (defrule expr-unambp-of-genassoc-default->expr
    (implies (and (genassoc-unambp assoc)
                  (genassoc-case assoc :default))
             (expr-unambp (genassoc-default->expr assoc)))
    :expand (genassoc-unambp assoc))

  (defrule member-designor-unambp-of-member-designor-dot->member
    (implies (and (member-designor-unambp memdes)
                  (member-designor-case memdes :dot))
             (member-designor-unambp (member-designor-dot->member memdes)))
    :expand (member-designor-unambp memdes))

  (defrule member-designor-unambp-of-member-designor-sub->member
    (implies (and (member-designor-unambp memdes)
                  (member-designor-case memdes :sub))
             (member-designor-unambp (member-designor-sub->member memdes)))
    :expand (member-designor-unambp memdes))

  (defrule expr-unambp-of-member-designor-dot->index
    (implies (and (member-designor-unambp memdes)
                  (member-designor-case memdes :sub))
             (expr-unambp (member-designor-sub->index memdes)))
    :expand (member-designor-unambp memdes))

  (defrule tyname-unambp-of-type-spec-atomic->type
    (implies (and (type-spec-unambp tyspec)
                  (type-spec-case tyspec :atomic))
             (tyname-unambp (type-spec-atomic->type tyspec)))
    :expand (type-spec-unambp tyspec))

  (defrule strunispec-unambp-of-type-spec-struct->spec
    (implies (and (type-spec-unambp tyspec)
                  (type-spec-case tyspec :struct))
             (strunispec-unambp (type-spec-struct->spec tyspec)))
    :expand (type-spec-unambp tyspec))

  (defrule strunispec-unambp-of-type-spec-union->spec
    (implies (and (type-spec-unambp tyspec)
                  (type-spec-case tyspec :union))
             (strunispec-unambp (type-spec-union->spec tyspec)))
    :expand (type-spec-unambp tyspec))

  (defrule enumspec-unambp-of-type-spec-enum->spec
    (implies (and (type-spec-unambp tyspec)
                  (type-spec-case tyspec :enum))
             (enumspec-unambp (type-spec-enum->spec tyspec)))
    :expand (type-spec-unambp tyspec))

  (defrule type-spec-unambp-of-spec/qual-typespec->spec
    (implies (and (spec/qual-unambp specqual)
                  (spec/qual-case specqual :typespec))
             (type-spec-unambp (spec/qual-typespec->spec specqual)))
    :expand (spec/qual-unambp specqual))

  (defrule align-spec-unambp-of-spec/qual-align->spec
    (implies (and (spec/qual-unambp specqual)
                  (spec/qual-case specqual :align))
             (align-spec-unambp (spec/qual-align->spec specqual)))
    :expand (spec/qual-unambp specqual))

  (defrule tyname-unambp-of-align-spec-alignas-type->type
    (implies (and (align-spec-unambp alignspec)
                  (align-spec-case alignspec :alignas-type))
             (tyname-unambp (align-spec-alignas-type->type alignspec)))
    :expand (align-spec-unambp alignspec))

  (defrule const-expr-unambp-of-align-spec-alignas-expr->expr
    (implies (and (align-spec-unambp alignspec)
                  (align-spec-case alignspec :alignas-expr))
             (const-expr-unambp (align-spec-alignas-expr->expr alignspec)))
    :expand (align-spec-unambp alignspec))

  (defrule type-spec-unambp-of-decl-spec-typespec->spec
    (implies (and (decl-spec-unambp declspec)
                  (decl-spec-case declspec :typespec))
             (type-spec-unambp (decl-spec-typespec->spec declspec)))
    :expand (decl-spec-unambp declspec))

  (defrule align-spec-unambp-of-decl-spec-align->spec
    (implies (and (decl-spec-unambp declspec)
                  (decl-spec-case declspec :align))
             (align-spec-unambp (decl-spec-align->spec declspec)))
    :expand (decl-spec-unambp declspec))

  (defrule expr-unambp-of-initer-single->expr
    (implies (and (initer-unambp initer)
                  (initer-case initer :single))
             (expr-unambp (initer-single->expr initer)))
    :expand (initer-unambp initer))

  (defrule desiniter-list-unambp-of-initer-list->elems
    (implies (and (initer-unambp initer)
                  (initer-case initer :list))
             (desiniter-list-unambp (initer-list->elems initer)))
    :expand (initer-unambp initer))

  (defrule designor-list-unambp-of-desiniter->designors
    (implies (desiniter-unambp desiniter)
             (designor-list-unambp (desiniter->designors desiniter)))
    :expand (desiniter-unambp desiniter))

  (defrule initer-unambp-of-desiniter->initer
    (implies (desiniter-unambp desiniter)
             (initer-unambp (desiniter->initer desiniter)))
    :expand (desiniter-unambp desiniter))

  (defrule const-expr-unambp-of-designor-sub->index
    (implies (and (designor-unambp designor)
                  (designor-case designor :sub))
             (const-expr-unambp (designor-sub->index designor)))
    :expand (designor-unambp designor))

  (defrule dirdeclor-unambp-of-declor->direct
    (implies (declor-unambp declor)
             (dirdeclor-unambp (declor->direct declor)))
    :expand (declor-unambp declor))

  (defrule declor-unambp-of-dirdeclor-paren->unwrap
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :paren))
             (declor-unambp (dirdeclor-paren->inner dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-array->declor
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array))
             (dirdeclor-unambp (dirdeclor-array->declor dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule expr-option-unambp-of-dirdeclor-array->size?
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array))
             (expr-option-unambp (dirdeclor-array->size? dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-array-static1->declor
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array-static1))
             (dirdeclor-unambp (dirdeclor-array-static1->declor dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule expr-unambp-of-dirdeclor-array-static1->sizer
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array-static1))
             (expr-unambp (dirdeclor-array-static1->size dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-array-static2->declor
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array-static2))
             (dirdeclor-unambp (dirdeclor-array-static2->declor dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule expr-unambp-of-dirdeclor-array-static2->size
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array-static2))
             (expr-unambp (dirdeclor-array-static2->size dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-array-star->declor
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array-star))
             (dirdeclor-unambp (dirdeclor-array-star->declor dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-function-params->declor
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :function-params))
             (dirdeclor-unambp (dirdeclor-function-params->declor dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule param-declon-list-unambp-of-dirdeclor-function-params->params
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :function-params))
             (param-declon-list-unambp
              (dirdeclor-function-params->params dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-function-names->declor
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :function-names))
             (dirdeclor-unambp (dirdeclor-function-names->declor dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirabsdeclor-option-unambp-of-absdeclor->direct?
    (implies (absdeclor-unambp absdeclor)
             (dirabsdeclor-option-unambp (absdeclor->direct? absdeclor)))
    :expand (absdeclor-unambp absdeclor))

  (defrule absdeclor-unambp-of-dirabsdeclor-paren->inner
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :paren))
             (absdeclor-unambp (dirabsdeclor-paren->inner dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule dirabsdeclor-option-unambp-of-dirabsdeclor-array->declor?
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array))
             (dirabsdeclor-option-unambp
              (dirabsdeclor-array->declor? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule expr-option-unambp-of-dirabsdeclor-array->size?
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array))
             (expr-option-unambp (dirabsdeclor-array->size? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-array-static1->declor?
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array-static1))
             (dirabsdeclor-option-unambp
              (dirabsdeclor-array-static1->declor? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule expr-unambp-of-dirabsdeclor-array-static1->size
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array-static1))
             (expr-unambp (dirabsdeclor-array-static1->size dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-array-static2->declor?
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array-static2))
             (dirabsdeclor-option-unambp
              (dirabsdeclor-array-static2->declor? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule expr-unambp-of-dirabsdeclor-array-static2->size
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array-static2))
             (expr-unambp (dirabsdeclor-array-static2->size dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-array-star->declor?
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array-star))
             (dirabsdeclor-option-unambp
              (dirabsdeclor-array-star->declor? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-function->declor?
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :function))
             (dirabsdeclor-option-unambp
              (dirabsdeclor-function->declor? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule param-declon-list-unambp-of-dirabsdeclor-function->params
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :function))
             (param-declon-list-unambp
              (dirabsdeclor-function->params dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule decl-spec-list-unambp-of-param-declon->specs
    (implies (param-declon-unambp param)
             (decl-spec-list-unambp (param-declon->specs param)))
    :expand (param-declon-unambp param))

  (defrule paramdeclor-unambp-of-param-declon->decl
    (implies (param-declon-unambp param)
             (paramdeclor-unambp (param-declon->decl param)))
    :expand (param-declon-unambp param))

  (defrule declor-unambp-of-paramdeclor-declor->unwrap
    (implies (and (paramdeclor-unambp paramdeclor)
                  (paramdeclor-case paramdeclor :declor))
             (declor-unambp (paramdeclor-declor->unwrap paramdeclor)))
    :expand (paramdeclor-unambp paramdeclor))

  (defrule absdeclor-unambp-of-paramdeclor-absdeclor->unwrap
    (implies (and (paramdeclor-unambp paramdeclor)
                  (paramdeclor-case paramdeclor :absdeclor))
             (absdeclor-unambp (paramdeclor-absdeclor->unwrap paramdeclor)))
    :expand (paramdeclor-unambp paramdeclor))

  (defrule spec/qual-list-unambp-of-tyname->specqual
    (implies (tyname-unambp tyname)
             (spec/qual-list-unambp (tyname->specqual tyname)))
    :expand (tyname-unambp tyname))

  (defrule absdeclor-option-unambp-of-tyname->decl?
    (implies (tyname-unambp tyname)
             (absdeclor-option-unambp (tyname->decl? tyname)))
    :expand (tyname-unambp tyname))

  (defrule structdecl-list-unambp-of-strunispec->members
    (implies (strunispec-unambp strunispec)
             (structdecl-list-unambp (strunispec->members strunispec)))
    :expand (strunispec-unambp strunispec))

  (defrule spec/qual-list-unambp-of-structdecl-member->specqual
    (implies (and (structdecl-unambp structdecl)
                  (structdecl-case structdecl :member))
             (spec/qual-list-unambp (structdecl-member->specqual structdecl)))
    :expand (structdecl-unambp structdecl))

  (defrule structdeclor-list-unambp-of-structdecl-member->declor
    (implies (and (structdecl-unambp structdecl)
                  (structdecl-case structdecl :member))
             (structdeclor-list-unambp (structdecl-member->declor structdecl)))
    :expand (structdecl-unambp structdecl))

  (defrule statassert-unambp-of-structdecl-statassert->unwrap
    (implies (and (structdecl-unambp structdecl)
                  (structdecl-case structdecl :statassert))
             (statassert-unambp (structdecl-statassert->unwrap structdecl)))
    :expand (structdecl-unambp structdecl))

  (defrule declor-option-unambp-of-structdeclor->declor?
    (implies (structdeclor-unambp structdeclor)
             (declor-option-unambp (structdeclor->declor? structdeclor)))
    :expand (structdeclor-unambp structdeclor))

  (defrule const-expr-option-unambp-of-structdeclor->declor?
    (implies (structdeclor-unambp structdeclor)
             (const-expr-option-unambp (structdeclor->expr? structdeclor)))
    :expand (structdeclor-unambp structdeclor))

  (defrule enumer-list-unambp-of-enumspec->list
    (implies (enumspec-unambp enumspec)
             (enumer-list-unambp (enumspec->list enumspec)))
    :expand (enumspec-unambp enumspec))

  (defrule const-expr-option-unambp-of-enumer->value
    (implies (enumer-unambp enumer)
             (const-expr-option-unambp (enumer->value enumer)))
    :expand (enumer-unambp enumer))

  (defrule const-expr-unambp-of-statassert->test
    (implies (statassert-unambp statassert)
             (const-expr-unambp (statassert->test statassert)))
    :expand (statassert-unambp statassert))

  (defrule declor-unambp-of-initdeclor->declor
    (implies (initdeclor-unambp initdeclor)
             (declor-unambp (initdeclor->declor initdeclor)))
    :expand (initdeclor-unambp initdeclor))

  (defrule initer-option-unambp-of-initdeclor->init?
    (implies (initdeclor-unambp initdeclor)
             (initer-option-unambp (initdeclor->init? initdeclor)))
    :expand (initdeclor-unambp initdeclor))

  (defrule decl-spec-list-unambp-of-decl-decl->specs
    (implies (and (decl-unambp decl)
                  (decl-case decl :decl))
             (decl-spec-list-unambp (decl-decl->specs decl)))
    :expand (decl-unambp decl))

  (defrule initdeclor-list-unambp-of-decl-decl->init
    (implies (and (decl-unambp decl)
                  (decl-case decl :decl))
             (initdeclor-list-unambp (decl-decl->init decl)))
    :expand (decl-unambp decl))

  (defrule statassert-unambp-of-decl-statassert->unwrap
    (implies (and (decl-unambp decl)
                  (decl-case decl :statassert))
             (statassert-unambp (decl-statassert->unwrap decl)))
    :expand (decl-unambp decl))

  (defrule const-expr-unambp-of-label-casexpr->expr
    (implies (and (label-unambp label)
                  (label-case label :casexpr))
             (const-expr-unambp (label-casexpr->expr label)))
    :expand (label-unambp label))

  (defrule const-expr-option-unambp-of-label-casexpr->range?
    (implies (and (label-unambp label)
                  (label-case label :casexpr))
             (const-expr-option-unambp (label-casexpr->range? label)))
    :expand (label-unambp label))

  (defrule label-unamb-of-stmt-labeled->label
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :labeled))
             (label-unambp (stmt-labeled->label stmt)))
    :expand (stmt-unambp stmt))

  (defrule stmt-unamb-of-stmt-labeled->stmt
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :labeled))
             (stmt-unambp (stmt-labeled->stmt stmt)))
    :expand (stmt-unambp stmt))

  (defrule stmt-unamb-of-stmt-compound->items
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :compound))
             (block-item-list-unambp (stmt-compound->items stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-optionp-unamb-of-stmt-expr->expr?
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :expr))
             (expr-option-unambp (stmt-expr->expr? stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-unamb-of-stmt-if->test
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :if))
             (expr-unambp (stmt-if->test stmt)))
    :expand (stmt-unambp stmt))

  (defrule stmt-unamb-of-stmt-if->then
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :if))
             (stmt-unambp (stmt-if->then stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-unamb-of-stmt-ifelse->test
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :ifelse))
             (expr-unambp (stmt-ifelse->test stmt)))
    :expand (stmt-unambp stmt))

  (defrule stmt-unamb-of-stmt-ifelse->then
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :ifelse))
             (stmt-unambp (stmt-ifelse->then stmt)))
    :expand (stmt-unambp stmt))

  (defrule stmt-unamb-of-stmt-ifelse->else
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :ifelse))
             (stmt-unambp (stmt-ifelse->else stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-unamb-of-stmt-switch->target
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :switch))
             (expr-unambp (stmt-switch->target stmt)))
    :expand (stmt-unambp stmt))

  (defrule stmt-unamb-of-stmt-switch->body
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :switch))
             (stmt-unambp (stmt-switch->body stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-unamb-of-stmt-while->test
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :while))
             (expr-unambp (stmt-while->test stmt)))
    :expand (stmt-unambp stmt))

  (defrule stmt-unamb-of-stmt-while->body
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :while))
             (stmt-unambp (stmt-while->body stmt)))
    :expand (stmt-unambp stmt))

  (defrule stmt-unamb-of-stmt-dowhile->body
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :dowhile))
             (stmt-unambp (stmt-dowhile->body stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-unamb-of-stmt-dowhile->test
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :dowhile))
             (expr-unambp (stmt-dowhile->test stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-option-unambp-of-stmt-for-expr->init
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :for-expr))
             (expr-option-unambp (stmt-for-expr->init stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-option-unambp-of-stmt-for-expr->test
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :for-expr))
             (expr-option-unambp (stmt-for-expr->test stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-option-unambp-of-stmt-for-expr->next
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :for-expr))
             (expr-option-unambp (stmt-for-expr->next stmt)))
    :expand (stmt-unambp stmt))

  (defrule stmt-unamb-of-stmt-for-expr->body
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :for-expr))
             (stmt-unambp (stmt-for-expr->body stmt)))
    :expand (stmt-unambp stmt))

  (defrule decl-unambp-of-stmt-for-decl->init
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :for-decl))
             (decl-unambp (stmt-for-decl->init stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-option-unambp-of-stmt-for-decl->test
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :for-decl))
             (expr-option-unambp (stmt-for-decl->test stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-option-unambp-of-stmt-for-decl->next
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :for-decl))
             (expr-option-unambp (stmt-for-decl->next stmt)))
    :expand (stmt-unambp stmt))

  (defrule stmt-unamb-of-stmt-for-decl->body
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :for-decl))
             (stmt-unambp (stmt-for-decl->body stmt)))
    :expand (stmt-unambp stmt))

  (defrule expr-optionp-unamb-of-stmt-return->expr?
    (implies (and (stmt-unambp stmt)
                  (stmt-case stmt :return))
             (expr-option-unambp (stmt-return->expr? stmt)))
    :expand (stmt-unambp stmt))

  (defrule decl-unamb-of-block-item-decl->unwrap
    (implies (and (block-item-unambp item)
                  (block-item-case item :decl))
             (decl-unambp (block-item-decl->unwrap item)))
    :expand (block-item-unambp item))

  (defrule stmt-unamb-of-block-item-stmt->unwrap
    (implies (and (block-item-unambp item)
                  (block-item-case item :stmt))
             (stmt-unambp (block-item-stmt->unwrap item)))
    :expand (block-item-unambp item))

  (defrule expr-unambp-of-expr/tyname-expr->unwrap
    (implies (and (expr/tyname-unambp expr/tyname)
                  (expr/tyname-case expr/tyname :expr))
             (expr-unambp (expr/tyname-expr->unwrap expr/tyname)))
    :enable expr/tyname-unambp)

  (defrule tyname-unambp-of-expr/tyname-tyname->unwrap
    (implies (and (expr/tyname-unambp expr/tyname)
                  (expr/tyname-case expr/tyname :tyname))
             (tyname-unambp (expr/tyname-tyname->unwrap expr/tyname)))
    :enable expr/tyname-unambp)

  (defrule declor-unambp-of-declor/absdeclor-declor->unwrap
    (implies (and (declor/absdeclor-unambp declor/absdeclor)
                  (declor/absdeclor-case declor/absdeclor :declor))
             (declor-unambp
              (declor/absdeclor-declor->unwrap declor/absdeclor)))
    :enable declor/absdeclor-unambp)

  (defrule absdeclor-unambp-of-declor/absdeclor-absdeclor->unwrap
    (implies (and (declor/absdeclor-unambp declor/absdeclor)
                  (declor/absdeclor-case declor/absdeclor :absdeclor))
             (absdeclor-unambp
              (declor/absdeclor-absdeclor->unwrap declor/absdeclor)))
    :enable declor/absdeclor-unambp)

  (defrule decl-unambp-of-decl/stmt-decl->unwrap
    (implies (and (decl/stmt-unambp decl/stmt)
                  (decl/stmt-case decl/stmt :decl))
             (decl-unambp (decl/stmt-decl->unwrap decl/stmt)))
    :enable decl/stmt-unambp)

  (defrule stmt-unambp-of-decl/stmt-stmt->unwrap
    (implies (and (decl/stmt-unambp decl/stmt)
                  (decl/stmt-case decl/stmt :stmt))
             (expr-unambp (decl/stmt-stmt->unwrap decl/stmt)))
    :enable decl/stmt-unambp)

  (defrule decl-spec-list-unambp-of-fundef->spec
    (implies (fundef-unambp fundef)
             (decl-spec-list-unambp (fundef->spec fundef)))
    :enable fundef-unambp)

  (defrule declor-unambp-of-fundef->declor
    (implies (fundef-unambp fundef)
             (declor-unambp (fundef->declor fundef)))
    :enable fundef-unambp)

  (defrule decl-list-unambp-of-fundef->decls
    (implies (fundef-unambp fundef)
             (decl-list-unambp (fundef->decls fundef)))
    :enable fundef-unambp)

  (defrule stmt-unambp-of-fundef->body
    (implies (fundef-unambp fundef)
             (stmt-unambp (fundef->body fundef)))
    :enable fundef-unambp)

  (defrule fundef-unambp-of-extdecl-fundef->unwrap
    (implies (and (extdecl-unambp edecl)
                  (extdecl-case edecl :fundef))
             (fundef-unambp (extdecl-fundef->unwrap edecl)))
    :enable extdecl-unambp)

  (defrule decl-unambp-of-extdecl-decl->unwrap
    (implies (and (extdecl-unambp edecl)
                  (extdecl-case edecl :decl))
             (decl-unambp (extdecl-decl->unwrap edecl)))
    :enable extdecl-unambp)

  (defrule extdecl-list-unambp-of-transunit->decls
    (implies (transunit-unambp tunit)
             (extdecl-list-unambp (transunit->decls tunit)))
    :enable transunit-unambp)

  (defrule transunit-ensemble-unambp-loop-of-transunit-ensemble->unwrap
    (implies (transunit-ensemble-unambp tunits)
             (filepath-transunit-map-unambp
              (transunit-ensemble->unwrap tunits)))
    :enable transunit-ensemble-unambp)

  ;; Theorems about excluded sum type kinds:

  (defrule not-sizeof-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :sizeof-ambig)))
    :rule-classes :forward-chaining
    :enable expr-unambp)

  (defrule not-cast/call-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :cast/call-ambig)))
    :rule-classes :forward-chaining
    :enable expr-unambp)

  (defrule not-cast/mul-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :cast/mul-ambig)))
    :rule-classes :forward-chaining
    :enable expr-unambp)

  (defrule not-cast/add-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :cast/add-ambig)))
    :rule-classes :forward-chaining
    :enable expr-unambp)

  (defrule not-cast/sub-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :cast/sub-ambig)))
    :rule-classes :forward-chaining
    :enable expr-unambp)

  (defrule not-cast/and-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :cast/and-ambig)))
    :rule-classes :forward-chaining
    :enable expr-unambp)

  (defrule expr-unambp-of-type-spec-typeof-expr->expr
    (implies (and (type-spec-unambp tyspec)
                  (equal (type-spec-kind tyspec) :typeof-expr))
             (expr-unambp (type-spec-typeof-expr->expr tyspec)))
    :rule-classes :forward-chaining
    :enable type-spec-unambp)

  (defrule tyname-unambp-of-type-spec-typeof-type->type
    (implies (and (type-spec-unambp tyspec)
                  (equal (type-spec-kind tyspec) :typeof-type))
             (tyname-unambp (type-spec-typeof-type->type tyspec)))
    :rule-classes :forward-chaining
    :enable type-spec-unambp)

  (defrule not-typeof-ambig-when-type-spec-unambp
    (implies (type-spec-unambp tyspec)
             (not (equal (type-spec-kind tyspec) :typeof-ambig)))
    :rule-classes :forward-chaining
    :enable type-spec-unambp)

  (defrule not-alignas-ambig-when-align-spec-unambp
    (implies (align-spec-unambp alignspec)
             (not (equal (align-spec-kind alignspec) :alignas-ambig)))
    :rule-classes :forward-chaining
    :enable align-spec-unambp)

  (defrule not-ambig-when-paramdeclor-unambp
    (implies (paramdeclor-unambp paramdeclor)
             (not (equal (paramdeclor-kind paramdeclor) :ambig)))
    :rule-classes :forward-chaining
    :expand (paramdeclor-unambp paramdeclor))

  (defrule not-for-ambig-when-stmt-unambp
    (implies (stmt-unambp stmt)
             (not (equal (stmt-kind stmt) :for-ambig)))
    :rule-classes :forward-chaining
    :enable stmt-unambp)

  (defrule not-ambig-when-block-item-unambp
    (implies (block-item-unambp item)
             (not (equal (block-item-kind item) :ambig)))
    :rule-classes :forward-chaining
    :enable block-item-unambp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-spec-list-unambp-of-sublists
  :short "Theorems saying that the sublist of type specifiers
          extracted via some abstract syntax operations
          is unambiguous if the initial list is unambiguous."

  (defrule type-spec-list-unambp-of-check-spec/qual-list-all-typespec
    (b* (((mv okp tyspecs) (check-spec/qual-list-all-typespec specquals)))
      (implies (and (spec/qual-list-unambp specquals)
                    okp)
               (type-spec-list-unambp tyspecs)))
    :induct t
    :enable check-spec/qual-list-all-typespec)

  (defrule type-spec-list-unambp-of-check-decl-spec-list-all-typespec
    (b* (((mv okp tyspecs) (check-decl-spec-list-all-typespec specquals)))
      (implies (and (decl-spec-list-unambp specquals)
                    okp)
               (type-spec-list-unambp tyspecs)))
    :induct t
    :enable check-decl-spec-list-all-typespec)

  (defrule type-spec-list-unambp-of-check-decl-spec-list-all-typespec/stoclass
    (b* (((mv okp tyspecs &)
          (check-decl-spec-list-all-typespec/stoclass declspecs)))
      (implies (and (decl-spec-list-unambp declspecs)
                    okp)
               (type-spec-list-unambp tyspecs)))
    :induct t
    :enable check-decl-spec-list-all-typespec/stoclass))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection expr-unambp-of-operation-on-expr-unambp
  :short "Preservation of unambiguity by certain operations on expressions."

  (defrule expr-unambp-of-apply-pre-inc/dec-ops
    (implies (expr-unambp expr)
             (expr-unambp (apply-pre-inc/dec-ops inc/dec expr)))
    :induct t
    :enable apply-pre-inc/dec-ops)

  (defrule expr-unambp-of-apply-post-inc/dec-ops
    (implies (expr-unambp expr)
             (expr-unambp (apply-post-inc/dec-ops expr inc/dec)))
    :induct t
    :enable apply-post-inc/dec-ops)

  (defrule expr-list-unambp-of-expr-to-asg-expr-list
    (implies (expr-unambp expr)
             (expr-list-unambp (expr-to-asg-expr-list expr)))
    :induct t
    :enable expr-to-asg-expr-list)

  (defrule expr-unambp-of-check-expr-mul
    (b* (((mv yes/no arg1 arg2) (check-expr-mul expr)))
      (implies (and (expr-unambp expr)
                    yes/no)
               (and (expr-unambp arg1)
                    (expr-unambp arg2))))
    :enable check-expr-mul)

  (defrule expr-unambp-of-check-expr-binary
    (b* (((mv yes/no & arg1 arg2) (check-expr-binary expr)))
      (implies (and (expr-unambp expr)
                    yes/no)
               (and (expr-unambp arg1)
                    (expr-unambp arg2))))
    :enable check-expr-binary))
