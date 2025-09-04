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
(include-book "code-ensembles")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

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

(fty::deffold-reduce unambp
  :short "Definition of the unambiguity predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee fty::deffold-reduce) to define these predicates concisely.")
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
  :types (exprs/decls/stmts
          type-spec-list
          expr/tyname
          declor/absdeclor
          decl/stmt
          fundef
          fundef-option
          extdecl
          extdecl-list
          transunit
          filepath-transunit-map
          transunit-ensemble)
  :result booleanp
  :default t
  :combine and
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unambiguity-predicate-theorems
  :short "Theorems about the unambiguity predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are mentioned in @(see unambiguity):
     they support guard and return proofs.
     We plan to extend @(tsee fty::deffold-reduce)
     to generate at least some of these."))

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

  (defrule member-designor-unambp-when-ident
    (implies (member-designor-case memdes :ident)
             (member-designor-unambp memdes))
    :enable member-designor-unambp)

  (defrule type-spec-unambp-when-not-atomic/struct/union/enum/typeof
    (implies (not (member-eq (type-spec-kind tyspec)
                             '(:atomic :struct :union :enum
                               :typeof-expr :typeof-type :typeof-ambig)))
             (type-spec-unambp tyspec))
    :enable type-spec-unambp)

  (defrule spec/qual-unambp-when-typequal
    (implies (eq (spec/qual-kind spec/qual) :typequal)
             (spec/qual-unambp spec/qual))
    :enable spec/qual-unambp)

  (defrule spec/qual-unambp-when-attrib
    (implies (eq (spec/qual-kind spec/qual) :attrib)
             (spec/qual-unambp spec/qual))
    :expand (spec/qual-unambp spec/qual))

  (defrule decl-spec-unambp-when-not-typespec/align
    (implies (and (not (decl-spec-case declspec :typespec))
                  (not (decl-spec-case declspec :align)))
             (decl-spec-unambp declspec))
    :expand (decl-spec-unambp declspec))

  (defrule designor-unambp-when-dot
    (implies (designor-case designor :dot)
             (designor-unambp designor))
    :enable designor-unambp)

  (defrule dirdeclor-unambp-when-ident
    (implies (dirdeclor-case dirdeclor :ident)
             (dirdeclor-unambp dirdeclor))
    :enable dirdeclor-unambp)

  (defrule not-dirabsdeclor-unambp-when-dummy-base
    (implies (dirabsdeclor-case dirabsdeclor :dummy-base)
             (not (dirabsdeclor-unambp dirabsdeclor)))
    :enable dirabsdeclor-unambp)

  (defrule structdecl-unambp-when-empty
    (implies (structdecl-case sdecl :empty)
             (structdecl-unambp sdecl))
    :enable structdecl-unambp)

  (defrule label-unambp-when-not-casexpr
    (implies (not (label-case label :casexpr))
             (label-unambp label))
    :enable label-unambp)

  (defrule stmt-unambp-when-goto
    (implies (stmt-case stmt :goto)
             (stmt-unambp stmt))
    :enable stmt-unambp)

  (defrule stmt-unambp-of-when-asm
    (implies (stmt-case stmt :asm)
             (stmt-unambp stmt))
    :expand (stmt-unambp stmt))

  (defrule extdecl-unambp-when-not-fundef/decl
    (implies (not (member-eq (extdecl-kind edecl) '(:fundef :decl)))
             (extdecl-unambp edecl))
    :enable extdecl-unambp)

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

  (defrule struni-spec-unambp-of-type-spec-struct->spec
    (implies (and (type-spec-unambp tyspec)
                  (type-spec-case tyspec :struct))
             (struni-spec-unambp (type-spec-struct->spec tyspec)))
    :expand (type-spec-unambp tyspec))

  (defrule struni-spec-unambp-of-type-spec-union->spec
    (implies (and (type-spec-unambp tyspec)
                  (type-spec-case tyspec :union))
             (struni-spec-unambp (type-spec-union->spec tyspec)))
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

  (defrule const-expr-unambp-of-designor-sub->range?
    (implies (and (designor-unambp designor)
                  (designor-case designor :sub))
             (const-expr-option-unambp (designor-sub->range? designor)))
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

  (defrule param-declor-unambp-of-param-declon->declor
    (implies (param-declon-unambp param)
             (param-declor-unambp (param-declon->declor param)))
    :expand (param-declon-unambp param))

  (defrule declor-unambp-of-param-declor-nonabstract->declor
    (implies (and (param-declor-unambp param-declor)
                  (param-declor-case param-declor :nonabstract))
             (declor-unambp (param-declor-nonabstract->declor param-declor)))
    :expand (param-declor-unambp param-declor))

  (defrule absdeclor-unambp-of-param-declor-abstract->declor
    (implies (and (param-declor-unambp param-declor)
                  (param-declor-case param-declor :abstract))
             (absdeclor-unambp (param-declor-abstract->declor param-declor)))
    :expand (param-declor-unambp param-declor))

  (defrule spec/qual-list-unambp-of-tyname->specquals
    (implies (tyname-unambp tyname)
             (spec/qual-list-unambp (tyname->specquals tyname)))
    :expand (tyname-unambp tyname))

  (defrule absdeclor-option-unambp-of-tyname->declor?
    (implies (tyname-unambp tyname)
             (absdeclor-option-unambp (tyname->declor? tyname)))
    :expand (tyname-unambp tyname))

  (defrule structdecl-list-unambp-of-struni-spec->members
    (implies (struni-spec-unambp struni-spec)
             (structdecl-list-unambp (struni-spec->members struni-spec)))
    :expand (struni-spec-unambp struni-spec))

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

  (defrule decl-unamb-of-block-item-decl->decl
    (implies (and (block-item-unambp item)
                  (block-item-case item :decl))
             (decl-unambp (block-item-decl->decl item)))
    :expand (block-item-unambp item))

  (defrule stmt-unamb-of-block-item-stmt->stmt
    (implies (and (block-item-unambp item)
                  (block-item-case item :stmt))
             (stmt-unambp (block-item-stmt->stmt item)))
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
             (block-item-list-unambp (fundef->body fundef)))
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

  (defrule not-ambig-when-param-declor-unambp
    (implies (param-declor-unambp param-declor)
             (not (equal (param-declor-kind param-declor) :ambig)))
    :rule-classes :forward-chaining
    :expand (param-declor-unambp param-declor))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
    :enable (check-spec/qual-list-all-typespec
             abstract-syntax-unambp-rules))

  (defrule type-spec-list-unambp-of-check-decl-spec-list-all-typespec
    (b* (((mv okp tyspecs) (check-decl-spec-list-all-typespec specquals)))
      (implies (and (decl-spec-list-unambp specquals)
                    okp)
               (type-spec-list-unambp tyspecs)))
    :induct t
    :enable (check-decl-spec-list-all-typespec
             abstract-syntax-unambp-rules))

  (defrule type-spec-list-unambp-of-check-decl-spec-list-all-typespec/stoclass
    (b* (((mv okp tyspecs &)
          (check-decl-spec-list-all-typespec/stoclass declspecs)))
      (implies (and (decl-spec-list-unambp declspecs)
                    okp)
               (type-spec-list-unambp tyspecs)))
    :induct t
    :enable (check-decl-spec-list-all-typespec/stoclass
             abstract-syntax-unambp-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection expr-unambp-of-operation-on-expr-unambp
  :short "Preservation of unambiguity by certain operations on expressions."

  (defrule expr-unambp-of-apply-pre-inc/dec-ops
    (implies (expr-unambp expr)
             (expr-unambp (apply-pre-inc/dec-ops inc/dec expr)))
    :induct t
    :enable (apply-pre-inc/dec-ops
             expr-unambp-of-expr-unary))

  (defrule expr-unambp-of-apply-post-inc/dec-ops
    (implies (expr-unambp expr)
             (expr-unambp (apply-post-inc/dec-ops expr inc/dec)))
    :induct t
    :enable (apply-post-inc/dec-ops
             expr-unambp-of-expr-unary))

  (defrule expr-list-unambp-of-expr-to-asg-expr-list
    (implies (expr-unambp expr)
             (expr-list-unambp (expr-to-asg-expr-list expr)))
    :induct t
    :enable (expr-to-asg-expr-list
             abstract-syntax-unambp-rules))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-ensemble-unambp ((code code-ensemblep))
  :returns (yes/no booleanp)
  :short "Check if a code ensemble is unambiguous."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether the translation unit ensemble is unambiguous.
     The implementation environment is ignored for this,
     but it is convenient to lift the unambiguity predicate
     from translation unit ensembles to code ensembles."))
  (transunit-ensemble-unambp (code-ensemble->transunits code))
  :hooks (:fix)

  ///

  (defruled code-ensemble-unambp-of-code-ensemble
    (equal (code-ensemble-unambp (code-ensemble tunits ienv))
           (transunit-ensemble-unambp tunits)))

  (defruled transunit-ensemble-unambp-of-code-ensemble->transunits
    (implies (code-ensemble-unambp code)
             (transunit-ensemble-unambp (code-ensemble->transunits code)))))
