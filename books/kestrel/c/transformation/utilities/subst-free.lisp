; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "../../syntax/abstract-syntax-operations")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (tau-system))))
(set-induction-depth-limit 0)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ subst-free
  :parents (utilities)
  :short "A utility to substitute expressions in for free variables in a C
          AST."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is a mapping operation over C ASTs, which will substitute ordinary
       free variables according to an identifier-expression "
      (xdoc::seetopic "omap::omaps" "omap")
      "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap ident-expr-map
  :key-type ident
  :val-type c$::expr
  :pred ident-expr-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: it may be more natural to remove bound-vars from subst instead of
;; tracking them
(defines exprs/decls/stmts-subst-free
  (define expr-subst-free ((expr exprp)
                           (subst ident-expr-mapp)
                           (bound-vars ident-setp))
    :returns (result exprp)
    (expr-case
     expr
     ;; Interesting case
     :ident (b* ((lookup (omap::assoc expr.ident subst)))
              (expr-fix (if (and lookup
                                 (not (in expr.ident bound-vars)))
                            (cdr lookup)
                          expr)))
     :const (expr-fix expr)
     :string (expr-fix expr)
     :paren
     (expr-paren (expr-subst-free (c$::expr-paren->inner expr)
                                  subst bound-vars))
     :gensel
     (c$::expr-gensel
       (expr-subst-free (c$::expr-gensel->control expr)
                        subst bound-vars)
       (genassoc-list-subst-free (c$::expr-gensel->assocs expr)
                                 subst bound-vars))
     :arrsub (c$::expr-arrsub
               (expr-subst-free (c$::expr-arrsub->arg1 expr)
                                subst bound-vars)
               (expr-subst-free (c$::expr-arrsub->arg2 expr)
                                subst bound-vars))
     :funcall
     (c$::expr-funcall
       (expr-subst-free (c$::expr-funcall->fun expr)
                        subst bound-vars)
       (expr-list-subst-free (c$::expr-funcall->args expr)
                             subst bound-vars))
     :member (c$::expr-member
               (expr-subst-free (c$::expr-member->arg expr)
                                subst bound-vars)
               (c$::expr-member->name expr))
     :memberp (c$::expr-memberp
                (expr-subst-free (c$::expr-memberp->arg expr)
                                 subst bound-vars)
                (c$::expr-memberp->name expr))
     :complit
     (c$::expr-complit
       (tyname-subst-free (c$::expr-complit->type expr)
                          subst bound-vars)
       (desiniter-list-subst-free (c$::expr-complit->elems expr)
                                  subst bound-vars)
       (c$::expr-complit->final-comma expr))
     :unary
     (c$::expr-unary (c$::expr-unary->op expr)
                     (expr-subst-free (c$::expr-unary->arg expr)
                                      subst bound-vars)
                     (c$::expr-unary->info expr))
     :sizeof
     (expr-sizeof
       (tyname-subst-free (c$::expr-sizeof->type expr)
                          subst bound-vars))
     :sizeof-ambig
     (c$::expr-sizeof-ambig (amb-expr/tyname-subst-free
                              (c$::expr-sizeof-ambig->expr/tyname expr)
                              subst bound-vars))
     :alignof
     (expr-alignof
       (tyname-subst-free (c$::expr-alignof->type expr)
                          subst bound-vars)
       (c$::expr-alignof->uscores expr))
     :cast (c$::expr-cast
             (tyname-subst-free (c$::expr-cast->type expr)
                                subst bound-vars)
             (expr-subst-free (c$::expr-cast->arg expr)
                              subst bound-vars))
     :binary (c$::expr-binary
               (c$::expr-binary->op expr)
               (expr-subst-free (c$::expr-binary->arg1 expr)
                                subst bound-vars)
               (expr-subst-free (c$::expr-binary->arg2 expr)
                                subst bound-vars)
               (c$::expr-binary->info expr))
     :cond
     (c$::expr-cond
       (expr-subst-free (c$::expr-cond->test expr)
                        subst bound-vars)
       (expr-option-subst-free (c$::expr-cond->then expr)
                               subst bound-vars)
       (expr-subst-free (c$::expr-cond->else expr)
                        subst bound-vars))
     :comma (c$::expr-comma
              (expr-subst-free (c$::expr-comma->first expr)
                               subst bound-vars)
              (expr-subst-free (c$::expr-comma->next expr)
                               subst bound-vars))
     :cast/call-ambig
     (c$::expr-cast/call-ambig
       (amb-expr/tyname-subst-free
         (c$::expr-cast/call-ambig->type/fun expr)
         subst bound-vars)
       (c$::expr-cast/call-ambig->inc/dec expr)
       (expr-subst-free (c$::expr-cast/call-ambig->arg/rest expr)
                        subst bound-vars))
     :cast/mul-ambig
     (c$::expr-cast/mul-ambig
       (amb-expr/tyname-subst-free
         (c$::expr-cast/mul-ambig->type/arg1 expr)
         subst bound-vars)
       (c$::expr-cast/mul-ambig->inc/dec expr)
       (expr-subst-free (c$::expr-cast/mul-ambig->arg/arg2 expr)
                        subst bound-vars))
     :cast/add-ambig
     (c$::expr-cast/add-ambig
       (amb-expr/tyname-subst-free
         (c$::expr-cast/add-ambig->type/arg1 expr)
         subst bound-vars)
       (c$::expr-cast/add-ambig->inc/dec expr)
       (expr-subst-free (c$::expr-cast/add-ambig->arg/arg2 expr)
                        subst bound-vars))
     :cast/sub-ambig
     (c$::expr-cast/sub-ambig
       (amb-expr/tyname-subst-free
         (c$::expr-cast/sub-ambig->type/arg1 expr)
         subst bound-vars)
       (c$::expr-cast/sub-ambig->inc/dec expr)
       (expr-subst-free (c$::expr-cast/sub-ambig->arg/arg2 expr)
                        subst bound-vars))
     :cast/and-ambig
     (c$::expr-cast/and-ambig
       (amb-expr/tyname-subst-free
         (c$::expr-cast/and-ambig->type/arg1 expr)
         subst bound-vars)
       (c$::expr-cast/and-ambig->inc/dec expr)
       (expr-subst-free (c$::expr-cast/and-ambig->arg/arg2 expr)
                        subst bound-vars))
     ;; Interesting case
     :stmt
     (b* (((mv items -)
           (block-item-list-subst-free (c$::expr-stmt->items expr)
                                       subst bound-vars)))
       (expr-stmt items))
     :tycompat
     (c$::expr-tycompat
       (tyname-subst-free (c$::expr-tycompat->type1 expr)
                          subst bound-vars)
       (tyname-subst-free (c$::expr-tycompat->type2 expr)
                          subst bound-vars))
     :offsetof
     (c$::expr-offsetof
       (tyname-subst-free (c$::expr-offsetof->type expr)
                          subst bound-vars)
       (member-designor-subst-free
         (c$::expr-offsetof->member expr)
         subst bound-vars))
     :va-arg
     (c$::expr-va-arg
       (expr-subst-free (c$::expr-va-arg->list expr)
                        subst bound-vars)
       (tyname-subst-free (c$::expr-va-arg->type expr)
                          subst bound-vars))
     :extension
     (expr-extension
       (expr-subst-free (c$::expr-extension->expr expr)
                        subst bound-vars)))
    :measure (expr-count expr))

  (define expr-list-subst-free ((expr-list expr-listp)
                                (subst ident-expr-mapp)
                                (bound-vars ident-setp))
    :returns (result expr-listp)
    (if (endp expr-list)
        nil
      (cons (expr-subst-free (car expr-list)
                             subst bound-vars)
            (expr-list-subst-free (cdr expr-list)
                                  subst bound-vars)))
    :measure (expr-list-count expr-list))

  (define expr-option-subst-free ((expr-option expr-optionp)
                                  (subst ident-expr-mapp)
                                  (bound-vars ident-setp))
    :returns (result expr-optionp)
    (expr-option-case
     expr-option
     :some
     (expr-fix
       (expr-subst-free (c$::expr-option-some->val expr-option)
                        subst bound-vars))
     :none nil)
    :measure (expr-option-count expr-option))

  (define const-expr-subst-free ((const-expr const-exprp)
                                 (subst ident-expr-mapp)
                                 (bound-vars ident-setp))
    :returns (result const-exprp)
    (const-expr (expr-subst-free (const-expr->expr const-expr)
                                 subst bound-vars))
    :measure (const-expr-count const-expr))

  (define const-expr-option-subst-free
    ((const-expr-option const-expr-optionp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result const-expr-optionp)
    (const-expr-option-case
     const-expr-option
     :some (c$::const-expr-fix
             (const-expr-subst-free
               (c$::const-expr-option-some->val const-expr-option)
               subst bound-vars))
     :none nil)
    :measure (const-expr-option-count const-expr-option))

  (define genassoc-subst-free ((genassoc genassocp)
                               (subst ident-expr-mapp)
                               (bound-vars ident-setp))
    :returns (result genassocp)
    (genassoc-case
     genassoc
     :type
     (c$::genassoc-type
       (tyname-subst-free (c$::genassoc-type->type genassoc)
                          subst bound-vars)
       (expr-subst-free (c$::genassoc-type->expr genassoc)
                        subst bound-vars))
     :default
     (genassoc-default
       (expr-subst-free (c$::genassoc-default->expr genassoc)
                        subst bound-vars)))
    :measure (genassoc-count genassoc))

  (define genassoc-list-subst-free
    ((c$::genassoc-list genassoc-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result genassoc-listp)
    (if (endp c$::genassoc-list)
        nil
      (cons (genassoc-subst-free (car c$::genassoc-list)
                                 subst bound-vars)
            (genassoc-list-subst-free (cdr c$::genassoc-list)
                                      subst bound-vars)))
    :measure (genassoc-list-count c$::genassoc-list))

  (define member-designor-subst-free
    ((member-designor member-designorp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result member-designorp)
    (member-designor-case
     member-designor
     :ident (member-designor-fix member-designor)
     :dot (c$::member-designor-dot
            (member-designor-subst-free
              (c$::member-designor-dot->member member-designor)
              subst bound-vars)
            (c$::member-designor-dot->name member-designor))
     :sub (c$::member-designor-sub
            (member-designor-subst-free
              (c$::member-designor-sub->member member-designor)
              subst bound-vars)
            (expr-subst-free
              (c$::member-designor-sub->index member-designor)
              subst bound-vars)))
    :measure (member-designor-count member-designor))

  (define type-spec-subst-free ((type-spec type-specp)
                                (subst ident-expr-mapp)
                                (bound-vars ident-setp))
    :returns (result type-specp)
    (type-spec-case
     type-spec
     :void (type-spec-fix type-spec)
     :char (type-spec-fix type-spec)
     :short (type-spec-fix type-spec)
     :int (type-spec-fix type-spec)
     :long (type-spec-fix type-spec)
     :float (type-spec-fix type-spec)
     :double (type-spec-fix type-spec)
     :signed (type-spec-fix type-spec)
     :unsigned (type-spec-fix type-spec)
     :bool (type-spec-fix type-spec)
     :complex (type-spec-fix type-spec)
     :atomic
     (type-spec-atomic
       (tyname-subst-free (c$::type-spec-atomic->type type-spec)
                          subst bound-vars))
     :struct (type-spec-struct (struni-spec-subst-free
                                 (c$::type-spec-struct->spec type-spec)
                                 subst bound-vars))
     :union (type-spec-union (struni-spec-subst-free
                               (c$::type-spec-union->spec type-spec)
                               subst bound-vars))
     :enum
     (type-spec-enum
       (enumspec-subst-free (c$::type-spec-enum->spec type-spec)
                            subst bound-vars))
     :typedef (type-spec-fix type-spec)
     :int128 (type-spec-fix type-spec)
     :float32 (type-spec-fix type-spec)
     :float32x (type-spec-fix type-spec)
     :float64 (type-spec-fix type-spec)
     :float64x (type-spec-fix type-spec)
     :float128 (type-spec-fix type-spec)
     :float128x (type-spec-fix type-spec)
     :builtin-va-list (type-spec-fix type-spec)
     :struct-empty (type-spec-fix type-spec)
     :typeof-expr (c$::type-spec-typeof-expr
                    (expr-subst-free
                      (c$::type-spec-typeof-expr->expr type-spec)
                      subst bound-vars)
                    (c$::type-spec-typeof-expr->uscores type-spec))
     :typeof-type (c$::type-spec-typeof-type
                    (tyname-subst-free
                      (c$::type-spec-typeof-type->type type-spec)
                      subst bound-vars)
                    (c$::type-spec-typeof-type->uscores type-spec))
     :typeof-ambig
     (c$::type-spec-typeof-ambig
       (amb-expr/tyname-subst-free
         (c$::type-spec-typeof-ambig->expr/type type-spec)
         subst bound-vars)
       (c$::type-spec-typeof-ambig->uscores type-spec))
     :auto-type (type-spec-fix type-spec))
    :measure (type-spec-count type-spec))

  (define spec/qual-subst-free ((spec/qual spec/qual-p)
                                (subst ident-expr-mapp)
                                (bound-vars ident-setp))
    :returns (result spec/qual-p)
    (spec/qual-case
     spec/qual
     :typespec
     (spec/qual-typespec (type-spec-subst-free
                           (c$::spec/qual-typespec->spec spec/qual)
                           subst bound-vars))
     :typequal (spec/qual-fix spec/qual)
     :align (spec/qual-align (align-spec-subst-free
                               (c$::spec/qual-align->spec spec/qual)
                               subst bound-vars))
     :attrib (spec/qual-attrib (attrib-spec-subst-free
                                 (c$::spec/qual-attrib->spec spec/qual)
                                 subst bound-vars)))
    :measure (spec/qual-count spec/qual))

  (define spec/qual-list-subst-free
    ((spec/qual-list spec/qual-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result spec/qual-listp)
    (if (endp spec/qual-list)
        nil
      (cons (spec/qual-subst-free (car spec/qual-list)
                                  subst bound-vars)
            (spec/qual-list-subst-free (cdr spec/qual-list)
                                       subst bound-vars)))
    :measure (spec/qual-list-count spec/qual-list))

  (define align-spec-subst-free ((align-spec align-specp)
                                 (subst ident-expr-mapp)
                                 (bound-vars ident-setp))
    :returns (result align-specp)
    (align-spec-case
     align-spec
     :alignas-type
     (align-spec-alignas-type
       (tyname-subst-free
         (c$::align-spec-alignas-type->type align-spec)
         subst bound-vars))
     :alignas-expr
     (align-spec-alignas-expr
       (const-expr-subst-free
         (c$::align-spec-alignas-expr->expr align-spec)
         subst bound-vars))
     :alignas-ambig
     (c$::align-spec-alignas-ambig
       (amb-expr/tyname-subst-free
         (c$::align-spec-alignas-ambig->expr/type align-spec)
         subst bound-vars)))
    :measure (align-spec-count align-spec))

  (define decl-spec-subst-free ((decl-spec decl-specp)
                                (subst ident-expr-mapp)
                                (bound-vars ident-setp))
    :returns (result decl-specp)
    (decl-spec-case
     decl-spec
     :stoclass (decl-spec-fix decl-spec)
     :typespec
     (decl-spec-typespec (type-spec-subst-free
                           (c$::decl-spec-typespec->spec decl-spec)
                           subst bound-vars))
     :typequal (decl-spec-fix decl-spec)
     :function (decl-spec-fix decl-spec)
     :align (decl-spec-align (align-spec-subst-free
                               (c$::decl-spec-align->spec decl-spec)
                               subst bound-vars))
     :attrib (decl-spec-attrib (attrib-spec-subst-free
                                 (c$::decl-spec-attrib->spec decl-spec)
                                 subst bound-vars))
     :stdcall (decl-spec-fix decl-spec)
     :declspec (decl-spec-fix decl-spec))
    :measure (decl-spec-count decl-spec))

  (define decl-spec-list-subst-free
    ((decl-spec-list decl-spec-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result decl-spec-listp)
    (if (endp decl-spec-list)
        nil
      (cons (decl-spec-subst-free (car decl-spec-list)
                                  subst bound-vars)
            (decl-spec-list-subst-free (cdr decl-spec-list)
                                       subst bound-vars)))
    :measure (decl-spec-list-count decl-spec-list))

  (define typequal/attribspec-subst-free
    ((typequal/attribspec c$::typequal/attribspec-p)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result c$::typequal/attribspec-p)
    (c$::typequal/attribspec-case
     typequal/attribspec
     :type (c$::typequal/attribspec-fix typequal/attribspec)
     :attrib
     (c$::typequal/attribspec-attrib
       (attrib-spec-subst-free
         (c$::typequal/attribspec-attrib->unwrap typequal/attribspec)
         subst bound-vars)))
    :measure (c$::typequal/attribspec-count typequal/attribspec))

  (define typequal/attribspec-list-subst-free
    ((typequal/attribspec-list c$::typequal/attribspec-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result c$::typequal/attribspec-listp)
    (if (endp typequal/attribspec-list)
        nil
      (cons (typequal/attribspec-subst-free
              (car typequal/attribspec-list)
              subst bound-vars)
            (typequal/attribspec-list-subst-free
              (cdr typequal/attribspec-list)
              subst bound-vars)))
    :measure (c$::typequal/attribspec-list-count typequal/attribspec-list))

  (define typequal/attribspec-list-list-subst-free
    ((typequal/attribspec-list-list typequal/attribspec-list-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result typequal/attribspec-list-listp)
    (if (endp typequal/attribspec-list-list)
        nil
      (cons (typequal/attribspec-list-subst-free
              (car typequal/attribspec-list-list)
              subst bound-vars)
            (typequal/attribspec-list-list-subst-free
              (cdr typequal/attribspec-list-list)
              subst bound-vars)))
    :measure (c$::typequal/attribspec-list-list-count
              typequal/attribspec-list-list))

  (define initer-subst-free ((initer initerp)
                             (subst ident-expr-mapp)
                             (bound-vars ident-setp))
    :returns (result initerp)
    (initer-case
     initer
     :single
     (initer-single
       (expr-subst-free (c$::initer-single->expr initer)
                        subst bound-vars))
     :list
     (c$::initer-list
       (desiniter-list-subst-free (c$::initer-list->elems initer)
                                  subst bound-vars)
       (c$::initer-list->final-comma initer)))
    :measure (initer-count initer))

  (define initer-option-subst-free
    ((initer-option initer-optionp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result initer-optionp)
    (initer-option-case
     initer-option
     :some (initer-fix (initer-subst-free
                         (c$::initer-option-some->val initer-option)
                         subst bound-vars))
     :none nil)
    :measure (initer-option-count initer-option))

  (define desiniter-subst-free ((desiniter desiniterp)
                                (subst ident-expr-mapp)
                                (bound-vars ident-setp))
    :returns (result desiniterp)
    (desiniter
     (designor-list-subst-free (c$::desiniter->designors desiniter)
                               subst bound-vars)
     (initer-subst-free (c$::desiniter->initer desiniter)
                        subst bound-vars))
    :measure (desiniter-count desiniter))

  (define desiniter-list-subst-free
    ((desiniter-list desiniter-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result desiniter-listp)
    (if (endp desiniter-list)
        nil
      (cons (desiniter-subst-free (car desiniter-list)
                                  subst bound-vars)
            (desiniter-list-subst-free (cdr desiniter-list)
                                       subst bound-vars)))
    :measure (desiniter-list-count desiniter-list))

  (define designor-subst-free ((designor designorp)
                               (subst ident-expr-mapp)
                               (bound-vars ident-setp))
    :returns (result designorp)
    (designor-case
     designor
     :sub
     (make-designor-sub
      :index (const-expr-subst-free (c$::designor-sub->index designor)
                                    subst bound-vars)
      :range? (const-expr-option-subst-free (c$::designor-sub->range? designor)
                                            subst bound-vars))
     :dot (designor-fix designor))
    :measure (designor-count designor))

  (define designor-list-subst-free
    ((designor-list designor-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result designor-listp)
    (if (endp designor-list)
        nil
      (cons (designor-subst-free (car designor-list)
                                 subst bound-vars)
            (designor-list-subst-free (cdr designor-list)
                                      subst bound-vars)))
    :measure (designor-list-count designor-list))

  (define declor-subst-free ((declor declorp)
                             (subst ident-expr-mapp)
                             (bound-vars ident-setp))
    :returns (mv (result declorp)
                 (bound-vars ident-setp)
                 (param-bound-vars ident-setp))
    (b* (((mv direct bound-vars param-bound-vars)
          (dirdeclor-subst-free (declor->direct declor) subst bound-vars)))
      (mv (declor (typequal/attribspec-list-list-subst-free
                    (c$::declor->pointers declor)
                    subst
                    bound-vars)
            direct)
          bound-vars
          param-bound-vars))
    :measure (declor-count declor))

  (define declor-option-subst-free
    ((declor-option declor-optionp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (mv (result declor-optionp)
                 (bound-vars ident-setp))
    (declor-option-case
     declor-option
     :some (b* (((mv declor bound-vars -)
                 (declor-subst-free (c$::declor-option-some->val declor-option)
                                    subst
                                    bound-vars)))
             (mv (declor-fix declor)
                 (ident-set-fix bound-vars)))
     :none (mv nil nil))
    :measure (declor-option-count declor-option))

  ;; Interesting case
  (define dirdeclor-subst-free ((dirdeclor dirdeclorp)
                                (subst ident-expr-mapp)
                                (bound-vars ident-setp))
    :returns (mv (result dirdeclorp)
                 (bound-vars ident-setp)
                 (param-bound-vars ident-setp))
    (dirdeclor-case
     dirdeclor
     :ident (mv (dirdeclor-fix dirdeclor)
                (insert dirdeclor.ident (ident-set-fix bound-vars))
                nil)
     :paren
     (b* (((mv inner bound-vars -)
           (declor-subst-free (c$::dirdeclor-paren->inner dirdeclor)
                              subst
                              bound-vars)))
       (mv (dirdeclor-paren inner)
           bound-vars
           nil))
     :array
     (b* (((mv declor bound-vars -)
           (dirdeclor-subst-free (c$::dirdeclor-array->declor dirdeclor)
                                 subst bound-vars)))
       (mv (c$::dirdeclor-array
             declor
             (typequal/attribspec-list-subst-free
               (c$::dirdeclor-array->qualspecs dirdeclor)
               subst bound-vars)
             (expr-option-subst-free (c$::dirdeclor-array->size? dirdeclor)
                                     subst bound-vars))
           bound-vars
           nil))
     :array-static1
     (b* (((mv declor bound-vars -)
           (dirdeclor-subst-free
             (c$::dirdeclor-array-static1->declor dirdeclor)
             subst bound-vars)))
       (mv (c$::dirdeclor-array-static1
             declor
             (typequal/attribspec-list-subst-free
               (c$::dirdeclor-array-static1->qualspecs dirdeclor)
               subst bound-vars)
             (expr-subst-free (c$::dirdeclor-array-static1->size dirdeclor)
                              subst bound-vars))
           bound-vars
           nil))
     :array-static2
     (b* (((mv declor bound-vars -)
           (dirdeclor-subst-free
             (c$::dirdeclor-array-static2->declor dirdeclor)
             subst bound-vars)))
       (mv (c$::dirdeclor-array-static2
             declor
             (typequal/attribspec-list-subst-free
               (c$::dirdeclor-array-static2->qualspecs dirdeclor)
               subst bound-vars)
             (expr-subst-free (c$::dirdeclor-array-static2->size dirdeclor)
                              subst bound-vars))
           bound-vars
           nil))
     :array-star
     (b* (((mv declor bound-vars -)
           (dirdeclor-subst-free
             (c$::dirdeclor-array-star->declor dirdeclor)
             subst bound-vars)))
       (mv (c$::dirdeclor-array-star
             declor
             (typequal/attribspec-list-subst-free
               (c$::dirdeclor-array-star->qualspecs dirdeclor)
               subst bound-vars))
           bound-vars
           nil))
     :function-params
     (b* (((mv declor bound-vars -)
           (dirdeclor-subst-free
             (dirdeclor-function-params->declor dirdeclor)
             subst bound-vars))
          ((mv params param-bound-vars)
           (param-declon-list-subst-free
             (dirdeclor-function-params->params dirdeclor)
             subst bound-vars)))
       (mv (c$::dirdeclor-function-params
             declor params
             (c$::dirdeclor-function-params->ellipsis dirdeclor))
           bound-vars
           param-bound-vars))
     :function-names
     (b* (((mv declor bound-vars -)
           (dirdeclor-subst-free
             (c$::dirdeclor-function-names->declor dirdeclor)
             subst bound-vars)))
       (mv (c$::dirdeclor-function-names
             declor
             (dirdeclor-function-names->names dirdeclor))
           bound-vars
           nil)))
    :measure (dirdeclor-count dirdeclor))

  (define absdeclor-subst-free ((absdeclor absdeclorp)
                                (subst ident-expr-mapp)
                                (bound-vars ident-setp))
    :returns (result absdeclorp)
    (absdeclor (typequal/attribspec-list-list-subst-free
                 (c$::absdeclor->pointers absdeclor)
                 subst bound-vars)
               (dirabsdeclor-option-subst-free
                 (c$::absdeclor->direct? absdeclor)
                 subst bound-vars))
    :measure (absdeclor-count absdeclor))

  (define absdeclor-option-subst-free
    ((absdeclor-option absdeclor-optionp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result absdeclor-optionp)
    (absdeclor-option-case
     absdeclor-option
     :some
     (absdeclor-fix (absdeclor-subst-free
                      (c$::absdeclor-option-some->val absdeclor-option)
                      subst bound-vars))
     :none nil)
    :measure (absdeclor-option-count absdeclor-option))

  (define dirabsdeclor-subst-free ((dirabsdeclor dirabsdeclorp)
                                   (subst ident-expr-mapp)
                                   (bound-vars ident-setp))
    :returns (result dirabsdeclorp)
    (dirabsdeclor-case
     dirabsdeclor
     :dummy-base (dirabsdeclor-fix dirabsdeclor)
     :paren
     (dirabsdeclor-paren (absdeclor-subst-free
                           (c$::dirabsdeclor-paren->inner dirabsdeclor)
                           subst bound-vars))
     :array (c$::dirabsdeclor-array
              (dirabsdeclor-option-subst-free
                (c$::dirabsdeclor-array->declor? dirabsdeclor)
                subst bound-vars)
              (typequal/attribspec-list-subst-free
                (c$::dirabsdeclor-array->qualspecs dirabsdeclor)
                subst bound-vars)
              (expr-option-subst-free
                (c$::dirabsdeclor-array->size? dirabsdeclor)
                subst bound-vars))
     :array-static1
     (c$::dirabsdeclor-array-static1
       (dirabsdeclor-option-subst-free
         (c$::dirabsdeclor-array-static1->declor? dirabsdeclor)
         subst bound-vars)
       (typequal/attribspec-list-subst-free
         (c$::dirabsdeclor-array-static1->qualspecs dirabsdeclor)
         subst bound-vars)
       (expr-subst-free
         (c$::dirabsdeclor-array-static1->size dirabsdeclor)
         subst bound-vars))
     :array-static2
     (c$::dirabsdeclor-array-static2
       (dirabsdeclor-option-subst-free
         (c$::dirabsdeclor-array-static2->declor? dirabsdeclor)
         subst bound-vars)
       (typequal/attribspec-list-subst-free
         (c$::dirabsdeclor-array-static2->qualspecs dirabsdeclor)
         subst bound-vars)
       (expr-subst-free
         (c$::dirabsdeclor-array-static2->size dirabsdeclor)
         subst bound-vars))
     :array-star
     (dirabsdeclor-array-star
       (dirabsdeclor-option-subst-free
         (c$::dirabsdeclor-array-star->declor? dirabsdeclor)
         subst bound-vars))
     :function
     (b* (((mv params -)
           (param-declon-list-subst-free
             (c$::dirabsdeclor-function->params dirabsdeclor)
             subst bound-vars)))
       (c$::dirabsdeclor-function
         (dirabsdeclor-option-subst-free
           (c$::dirabsdeclor-function->declor? dirabsdeclor)
           subst bound-vars)
         params
         (c$::dirabsdeclor-function->ellipsis dirabsdeclor))))
    :measure (dirabsdeclor-count dirabsdeclor))

  (define dirabsdeclor-option-subst-free
    ((dirabsdeclor-option dirabsdeclor-optionp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result dirabsdeclor-optionp)
    (dirabsdeclor-option-case
     dirabsdeclor-option
     :some
     (dirabsdeclor-fix
       (dirabsdeclor-subst-free
         (c$::dirabsdeclor-option-some->val dirabsdeclor-option)
         subst bound-vars))
     :none nil)
    :measure (dirabsdeclor-option-count dirabsdeclor-option))

  (define param-declon-subst-free ((param-declon param-declonp)
                                   (subst ident-expr-mapp)
                                   (bound-vars ident-setp))
    :returns (mv (result param-declonp)
                 (bound-vars ident-setp))
    (b* ((specs (decl-spec-list-subst-free
                  (c$::param-declon->specs param-declon)
                  subst bound-vars))
         ((mv declor bound-vars)
          (param-declor-subst-free
            (c$::param-declon->declor param-declon)
            subst bound-vars)))
      (mv (param-declon specs declor (c$::param-declon->attribs param-declon))
          (ident-set-fix bound-vars)))
    :measure (param-declon-count param-declon))

  (define param-declon-list-subst-free
    ((param-declon-list param-declon-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (mv (result param-declon-listp)
                 (bound-vars ident-setp))
    (b* (((when (endp param-declon-list))
          (mv nil (ident-set-fix bound-vars)))
         ((mv first bound-vars)
          (param-declon-subst-free (first param-declon-list) subst bound-vars))
         ((mv rest bound-vars)
          (param-declon-list-subst-free (rest param-declon-list) subst bound-vars)))
      (mv (cons first rest)
          (ident-set-fix bound-vars)))
    :measure (param-declon-list-count param-declon-list))

  (define param-declor-subst-free ((param-declor param-declorp)
                                   (subst ident-expr-mapp)
                                   (bound-vars ident-setp))
    :returns (mv (result param-declorp)
                 (bound-vars ident-setp))
    (param-declor-case
     param-declor
     :nonabstract
     (b* (((mv declor bound-vars -)
           (declor-subst-free
             (param-declor-nonabstract->declor param-declor)
             subst bound-vars)))
       (mv (make-param-declor-nonabstract :declor declor
                                          :info param-declor.info)
           (ident-set-fix bound-vars)))
     :abstract
     (mv (param-declor-abstract
           (absdeclor-subst-free
             (c$::param-declor-abstract->declor param-declor)
             subst bound-vars))
         (ident-set-fix bound-vars))
     :none (mv (param-declor-fix param-declor) (ident-set-fix bound-vars))
     :ambig
     (mv (c$::param-declor-ambig
           (amb-declor/absdeclor-subst-free
             (c$::param-declor-ambig->declor param-declor)
             subst bound-vars))
         (ident-set-fix bound-vars)))
    :measure (param-declor-count param-declor))

  (define tyname-subst-free ((tyname tynamep)
                             (subst ident-expr-mapp)
                             (bound-vars ident-setp))
    :returns (result tynamep)
    (tyname
     (spec/qual-list-subst-free (c$::tyname->specquals tyname)
                                subst bound-vars)
     (absdeclor-option-subst-free (c$::tyname->declor? tyname)
                                  subst bound-vars)
     (c$::tyname->info tyname))
    :measure (tyname-count tyname))

  (define struni-spec-subst-free ((struni-spec struni-specp)
                                 (subst ident-expr-mapp)
                                 (bound-vars ident-setp))
    :returns (result struni-specp)
    (b* (((mv members -)
          (structdecl-list-subst-free
            (c$::struni-spec->members struni-spec)
            subst bound-vars)))
      (struni-spec (c$::struni-spec->name? struni-spec)
                  members))
    :measure (struni-spec-count struni-spec))

  (define structdecl-subst-free ((structdecl structdeclp)
                                 (subst ident-expr-mapp)
                                 (bound-vars ident-setp))
    :returns (mv (result structdeclp)
                 (bound-vars ident-setp))
    (structdecl-case
     structdecl
     :member
     (b* ((specqual (spec/qual-list-subst-free
                      (c$::structdecl-member->specqual structdecl)
                      subst bound-vars))
          ((mv declor bound-vars)
           (struct-declor-list-subst-free
             (c$::structdecl-member->declor structdecl)
             subst bound-vars)))
       (mv (c$::structdecl-member
             (c$::structdecl-member->extension structdecl)
             specqual
             declor
             (attrib-spec-list-subst-free
               (c$::structdecl-member->attrib structdecl)
               subst bound-vars))
           (ident-set-fix bound-vars)))
     :statassert
     (mv (structdecl-statassert
           (statassert-subst-free
             (c$::structdecl-statassert->unwrap structdecl)
             subst bound-vars))
         (ident-set-fix bound-vars))
     :empty (mv (structdecl-fix structdecl) (ident-set-fix bound-vars)))
    :measure (structdecl-count structdecl))

  (define structdecl-list-subst-free
    ((structdecl-list structdecl-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (mv (result structdecl-listp)
                 (bound-vars ident-setp))
    (b* (((when (endp structdecl-list))
          (mv nil (ident-set-fix bound-vars)))
         ((mv first bound-vars)
          (structdecl-subst-free (first structdecl-list) subst bound-vars))
         ((mv rest bound-vars)
          (structdecl-list-subst-free (rest structdecl-list) subst bound-vars)))
      (mv (cons first rest)
          (ident-set-fix bound-vars)))
    :measure (structdecl-list-count structdecl-list))

  (define struct-declor-subst-free ((structdeclor struct-declorp)
                                    (subst ident-expr-mapp)
                                    (bound-vars ident-setp))
    :returns (mv (result struct-declorp)
                 (bound-vars ident-setp))
    (b* ((expr? (const-expr-option-subst-free
                 (c$::struct-declor->expr? structdeclor)
                 subst bound-vars))
         ((mv declor? bound-vars)
          (declor-option-subst-free
           (c$::struct-declor->declor? structdeclor)
           subst bound-vars)))
      (mv (struct-declor declor? expr?)
          (ident-set-fix bound-vars)))
    :measure (struct-declor-count structdeclor))

  (define struct-declor-list-subst-free
    ((struct-declor-list struct-declor-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (mv (result struct-declor-listp)
                 (bound-vars ident-setp))
    (b* (((when (endp struct-declor-list))
          (mv nil (ident-set-fix bound-vars)))
         ((mv first bound-vars)
          (struct-declor-subst-free (first struct-declor-list) subst bound-vars))
         ((mv rest bound-vars)
          (struct-declor-list-subst-free (rest struct-declor-list) subst bound-vars)))
      (mv (cons first rest)
          (ident-set-fix bound-vars)))
    :measure (struct-declor-list-count struct-declor-list))

  (define enumspec-subst-free ((enumspec enumspecp)
                               (subst ident-expr-mapp)
                               (bound-vars ident-setp))
    :returns (result enumspecp)
    (enumspec (c$::enumspec->name enumspec)
              (enumer-list-subst-free (c$::enumspec->list enumspec)
                                      subst bound-vars)
              (c$::enumspec->final-comma enumspec))
    :measure (enumspec-count enumspec))

  (define enumer-subst-free ((enumer enumerp)
                             (subst ident-expr-mapp)
                             (bound-vars ident-setp))
    :returns (result enumerp)
    (enumer (c$::enumer->name enumer)
            (const-expr-option-subst-free (c$::enumer->value enumer)
                                          subst bound-vars))
    :measure (enumer-count enumer))

  (define enumer-list-subst-free ((enumer-list enumer-listp)
                                  (subst ident-expr-mapp)
                                  (bound-vars ident-setp))
    :returns (result enumer-listp)
    (if (endp enumer-list)
        nil
      (cons (enumer-subst-free (car enumer-list)
                               subst bound-vars)
            (enumer-list-subst-free (cdr enumer-list)
                                    subst bound-vars)))
    :measure (enumer-list-count enumer-list))

  (define statassert-subst-free ((statassert statassertp)
                                 (subst ident-expr-mapp)
                                 (bound-vars ident-setp))
    :returns (result statassertp)
    (statassert
     (const-expr-subst-free (c$::statassert->test statassert)
                            subst bound-vars)
     (c$::statassert->message statassert))
    :measure (statassert-count statassert))

  (define attrib-subst-free ((attrib c$::attribp)
                             (subst ident-expr-mapp)
                             (bound-vars ident-setp))
    :returns (result c$::attribp)
    (c$::attrib-case
     attrib
     :name-only (c$::attrib-fix attrib)
     :name-param
     (c$::attrib-name-param (c$::attrib-name-param->name attrib)
                            (expr-list-subst-free
                              (c$::attrib-name-param->param attrib)
                              subst bound-vars)))
    :measure (c$::attrib-count attrib))

  (define attrib-list-subst-free
    ((attrib-list c$::attrib-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result c$::attrib-listp)
    (if (endp attrib-list)
        nil
      (cons (attrib-subst-free (car attrib-list)
                               subst bound-vars)
            (attrib-list-subst-free (cdr attrib-list)
                                    subst bound-vars)))
    :measure (c$::attrib-list-count attrib-list))

  (define attrib-spec-subst-free
    ((attrib-spec c$::attrib-specp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result c$::attrib-specp)
    (c$::attrib-spec (c$::attrib-spec->uscores attrib-spec)
                     (attrib-list-subst-free
                       (c$::attrib-spec->attribs attrib-spec)
                       subst bound-vars))
    :measure (c$::attrib-spec-count attrib-spec))

  (define attrib-spec-list-subst-free
    ((attrib-spec-list c$::attrib-spec-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result c$::attrib-spec-listp)
    (if (endp attrib-spec-list)
        nil
      (cons (attrib-spec-subst-free (car attrib-spec-list)
                                    subst bound-vars)
            (attrib-spec-list-subst-free (cdr attrib-spec-list)
                                         subst bound-vars)))
    :measure (c$::attrib-spec-list-count attrib-spec-list))

  (define initdeclor-subst-free ((initdeclor initdeclorp)
                                 (subst ident-expr-mapp)
                                 (bound-vars ident-setp))
    :returns (mv (result initdeclorp)
                 (bound-vars ident-setp))
    (b* ((init? (initer-option-subst-free (c$::initdeclor->init? initdeclor)
                                          subst bound-vars))
         (attribs (attrib-spec-list-subst-free
                    (c$::initdeclor->attribs initdeclor)
                    subst bound-vars))
         ((mv declor bound-vars -)
          (declor-subst-free (c$::initdeclor->declor initdeclor)
                           subst bound-vars)))
      (mv (initdeclor declor
                      (c$::initdeclor->asm? initdeclor)
                      attribs
                      init?
                      (c$::initdeclor->info initdeclor))
          (ident-set-fix bound-vars)))
    :measure (initdeclor-count initdeclor))

  (define initdeclor-list-subst-free
    ((initdeclor-list initdeclor-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (mv (result initdeclor-listp)
                 (bound-vars ident-setp))
    (b* (((when (endp initdeclor-list))
          (mv nil (ident-set-fix bound-vars)))
         ((mv first bound-vars)
          (initdeclor-subst-free (first initdeclor-list) subst bound-vars))
         ((mv rest bound-vars)
          (initdeclor-list-subst-free (rest initdeclor-list) subst bound-vars)))
      (mv (cons first rest)
          (ident-set-fix bound-vars)))
    :measure (initdeclor-list-count initdeclor-list))

  (define decl-subst-free ((decl declp)
                           (subst ident-expr-mapp)
                           (bound-vars ident-setp))
    :returns (mv (result declp)
                 (bound-vars ident-setp))
    (decl-case
     decl
     :decl (b* ((specs (decl-spec-list-subst-free (c$::decl-decl->specs decl)
                                                  subst bound-vars))
                ((mv init bound-vars)
                 (initdeclor-list-subst-free (c$::decl-decl->init decl)
                                             subst bound-vars)))
             (mv (c$::decl-decl
                   (c$::decl-decl->extension decl)
                   specs
                   init)
                 (ident-set-fix bound-vars)))
     :statassert
     (mv (decl-statassert
           (statassert-subst-free (c$::decl-statassert->unwrap decl)
                                  subst bound-vars))
         nil))
    :measure (decl-count decl))

  (define decl-list-subst-free ((decl-list decl-listp)
                                (subst ident-expr-mapp)
                                (bound-vars ident-setp))
    :returns (mv (result decl-listp)
                 (bound-vars ident-setp))
    (b* (((when (endp decl-list))
          (mv nil (ident-set-fix bound-vars)))
         ((mv first bound-vars)
          (decl-subst-free (first decl-list) subst bound-vars))
         ((mv rest bound-vars)
          (decl-list-subst-free (rest decl-list) subst bound-vars)))
      (mv (cons first rest)
          (ident-set-fix bound-vars)))
    :measure (decl-list-count decl-list))

  (define label-subst-free ((label labelp)
                            (subst ident-expr-mapp)
                            (bound-vars ident-setp))
    :returns (result labelp)
    (label-case
     label
     :name (label-fix label)
     :casexpr
     (c$::label-casexpr
       (const-expr-subst-free (c$::label-casexpr->expr label)
                              subst bound-vars)
       (const-expr-option-subst-free
         (c$::label-casexpr->range? label)
         subst bound-vars))
     :default (label-fix label))
    :measure (label-count label))

  (define asm-output-subst-free ((asm-output c$::asm-outputp)
                                 (subst ident-expr-mapp)
                                 (bound-vars ident-setp))
    :returns (result c$::asm-outputp)
    (c$::asm-output
     (c$::asm-output->name asm-output)
     (c$::asm-output->constraint asm-output)
     (expr-subst-free (c$::asm-output->lvalue asm-output)
                      subst bound-vars))
    :measure (c$::asm-output-count asm-output))

  (define asm-output-list-subst-free
    ((asm-output-list c$::asm-output-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result c$::asm-output-listp)
    (if (endp asm-output-list)
        nil
      (cons (asm-output-subst-free (car asm-output-list)
                                   subst bound-vars)
            (asm-output-list-subst-free (cdr asm-output-list)
                                        subst bound-vars)))
    :measure (c$::asm-output-list-count asm-output-list))

  (define asm-input-subst-free ((asm-input c$::asm-inputp)
                                (subst ident-expr-mapp)
                                (bound-vars ident-setp))
    :returns (result c$::asm-inputp)
    (c$::asm-input
     (c$::asm-input->name asm-input)
     (c$::asm-input->constraint asm-input)
     (expr-subst-free (c$::asm-input->rvalue asm-input)
                      subst bound-vars))
    :measure (c$::asm-input-count asm-input))

  (define asm-input-list-subst-free
    ((asm-input-list c$::asm-input-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result c$::asm-input-listp)
    (if (endp asm-input-list)
        nil
      (cons (asm-input-subst-free (car asm-input-list)
                                  subst bound-vars)
            (asm-input-list-subst-free (cdr asm-input-list)
                                       subst bound-vars)))
    :measure (c$::asm-input-list-count asm-input-list))

  (define asm-stmt-subst-free ((asm-stmt c$::asm-stmtp)
                               (subst ident-expr-mapp)
                               (bound-vars ident-setp))
    :returns (result c$::asm-stmtp)
    (c$::asm-stmt
     (c$::asm-stmt->uscores asm-stmt)
     (c$::asm-stmt->quals asm-stmt)
     (c$::asm-stmt->template asm-stmt)
     (c$::asm-stmt->num-colons asm-stmt)
     (asm-output-list-subst-free
       (c$::asm-stmt->outputs asm-stmt)
       subst bound-vars)
     (asm-input-list-subst-free (c$::asm-stmt->inputs asm-stmt)
                                subst bound-vars)
     (c$::asm-stmt->clobbers asm-stmt)
     (c$::asm-stmt->labels asm-stmt))
    :measure (c$::asm-stmt-count asm-stmt))

  (define stmt-subst-free ((stmt stmtp)
                           (subst ident-expr-mapp)
                           (bound-vars ident-setp))
    :returns (result stmtp)
    (stmt-case
     stmt
     :labeled
     (c$::stmt-labeled
       (label-subst-free (c$::stmt-labeled->label stmt)
                         subst bound-vars)
       (stmt-subst-free (c$::stmt-labeled->stmt stmt)
                        subst bound-vars))
     ;; Interesting case
     :compound
     (b* (((mv items -)
           (block-item-list-subst-free (stmt-compound->items stmt)
                                       subst bound-vars)))
       (stmt-compound items))
     :expr
     (make-stmt-expr
      :expr? (expr-option-subst-free (c$::stmt-expr->expr? stmt)
                                     subst bound-vars)
      :info stmt.info)
     :if (c$::stmt-if (expr-subst-free (c$::stmt-if->test stmt)
                                       subst bound-vars)
                      (stmt-subst-free (c$::stmt-if->then stmt)
                                       subst bound-vars))
     :ifelse (c$::stmt-ifelse
               (expr-subst-free (c$::stmt-ifelse->test stmt)
                                subst bound-vars)
               (stmt-subst-free (c$::stmt-ifelse->then stmt)
                                subst bound-vars)
               (stmt-subst-free (c$::stmt-ifelse->else stmt)
                                subst bound-vars))
     :switch
     (c$::stmt-switch
       (expr-subst-free (c$::stmt-switch->target stmt)
                        subst bound-vars)
       (stmt-subst-free (c$::stmt-switch->body stmt)
                        subst bound-vars))
     :while (c$::stmt-while
              (expr-subst-free (c$::stmt-while->test stmt)
                               subst bound-vars)
              (stmt-subst-free (c$::stmt-while->body stmt)
                               subst bound-vars))
     :dowhile
     (c$::stmt-dowhile
       (stmt-subst-free (c$::stmt-dowhile->body stmt)
                        subst bound-vars)
       (expr-subst-free (c$::stmt-dowhile->test stmt)
                        subst bound-vars))
     :for-expr
     (c$::stmt-for-expr
       (expr-option-subst-free (c$::stmt-for-expr->init stmt)
                               subst bound-vars)
       (expr-option-subst-free (c$::stmt-for-expr->test stmt)
                               subst bound-vars)
       (expr-option-subst-free (c$::stmt-for-expr->next stmt)
                               subst bound-vars)
       (stmt-subst-free (c$::stmt-for-expr->body stmt)
                        subst bound-vars))
     :for-decl
     (b* (((mv init bound-vars)
           (decl-subst-free (c$::stmt-for-decl->init stmt)
                            subst bound-vars)))
       (c$::stmt-for-decl
         init
         (expr-option-subst-free (c$::stmt-for-decl->test stmt)
                                 subst bound-vars)
         (expr-option-subst-free (c$::stmt-for-decl->next stmt)
                                 subst bound-vars)
         (stmt-subst-free (c$::stmt-for-decl->body stmt)
                          subst bound-vars)))
     :for-ambig
     (c$::stmt-for-ambig
       (amb-decl/stmt-subst-free (c$::stmt-for-ambig->init stmt)
                                 subst bound-vars)
       (expr-option-subst-free (c$::stmt-for-ambig->test stmt)
                               subst bound-vars)
       (expr-option-subst-free (c$::stmt-for-ambig->next stmt)
                               subst bound-vars)
       (stmt-subst-free (c$::stmt-for-ambig->body stmt)
                        subst bound-vars))
     :goto (stmt-fix stmt)
     :continue (stmt-fix stmt)
     :break (stmt-fix stmt)
     :return
     (make-stmt-return
      :expr?
       (expr-option-subst-free (c$::stmt-return->expr? stmt)
                               subst bound-vars)
       :info stmt.info)
     :asm (c$::stmt-asm
            (asm-stmt-subst-free (c$::stmt-asm->unwrap stmt)
                                 subst bound-vars)))
    :measure (stmt-count stmt))

  (define block-item-subst-free ((block-item block-itemp)
                                 (subst ident-expr-mapp)
                                 (bound-vars ident-setp))
    :returns (mv (result block-itemp)
                 (bound-vars ident-setp))
    (block-item-case
     block-item
     :decl
     (b* (((mv decl bound-vars)
           (decl-subst-free (c$::block-item-decl->decl block-item)
                            subst bound-vars)))
       (mv (make-block-item-decl :decl decl :info block-item.info)
           (ident-set-fix bound-vars)))
     :stmt
     (mv (make-block-item-stmt
          :stmt (stmt-subst-free (c$::block-item-stmt->stmt block-item)
                                 subst bound-vars)
          :info block-item.info)
         (ident-set-fix bound-vars))
     :ambig
     (mv (c$::block-item-ambig (amb-decl/stmt-subst-free
                                 (c$::block-item-ambig->unwrap block-item)
                                 subst bound-vars))
         (ident-set-fix bound-vars)))
    :measure (block-item-count block-item))

  (define block-item-list-subst-free
    ((block-item-list block-item-listp)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (mv (result block-item-listp)
                 (bound-vars ident-setp))
    (b* (((when (endp block-item-list))
          (mv nil (ident-set-fix bound-vars)))
         ((mv first bound-vars)
          (block-item-subst-free (first block-item-list) subst bound-vars))
         ((mv rest bound-vars)
          (block-item-list-subst-free (rest block-item-list) subst bound-vars)))
      (mv (cons first rest)
          (ident-set-fix bound-vars)))
    :measure (block-item-list-count block-item-list))

  (define amb-expr/tyname-subst-free
    ((amb-expr/tyname c$::amb-expr/tyname-p)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result c$::amb-expr/tyname-p)
    (c$::amb-expr/tyname
     (expr-subst-free
       (c$::amb-expr/tyname->expr amb-expr/tyname)
       subst bound-vars)
     (tyname-subst-free
       (c$::amb-expr/tyname->tyname amb-expr/tyname)
       subst bound-vars))
    :measure (c$::amb-expr/tyname-count amb-expr/tyname))

  (define amb-declor/absdeclor-subst-free
    ((amb-declor/absdeclor c$::amb-declor/absdeclor-p)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result c$::amb-declor/absdeclor-p)
    (b* (((mv declor bound-vars -)
          (declor-subst-free
            (c$::amb-declor/absdeclor->declor amb-declor/absdeclor)
            subst bound-vars)))
      (c$::amb-declor/absdeclor
        declor
        (absdeclor-subst-free
          (c$::amb-declor/absdeclor->absdeclor amb-declor/absdeclor)
          subst bound-vars)))
    :measure (c$::amb-declor/absdeclor-count amb-declor/absdeclor))

  (define amb-decl/stmt-subst-free
    ((amb-decl/stmt c$::amb-decl/stmt-p)
     (subst ident-expr-mapp)
     (bound-vars ident-setp))
    :returns (result c$::amb-decl/stmt-p)
    (b* (((mv decl bound-vars)
          (decl-subst-free (c$::amb-decl/stmt->decl amb-decl/stmt)
                           subst bound-vars)))
      (c$::amb-decl/stmt
        decl
        (expr-subst-free (c$::amb-decl/stmt->stmt amb-decl/stmt)
                         subst bound-vars)))
    :measure (c$::amb-decl/stmt-count amb-decl/stmt))
  :verify-guards :after-returns
  :flag-local nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-subst-free
  ((fundef fundefp)
   (subst ident-expr-mapp)
   (bound-vars ident-setp))
  :short "Substitute expressions in for free variables appearing in a function
          definition."
  :returns (mv (result fundefp)
               (bound-vars ident-setp))
  (b* (((fundef fundef) fundef)
       (spec (decl-spec-list-subst-free fundef.spec subst bound-vars))
       ((mv declor bound-vars param-bound-vars)
        (declor-subst-free fundef.declor subst bound-vars))
       (body-bound-vars (union bound-vars param-bound-vars))
       (attribs (attrib-spec-list-subst-free fundef.attribs subst body-bound-vars))
       ((mv decls body-bound-vars)
        (decl-list-subst-free fundef.decls subst body-bound-vars))
       ((mv body &) (block-item-list-subst-free fundef.body subst body-bound-vars)))
    (mv (make-fundef
          :extension fundef.extension
          :spec spec
          :declor declor
          :asm? fundef.asm?
          :attribs attribs
          :decls decls
          :body body
          :info fundef.info)
        bound-vars)))
