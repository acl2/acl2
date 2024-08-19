; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "../../syntax/abstract-syntax")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ free-vars
  :parents (utilities)
  :short "A utility to collect free variables over a C AST."
  :long
  (xdoc::topstring
    (xdoc::p
      "This returns a set of all identifiers used as variables within the AST,
       excluding those variables which have first been declared, i.e. in a
       statement declaration or as a function parameter.")
    (xdoc::p
      "It only considers variables of regular data object, not other types of
       named language constructs, such as @('typedef') type names."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines declor/dirdeclor-get-ident
  (define declor-get-ident
    ((declor declorp))
    :short "Get the identifier described by a declarator."
    :returns (ident? ident-optionp)
    (b* (((declor declor) declor))
      (dirdeclor-get-ident declor.decl))
    :measure (declor-count declor))

  (define dirdeclor-get-ident
    :short "Get the identifier described by a direct declarator."
    ((dirdeclor dirdeclorp))
    :returns (ident? ident-optionp)
    (dirdeclor-case
     dirdeclor
     :ident dirdeclor.unwrap
     :paren (declor-get-ident dirdeclor.unwrap)
     :array (dirdeclor-get-ident dirdeclor.decl)
     :array-static1 (dirdeclor-get-ident dirdeclor.decl)
     :array-static2 (dirdeclor-get-ident dirdeclor.decl)
     :array-star (dirdeclor-get-ident dirdeclor.decl)
     :function-params (dirdeclor-get-ident dirdeclor.decl)
     :function-names (dirdeclor-get-ident dirdeclor.decl))
    :measure (dirdeclor-count dirdeclor))

  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines free-vars-exprs/decls
  (define free-vars-expr
    ((expr exprp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an expression."
    :returns (free-vars ident-setp)
    (expr-case
     expr
     :ident (if (in expr.unwrap bound-vars)
                nil
              (insert expr.unwrap nil))
     :paren (free-vars-expr expr.unwrap bound-vars)
     :gensel (union (free-vars-expr expr.control bound-vars)
                    (free-vars-genassoc-list expr.assocs bound-vars))
     :arrsub (union (free-vars-expr expr.arg1 bound-vars)
                    (free-vars-expr expr.arg2 bound-vars))
     :funcall (union (free-vars-expr expr.fun bound-vars)
                     (free-vars-expr-list expr.args bound-vars))
     :complit (free-vars-desiniter-list expr.elems bound-vars)
     :unary (free-vars-expr expr.arg bound-vars)
     :cast (free-vars-expr expr.arg bound-vars)
     :binary (union (free-vars-expr expr.arg1 bound-vars)
                    (free-vars-expr expr.arg2 bound-vars))
     :cond (union (free-vars-expr expr.test bound-vars)
                  (union (free-vars-expr expr.then bound-vars)
                         (free-vars-expr expr.else bound-vars)))
     :comma (union (free-vars-expr expr.first bound-vars)
                   (free-vars-expr expr.next bound-vars))
     :otherwise nil)
    :measure (expr-count expr))

  (define free-vars-expr-list
    ((exprs expr-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an expression list."
    :returns (free-vars ident-setp)
    (if (endp exprs)
        nil
      (union (free-vars-expr (first exprs) bound-vars)
             (free-vars-expr-list (rest exprs) bound-vars)))
    :measure (expr-list-count exprs))

  (define free-vars-expr-option
    ((expr? expr-optionp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an optional expression."
    :returns (free-vars ident-setp)
    (expr-option-case
     expr?
     :some (free-vars-expr expr?.val bound-vars)
     :none nil)
    :measure (expr-option-count expr?))

  (define free-vars-genassoc
    ((genassoc genassocp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a generic association."
    :returns (free-vars ident-setp)
    (genassoc-case
     genassoc
     :type (free-vars-expr genassoc.expr bound-vars)
     :default (free-vars-expr genassoc.expr bound-vars))
    :measure (genassoc-count genassoc))

  (define free-vars-genassoc-list
    ((genassocs genassoc-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a generic association list."
    :returns (free-vars ident-setp)
    (if (endp genassocs)
        nil
      (union (free-vars-genassoc (first genassocs) bound-vars)
             (free-vars-genassoc-list (rest genassocs) bound-vars)))
    :measure (genassoc-list-count genassocs))

  (define free-vars-initer
    ((initer initerp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an initializer."
    :returns (free-vars ident-setp)
    (initer-case
     initer
     :single (free-vars-expr initer.expr bound-vars)
     :list (free-vars-desiniter-list initer.elems bound-vars))
    :measure (initer-count initer))

  (define free-vars-initer-option
    ((initer? initer-optionp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an optional initializer."
    :returns (free-vars ident-setp)
    (initer-option-case
     initer?
     :some (free-vars-initer initer?.val bound-vars)
     :none nil)
    :measure (initer-option-count initer?))

  (define free-vars-desiniter
    ((desiniter desiniterp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an initializer with optional
            designations."
    :returns (free-vars ident-setp)
    (b* (((desiniter desiniter) desiniter))
      (free-vars-initer desiniter.init bound-vars))
    :measure (desiniter-count desiniter))

  (define free-vars-desiniter-list
    ((desiniters desiniter-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of initializers with
            optional designations."
    :returns (free-vars ident-setp)
    (if (endp desiniters)
        nil
      (union (free-vars-desiniter (first desiniters) bound-vars)
             (free-vars-desiniter-list (rest desiniters) bound-vars)))
    :measure (desiniter-list-count desiniters))

  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define free-vars-initdeclor
  ((initdeclor initdeclorp)
   (bound-vars ident-setp))
  :short "Collect free variables appearing in an initializer declarator."
  :returns (mv (free-vars ident-setp)
               (bound-vars ident-setp))
  (b* ((bound-vars (ident-set-fix bound-vars))
       ((initdeclor initdeclor) initdeclor)
       (ident (declor-get-ident initdeclor.declor)))
    (mv (free-vars-initer-option initdeclor.init? bound-vars)
        (if ident
            (insert (ident-fix ident) bound-vars)
          bound-vars))))

(define free-vars-initdeclor-list
  ((initdeclors initdeclor-listp)
   (bound-vars ident-setp))
  :short "Collect free variables appearing in a list of initializer
          declarators."
  :returns (mv (free-vars ident-setp)
               (bound-vars ident-setp))
  (b* ((bound-vars (ident-set-fix bound-vars))
       ((when (endp initdeclors))
        (mv nil bound-vars))
       ((mv free-vars1 bound-vars)
        (free-vars-initdeclor (first initdeclors) bound-vars))
       ((mv free-vars2 bound-vars)
        (free-vars-initdeclor-list (rest initdeclors) bound-vars)))
    (mv (union free-vars1 free-vars2)
        bound-vars))
  :verify-guards :after-returns)

(define free-vars-decl
  ((decl declp)
   (bound-vars ident-setp))
  :short "Collect free variables appearing in a declaration."
  :returns (mv (free-vars ident-setp)
               (bound-vars ident-setp))
  (b* ((bound-vars (ident-set-fix bound-vars)))
    (decl-case
      decl
      :decl (free-vars-initdeclor-list decl.init bound-vars)
      :statassert (mv nil bound-vars))))

(define free-vars-decl-list
  ((decls decl-listp)
   (bound-vars ident-setp))
  :short "Collect free variables appearing in a list of declarations."
  :returns (mv (free-vars ident-setp)
               (bound-vars ident-setp))
  (b* ((bound-vars (ident-set-fix bound-vars))
       ((when (endp decls))
        (mv nil bound-vars))
       ((mv free-vars1 bound-vars)
        (free-vars-decl (first decls) bound-vars))
       ((mv free-vars2 bound-vars)
        (free-vars-decl-list (rest decls) bound-vars)))
    (mv (union free-vars1 free-vars2)
        bound-vars))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines free-vars-stmts/blocks
  (define free-vars-stmt
    ((stmt stmtp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a statement."
    :returns (free-vars ident-setp)
    (stmt-case
     stmt
     :labeled (free-vars-stmt stmt.stmt bound-vars)
     :compound (free-vars-block-item-list stmt.items bound-vars)
     :expr (free-vars-expr-option stmt.expr? bound-vars)
     :if (union (free-vars-expr stmt.test bound-vars)
                (free-vars-stmt stmt.then bound-vars))
     :ifelse (union (free-vars-expr stmt.test bound-vars)
                    (union (free-vars-stmt stmt.then bound-vars)
                           (free-vars-stmt stmt.else bound-vars)))
     :switch (union (free-vars-expr stmt.target bound-vars)
                    (free-vars-stmt stmt.body bound-vars))
     :while (union (free-vars-expr stmt.test bound-vars)
                   (free-vars-stmt stmt.body bound-vars))
     :dowhile (union (free-vars-stmt stmt.body bound-vars)
                     (free-vars-expr stmt.test bound-vars))
     :for-expr (union (free-vars-expr-option stmt.init bound-vars)
                      (union (free-vars-expr-option stmt.test bound-vars)
                             (union (free-vars-expr-option stmt.next bound-vars)
                                    (free-vars-stmt stmt.body bound-vars))))
     :for-decl (b* (((mv free-vars for-bound-vars)
                     (free-vars-decl stmt.init bound-vars)))
                 (union free-vars
                        (union (free-vars-expr-option stmt.test for-bound-vars)
                               (union (free-vars-expr-option stmt.next for-bound-vars)
                                      (free-vars-stmt stmt.body for-bound-vars)))))
     :return (free-vars-expr-option stmt.expr? bound-vars)
     :otherwise nil)
    :measure (stmt-count stmt))

  (define free-vars-block-item
    ((item block-itemp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a block item."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* ((bound-vars (ident-set-fix bound-vars)))
      (block-item-case
        item
        :decl (free-vars-decl item.unwrap bound-vars)
        :stmt (mv (free-vars-stmt item.unwrap bound-vars)
                  bound-vars)
        :ambig (mv nil bound-vars)))
    :measure (block-item-count item))

  (define free-vars-block-item-list
    ((items block-item-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of block item."
    :returns (free-vars ident-setp)
    (b* (((when (endp items))
          nil)
         ((mv free-vars1 bound-vars)
          (free-vars-block-item (first items) bound-vars)))
      (union free-vars1
             (free-vars-block-item-list (rest items) bound-vars)))
    :measure (block-item-list-count items))

  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define free-vars-fundef
  ((fundef fundefp)
   (bound-vars ident-setp))
  :short "Collect free variables appearing in a function function definition."
  :returns (free-vars ident-setp)
  (b* (((fundef fundef) fundef)
       ((mv free-vars bound-vars)
        (free-vars-decl-list fundef.decls bound-vars)))
    (union free-vars
           (free-vars-stmt fundef.body bound-vars))))
