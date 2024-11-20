; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/unambiguity")

(include-book "std/lists/index-of" :dir :system)

(local (include-book "std/typed-lists/character-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ simpadd0
  :parents (transformation-tools)
  :short "A transformation to simplify @('x + 0') to @('x')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a very simple proof-of-concept transformation,
     which replaces expressions of the form @('x + 0') with @('x').
     Due to C's arithmetic conversions, it is not immediately clear whether
     this transformation always preserves code equivalence,
     but for now we are not concerned about this,
     as the goal of this proof-of-concept transformation
     is just to show a plausible example of C-to-C transformation;
     and there are certainly many cases (perhaps all cases) in which
     this transformation is indeed equivalence-preserving.")
   (xdoc::p
    "This transformation is implemented as a collection of ACL2 functions
     that operate on the abstract syntax,
     following the recursion structure of the abstract syntax
     (similarly to the @(see c$::printer)).
     This is a typical pattern for C-to-C transformations,
     which we may want to partially automate,
     via things like generalized `folds' over the abstract syntax."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines simpadd0-exprs/decls/stmts
  :short "Transform expressions, declarations, statements,
          and related entities."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr ((expr exprp))
    :guard (expr-unambp expr)
    :returns (new-expr exprp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an expression."
    (expr-case
     expr
     :ident (expr-fix expr)
     :const (expr-fix expr)
     :string (expr-fix expr)
     :paren (expr-paren (simpadd0-expr expr.inner))
     :gensel (make-expr-gensel
              :control (simpadd0-expr expr.control)
              :assocs (simpadd0-genassoc-list expr.assocs))
     :arrsub (make-expr-arrsub
              :arg1 (simpadd0-expr expr.arg1)
              :arg2 (simpadd0-expr expr.arg2))
     :funcall (make-expr-funcall
               :fun (simpadd0-expr expr.fun)
               :args (simpadd0-expr-list expr.args))
     :member (make-expr-member
              :arg (simpadd0-expr expr.arg)
              :name expr.name)
     :memberp (make-expr-memberp
               :arg (simpadd0-expr expr.arg)
               :name expr.name)
     :complit (make-expr-complit
               :type (simpadd0-tyname expr.type)
               :elems (simpadd0-desiniter-list expr.elems)
               :final-comma expr.final-comma)
     :unary (make-expr-unary
             :op expr.op
             :arg (simpadd0-expr expr.arg))
     :sizeof (expr-sizeof (simpadd0-tyname expr.type))
     :sizeof-ambig (prog2$ (impossible) (irr-expr))
     :alignof (make-expr-alignof :type (simpadd0-tyname expr.type)
                                 :uscores expr.uscores)
     :cast (make-expr-cast
            :type (simpadd0-tyname expr.type)
            :arg (simpadd0-expr expr.arg))
     :binary (b* ((arg1 (simpadd0-expr expr.arg1))
                  (arg2 (simpadd0-expr expr.arg2)))
               (if (c$::expr-zerop arg2)
                   arg1
                 (make-expr-binary
                  :op expr.op
                  :arg1 arg1
                  :arg2 arg2)))
     :cond (make-expr-cond
            :test (simpadd0-expr expr.test)
            :then (simpadd0-expr-option expr.then)
            :else (simpadd0-expr expr.else))
     :comma (make-expr-comma
             :first (simpadd0-expr expr.first)
             :next (simpadd0-expr expr.next))
     :cast/call-ambig (prog2$ (impossible) (irr-expr))
     :cast/mul-ambig (prog2$ (impossible) (irr-expr))
     :cast/add-ambig (prog2$ (impossible) (irr-expr))
     :cast/sub-ambig (prog2$ (impossible) (irr-expr))
     :cast/and-ambig (prog2$ (impossible) (irr-expr))
     :stmt (expr-stmt (simpadd0-block-item-list expr.items))
     :tycompat (make-expr-tycompat
                :type1 (simpadd0-tyname expr.type1)
                :type2 (simpadd0-tyname expr.type2))
     :offsetof (make-expr-offsetof
                :type (simpadd0-tyname expr.type)
                :member (simpadd0-member-designor expr.member))
     :va-arg (make-expr-va-arg
              :list (simpadd0-expr expr.list)
              :type (simpadd0-tyname expr.type))
     :extension (expr-extension (simpadd0-expr expr.expr)))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr-list ((exprs expr-listp))
    :guard (expr-list-unambp exprs)
    :returns (new-exprs expr-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of expressions."
    (cond ((endp exprs) nil)
          (t (cons (simpadd0-expr (car exprs))
                   (simpadd0-expr-list (cdr exprs)))))
    :measure (expr-list-count exprs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr-option ((expr? expr-optionp))
    :guard (expr-option-unambp expr?)
    :returns (new-expr? expr-optionp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional expression."
    (expr-option-case
     expr?
     :some (simpadd0-expr expr?.val)
     :none nil)
    :measure (expr-option-count expr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-const-expr ((cexpr const-exprp))
    :guard (const-expr-unambp cexpr)
    :returns (new-cexpr const-exprp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a constant expression."
    (const-expr (simpadd0-expr (const-expr->expr cexpr)))
    :measure (const-expr-count cexpr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-const-expr-option ((cexpr? const-expr-optionp))
    :guard (const-expr-option-unambp cexpr?)
    :returns (new-cexpr? const-expr-optionp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional constant expression."
    (const-expr-option-case
     cexpr?
     :some (simpadd0-const-expr cexpr?.val)
     :none nil)
    :measure (const-expr-option-count cexpr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-genassoc ((genassoc genassocp))
    :guard (genassoc-unambp genassoc)
    :returns (new-genassoc genassocp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a generic association."
    (genassoc-case
     genassoc
     :type (make-genassoc-type
            :type (simpadd0-tyname genassoc.type)
            :expr (simpadd0-expr genassoc.expr))
     :default (genassoc-default (simpadd0-expr genassoc.expr)))
    :measure (genassoc-count genassoc))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-genassoc-list ((genassocs genassoc-listp))
    :guard (genassoc-list-unambp genassocs)
    :returns (new-genassocs genassoc-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of generic associations."
    (cond ((endp genassocs) nil)
          (t (cons (simpadd0-genassoc (car genassocs))
                   (simpadd0-genassoc-list (cdr genassocs)))))
    :measure (genassoc-list-count genassocs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-member-designor ((memdes member-designorp))
    :guard (member-designor-unambp memdes)
    :returns (new-memdes member-designorp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a member designator."
    (member-designor-case
     memdes
     :ident (member-designor-fix memdes)
     :dot (make-member-designor-dot
           :member (simpadd0-member-designor memdes.member)
           :name memdes.name)
     :sub (make-member-designor-sub
           :member (simpadd0-member-designor memdes.member)
           :index (simpadd0-expr memdes.index)))
    :measure (member-designor-count memdes))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-type-spec ((tyspec type-specp))
    :guard (type-spec-unambp tyspec)
    :returns (new-tyspec type-specp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type specifier."
    (type-spec-case
     tyspec
     :void (type-spec-fix tyspec)
     :char (type-spec-fix tyspec)
     :short (type-spec-fix tyspec)
     :int (type-spec-fix tyspec)
     :long (type-spec-fix tyspec)
     :float (type-spec-fix tyspec)
     :double (type-spec-fix tyspec)
     :signed (type-spec-fix tyspec)
     :unsigned (type-spec-fix tyspec)
     :bool (type-spec-fix tyspec)
     :complex (type-spec-fix tyspec)
     :atomic (type-spec-atomic (simpadd0-tyname tyspec.type))
     :struct (type-spec-struct (simpadd0-strunispec tyspec.spec))
     :union (type-spec-union (simpadd0-strunispec tyspec.spec))
     :enum (type-spec-enum (simpadd0-enumspec tyspec.spec))
     :typedef (type-spec-fix tyspec)
     :int128 (type-spec-fix tyspec)
     :float32 (type-spec-fix tyspec)
     :float32x (type-spec-fix tyspec)
     :float64 (type-spec-fix tyspec)
     :float64x (type-spec-fix tyspec)
     :float128 (type-spec-fix tyspec)
     :float128x (type-spec-fix tyspec)
     :builtin-va-list (type-spec-fix tyspec)
     :struct-empty (type-spec-fix tyspec)
     :typeof-expr (make-type-spec-typeof-expr
                   :expr (simpadd0-expr tyspec.expr)
                   :uscores tyspec.uscores)
     :typeof-type (make-type-spec-typeof-type
                   :type (simpadd0-tyname tyspec.type)
                   :uscores tyspec.uscores)
     :typeof-ambig (prog2$ (impossible) (irr-type-spec))
     :auto-type (type-spec-fix tyspec))
    :measure (type-spec-count tyspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-spec/qual ((specqual spec/qual-p))
    :guard (spec/qual-unambp specqual)
    :returns (new-specqual spec/qual-p)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type specifier or qualifier."
    (spec/qual-case
     specqual
     :tyspec (spec/qual-tyspec (simpadd0-type-spec specqual.spec))
     :tyqual (spec/qual-fix specqual)
     :align (spec/qual-align (simpadd0-align-spec specqual.spec))
     :attrib (spec/qual-fix specqual))
    :measure (spec/qual-count specqual))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-spec/qual-list ((specquals spec/qual-listp))
    :guard (spec/qual-list-unambp specquals)
    :returns (new-specquals spec/qual-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of type specifiers and qualifiers."
    (cond ((endp specquals) nil)
          (t (cons (simpadd0-spec/qual (car specquals))
                   (simpadd0-spec/qual-list (cdr specquals)))))
    :measure (spec/qual-list-count specquals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-align-spec ((alignspec align-specp))
    :guard (align-spec-unambp alignspec)
    :returns (new-alignspec align-specp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an alignment specifier."
    (align-spec-case
     alignspec
     :alignas-type (align-spec-alignas-type (simpadd0-tyname alignspec.type))
     :alignas-expr (align-spec-alignas-expr (simpadd0-const-expr alignspec.expr))
     :alignas-ambig (prog2$ (impossible) (irr-align-spec)))
    :measure (align-spec-count alignspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl-spec ((declspec decl-specp))
    :guard (decl-spec-unambp declspec)
    :returns (new-declspec decl-specp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declaration specifier."
    (decl-spec-case
     declspec
     :stocla (decl-spec-fix declspec)
     :tyspec (decl-spec-tyspec (simpadd0-type-spec declspec.spec))
     :tyqual (decl-spec-fix declspec)
     :funspec (decl-spec-fix declspec)
     :align (decl-spec-align (simpadd0-align-spec declspec.spec))
     :attrib (decl-spec-fix declspec)
     :stdcall (decl-spec-fix declspec)
     :declspec (decl-spec-fix declspec))
    :measure (decl-spec-count declspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl-spec-list ((declspecs decl-spec-listp))
    :guard (decl-spec-list-unambp declspecs)
    :returns (new-declspecs decl-spec-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of declaration specifiers."
    (cond ((endp declspecs) nil)
          (t (cons (simpadd0-decl-spec (car declspecs))
                   (simpadd0-decl-spec-list (cdr declspecs)))))
    :measure (decl-spec-list-count declspecs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initer ((initer initerp))
    :guard (initer-unambp initer)
    :returns (new-initer initerp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer."
    (initer-case
     initer
     :single (initer-single (simpadd0-expr initer.expr))
     :list (make-initer-list
            :elems (simpadd0-desiniter-list initer.elems)
            :final-comma initer.final-comma))
    :measure (initer-count initer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initer-option ((initer? initer-optionp))
    :guard (initer-option-unambp initer?)
    :returns (new-initer? initer-optionp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional initializer."
    (initer-option-case
     initer?
     :some (simpadd0-initer initer?.val)
     :none nil)
    :measure (initer-option-count initer?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-desiniter ((desiniter desiniterp))
    :guard (desiniter-unambp desiniter)
    :returns (new-desiniter desiniterp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer with optional designations."
    (b* (((desiniter desiniter) desiniter))
      (make-desiniter
       :design (simpadd0-designor-list desiniter.design)
       :init (simpadd0-initer desiniter.init)))
    :measure (desiniter-count desiniter))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-desiniter-list ((desiniters desiniter-listp))
    :guard (desiniter-list-unambp desiniters)
    :returns (new-desiniters desiniter-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of initializers with optional designations."
    (cond ((endp desiniters) nil)
          (t (cons (simpadd0-desiniter (car desiniters))
                   (simpadd0-desiniter-list (cdr desiniters)))))
    :measure (desiniter-list-count desiniters))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-designor ((designor designorp))
    :guard (designor-unambp designor)
    :returns (new-designor designorp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a designator."
    (designor-case
     designor
     :sub (designor-sub (simpadd0-const-expr designor.index))
     :dot (designor-fix designor))
    :measure (designor-count designor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-designor-list ((designors designor-listp))
    :guard (designor-list-unambp designors)
    :returns (new-designors designor-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of designators."
    (cond ((endp designors) nil)
          (t (cons (simpadd0-designor (car designors))
                   (simpadd0-designor-list (cdr designors)))))
    :measure (designor-list-count designors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declor ((declor declorp))
    :guard (declor-unambp declor)
    :returns (new-declor declorp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declarator."
    (b* (((declor declor) declor))
      (make-declor
       :pointers declor.pointers
       :decl (simpadd0-dirdeclor declor.decl)))
    :measure (declor-count declor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declor-option ((declor? declor-optionp))
    :guard (declor-option-unambp declor?)
    :returns (new-declor? declor-optionp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional declarator."
    (declor-option-case
     declor?
     :some (simpadd0-declor declor?.val)
     :none nil)
    :measure (declor-option-count declor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirdeclor ((dirdeclor dirdeclorp))
    :guard (dirdeclor-unambp dirdeclor)
    :returns (new-dirdeclor dirdeclorp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a direct declarator."
    (dirdeclor-case
     dirdeclor
     :ident (dirdeclor-fix dirdeclor)
     :paren (dirdeclor-paren (simpadd0-declor dirdeclor.unwrap))
     :array (make-dirdeclor-array
             :decl (simpadd0-dirdeclor dirdeclor.decl)
             :tyquals dirdeclor.tyquals
             :expr? (simpadd0-expr-option dirdeclor.expr?))
     :array-static1 (make-dirdeclor-array-static1
                     :decl (simpadd0-dirdeclor dirdeclor.decl)
                     :tyquals dirdeclor.tyquals
                     :expr (simpadd0-expr dirdeclor.expr))
     :array-static2 (make-dirdeclor-array-static2
                     :decl (simpadd0-dirdeclor dirdeclor.decl)
                     :tyquals dirdeclor.tyquals
                     :expr (simpadd0-expr dirdeclor.expr))
     :array-star (make-dirdeclor-array-star
                  :decl (simpadd0-dirdeclor dirdeclor.decl)
                  :tyquals dirdeclor.tyquals)
     :function-params (make-dirdeclor-function-params
                       :decl (simpadd0-dirdeclor dirdeclor.decl)
                       :params (simpadd0-paramdecl-list dirdeclor.params)
                       :ellipsis dirdeclor.ellipsis)
     :function-names (make-dirdeclor-function-names
                      :decl (simpadd0-dirdeclor dirdeclor.decl)
                      :names dirdeclor.names))
    :measure (dirdeclor-count dirdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-absdeclor ((absdeclor absdeclorp))
    :guard (absdeclor-unambp absdeclor)
    :returns (new-absdeclor absdeclorp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an abstract declarator."
    (b* (((absdeclor absdeclor) absdeclor))
      (make-absdeclor
       :pointers absdeclor.pointers
       :decl? (simpadd0-dirabsdeclor-option absdeclor.decl?)))
    :measure (absdeclor-count absdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-absdeclor-option ((absdeclor? absdeclor-optionp))
    :guard (absdeclor-option-unambp absdeclor?)
    :returns (new-absdeclor? absdeclor-optionp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional abstract declarator."
    (absdeclor-option-case
     absdeclor?
     :some (simpadd0-absdeclor absdeclor?.val)
     :none nil)
    :measure (absdeclor-option-count absdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirabsdeclor ((dirabsdeclor dirabsdeclorp))
    :guard (dirabsdeclor-unambp dirabsdeclor)
    :returns (new-dirabsdeclor dirabsdeclorp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a direct abstract declarator."
    (dirabsdeclor-case
     dirabsdeclor
     :dummy-base (prog2$
                  (raise "Misusage error: ~x0." (dirabsdeclor-fix dirabsdeclor))
                  (irr-dirabsdeclor))
     :paren (dirabsdeclor-paren (simpadd0-absdeclor dirabsdeclor.unwrap))
     :array (make-dirabsdeclor-array
             :decl? (simpadd0-dirabsdeclor-option dirabsdeclor.decl?)
             :tyquals dirabsdeclor.tyquals
             :expr? (simpadd0-expr-option dirabsdeclor.expr?))
     :array-static1 (make-dirabsdeclor-array-static1
                     :decl? (simpadd0-dirabsdeclor-option dirabsdeclor.decl?)
                     :tyquals dirabsdeclor.tyquals
                     :expr (simpadd0-expr dirabsdeclor.expr))
     :array-static2 (make-dirabsdeclor-array-static2
                     :decl? (simpadd0-dirabsdeclor-option dirabsdeclor.decl?)
                     :tyquals dirabsdeclor.tyquals
                     :expr (simpadd0-expr dirabsdeclor.expr))
     :array-star (dirabsdeclor-array-star
                  (simpadd0-dirabsdeclor-option dirabsdeclor.decl?))
     :function (make-dirabsdeclor-function
                :decl? (simpadd0-dirabsdeclor-option dirabsdeclor.decl?)
                :params (simpadd0-paramdecl-list dirabsdeclor.params)
                :ellipsis dirabsdeclor.ellipsis))
    :measure (dirabsdeclor-count dirabsdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirabsdeclor-option ((dirabsdeclor? dirabsdeclor-optionp))
    :guard (dirabsdeclor-option-unambp dirabsdeclor?)
    :returns (new-dirabsdeclor? dirabsdeclor-optionp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional direct abstract declarator."
    (dirabsdeclor-option-case
     dirabsdeclor?
     :some (simpadd0-dirabsdeclor dirabsdeclor?.val)
     :none nil)
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-paramdecl ((paramdecl paramdeclp))
    :guard (paramdecl-unambp paramdecl)
    :returns (new-paramdecl paramdeclp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a parameter declaration."
    (b* (((paramdecl paramdecl) paramdecl))
      (make-paramdecl :spec (simpadd0-decl-spec-list paramdecl.spec)
                      :decl (simpadd0-paramdeclor paramdecl.decl)))
    :measure (paramdecl-count paramdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-paramdecl-list ((paramdecls paramdecl-listp))
    :guard (paramdecl-list-unambp paramdecls)
    :returns (new-paramdecls paramdecl-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of parameter declarations."
    (cond ((endp paramdecls) nil)
          (t (cons (simpadd0-paramdecl (car paramdecls))
                   (simpadd0-paramdecl-list (cdr paramdecls)))))
    :measure (paramdecl-list-count paramdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-paramdeclor ((paramdeclor paramdeclorp))
    :guard (paramdeclor-unambp paramdeclor)
    :returns (new-paramdeclor paramdeclorp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a parameter declarator."
    (paramdeclor-case
     paramdeclor
     :declor (paramdeclor-declor (simpadd0-declor paramdeclor.unwrap))
     :absdeclor (paramdeclor-absdeclor (simpadd0-absdeclor paramdeclor.unwrap))
     :none (paramdeclor-none)
     :ambig (prog2$ (impossible) (irr-paramdeclor)))
    :measure (paramdeclor-count paramdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-tyname ((tyname tynamep))
    :guard (tyname-unambp tyname)
    :returns (new-tyname tynamep)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type name."
    (b* (((tyname tyname) tyname))
      (make-tyname
       :specqual (simpadd0-spec/qual-list tyname.specqual)
       :decl? (simpadd0-absdeclor-option tyname.decl?)))
    :measure (tyname-count tyname))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-strunispec ((strunispec strunispecp))
    :guard (strunispec-unambp strunispec)
    :returns (new-strunispec strunispecp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure or union specifier."
    (b* (((strunispec strunispec) strunispec))
      (make-strunispec
       :name strunispec.name
       :members (simpadd0-structdecl-list strunispec.members)))
    :measure (strunispec-count strunispec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdecl ((structdecl structdeclp))
    :guard (structdecl-unambp structdecl)
    :returns (new-structdecl structdeclp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure declaration."
    (structdecl-case
     structdecl
     :member (make-structdecl-member
              :extension structdecl.extension
              :specqual (simpadd0-spec/qual-list structdecl.specqual)
              :declor (simpadd0-structdeclor-list structdecl.declor)
              :attrib structdecl.attrib)
     :statassert (structdecl-statassert
                  (simpadd0-statassert structdecl.unwrap))
     :empty (structdecl-empty))
    :measure (structdecl-count structdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdecl-list ((structdecls structdecl-listp))
    :guard (structdecl-list-unambp structdecls)
    :returns (new-structdecls structdecl-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of structure declarations."
    (cond ((endp structdecls) nil)
          (t (cons (simpadd0-structdecl (car structdecls))
                   (simpadd0-structdecl-list (cdr structdecls)))))
    :measure (structdecl-list-count structdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdeclor ((structdeclor structdeclorp))
    :guard (structdeclor-unambp structdeclor)
    :returns (new-structdeclor structdeclorp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure declarator."
    (b* (((structdeclor structdeclor) structdeclor))
      (make-structdeclor
       :declor? (simpadd0-declor-option structdeclor.declor?)
       :expr? (simpadd0-const-expr-option structdeclor.expr?)))
    :measure (structdeclor-count structdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdeclor-list ((structdeclors structdeclor-listp))
    :guard (structdeclor-list-unambp structdeclors)
    :returns (new-structdeclors structdeclor-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of structure declarators."
    (cond ((endp structdeclors) nil)
          (t (cons (simpadd0-structdeclor (car structdeclors))
                   (simpadd0-structdeclor-list (cdr structdeclors)))))
    :measure (structdeclor-list-count structdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumspec ((enumspec enumspecp))
    :guard (enumspec-unambp enumspec)
    :returns (new-enumspec enumspecp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an enumeration specifier."
    (b* (((enumspec enumspec) enumspec))
      (make-enumspec
       :name enumspec.name
       :list (simpadd0-enumer-list enumspec.list)
       :final-comma enumspec.final-comma))
    :measure (enumspec-count enumspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumer ((enumer enumerp))
    :guard (enumer-unambp enumer)
    :returns (new-enumer enumerp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an enumerator."
    (b* (((enumer enumer) enumer))
      (make-enumer
       :name enumer.name
       :value (simpadd0-const-expr-option enumer.value)))
    :measure (enumer-count enumer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumer-list ((enumers enumer-listp))
    :guard (enumer-list-unambp enumers)
    :returns (new-enumers enumer-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of enumerators."
    (cond ((endp enumers) nil)
          (t (cons (simpadd0-enumer (car enumers))
                   (simpadd0-enumer-list (cdr enumers)))))
    :measure (enumer-list-count enumers))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-statassert ((statassert statassertp))
    :guard (statassert-unambp statassert)
    :returns (new-statassert statassertp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an static assertion declaration."
    (b* (((statassert statassert) statassert))
      (make-statassert
       :test (simpadd0-const-expr statassert.test)
       :message statassert.message))
    :measure (statassert-count statassert))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initdeclor ((initdeclor initdeclorp))
    :guard (initdeclor-unambp initdeclor)
    :returns (new-initdeclor initdeclorp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer declarator."
    (b* (((initdeclor initdeclor) initdeclor))
      (make-initdeclor
       :declor (simpadd0-declor initdeclor.declor)
       :asm? initdeclor.asm?
       :attribs initdeclor.attribs
       :init? (simpadd0-initer-option initdeclor.init?)))
    :measure (initdeclor-count initdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initdeclor-list ((initdeclors initdeclor-listp))
    :guard (initdeclor-list-unambp initdeclors)
    :returns (new-initdeclors initdeclor-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of initializer declarators."
    (cond ((endp initdeclors) nil)
          (t (cons (simpadd0-initdeclor (car initdeclors))
                   (simpadd0-initdeclor-list (cdr initdeclors)))))
    :measure (initdeclor-list-count initdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl ((decl declp))
    :guard (decl-unambp decl)
    :returns (new-decl declp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declaration."
    (decl-case
     decl
     :decl (make-decl-decl
            :extension decl.extension
            :specs (simpadd0-decl-spec-list decl.specs)
            :init (simpadd0-initdeclor-list decl.init))
     :statassert (decl-statassert
                  (simpadd0-statassert decl.unwrap)))
    :measure (decl-count decl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl-list ((decls decl-listp))
    :guard (decl-list-unambp decls)
    :returns (new-decls decl-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of declarations."
    (cond ((endp decls) nil)
          (t (cons (simpadd0-decl (car decls))
                   (simpadd0-decl-list (cdr decls)))))
    :measure (decl-list-count decls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-label ((label labelp))
    :guard (label-unambp label)
    :returns (new-label labelp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a label."
    (label-case
     label
     :name (label-fix label)
     :casexpr (make-label-casexpr
               :expr (simpadd0-const-expr label.expr)
               :range? (simpadd0-const-expr-option label.range?))
     :default (label-fix label))
    :measure (label-count label))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-stmt ((stmt stmtp))
    :guard (stmt-unambp stmt)
    :returns (new-stmt stmtp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a statement."
    (stmt-case
     stmt
     :labeled (make-stmt-labeled
               :label (simpadd0-label stmt.label)
               :stmt (simpadd0-stmt stmt.stmt))
     :compound (stmt-compound (simpadd0-block-item-list stmt.items))
     :expr (stmt-expr (simpadd0-expr-option stmt.expr?))
     :if (make-stmt-if
          :test (simpadd0-expr stmt.test)
          :then (simpadd0-stmt stmt.then))
     :ifelse (make-stmt-ifelse
              :test (simpadd0-expr stmt.test)
              :then (simpadd0-stmt stmt.then)
              :else (simpadd0-stmt stmt.else))
     :switch (make-stmt-switch
              :target (simpadd0-expr stmt.target)
              :body (simpadd0-stmt stmt.body))
     :while (make-stmt-while
             :test (simpadd0-expr stmt.test)
             :body (simpadd0-stmt stmt.body))
     :dowhile (make-stmt-dowhile
               :body (simpadd0-stmt stmt.body)
               :test (simpadd0-expr stmt.test))
     :for-expr (make-stmt-for-expr
                :init (simpadd0-expr-option stmt.init)
                :test (simpadd0-expr-option stmt.test)
                :next (simpadd0-expr-option stmt.next)
                :body (simpadd0-stmt stmt.body))
     :for-decl (make-stmt-for-decl
                :init (simpadd0-decl stmt.init)
                :test (simpadd0-expr-option stmt.test)
                :next (simpadd0-expr-option stmt.next)
                :body (simpadd0-stmt stmt.body))
     :for-ambig (prog2$ (impossible) (irr-stmt))
     :goto (stmt-fix stmt)
     :continue (stmt-fix stmt)
     :break (stmt-fix stmt)
     :return (stmt-return (simpadd0-expr-option stmt.expr?))
     :asm (stmt-fix stmt))
    :measure (stmt-count stmt))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-block-item ((item block-itemp))
    :guard (block-item-unambp item)
    :returns (new-item block-itemp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a block item."
    (block-item-case
     item
     :decl (block-item-decl (simpadd0-decl item.unwrap))
     :stmt (block-item-stmt (simpadd0-stmt item.unwrap))
     :ambig (prog2$ (impossible) (irr-block-item)))
    :measure (block-item-count item))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-block-item-list ((items block-item-listp))
    :guard (block-item-list-unambp items)
    :returns (new-items block-item-listp)
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of block items."
    (cond ((endp items) nil)
          (t (cons (simpadd0-block-item (car items))
                   (simpadd0-block-item-list (cdr items)))))
    :measure (block-item-list-count items))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :verify-guards :after-returns

  ///

  (local (in-theory (enable irr-absdeclor
                            irr-dirabsdeclor)))

  (fty::deffixequiv-mutual simpadd0-exprs/decls/stmts)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual exprs/decls-unambp-of-simpadd0-exprs/decls
    (defret expr-unambp-of-simpadd0-expr
      (expr-unambp new-expr)
      :fn simpadd0-expr)
    (defret expr-list-unambp-of-simpadd0-expr-list
      (expr-list-unambp new-exprs)
      :fn simpadd0-expr-list)
    (defret expr-option-unambp-of-simpadd0-expr-option
      (expr-option-unambp new-expr?)
      :fn simpadd0-expr-option)
    (defret const-expr-unambp-of-simpadd0-const-expr
      (const-expr-unambp new-cexpr)
      :fn simpadd0-const-expr)
    (defret const-expr-option-unambp-of-simpadd0-const-expr-option
      (const-expr-option-unambp new-cexpr?)
      :fn simpadd0-const-expr-option)
    (defret genassoc-unambp-of-simpadd0-genassoc
      (genassoc-unambp new-genassoc)
      :fn simpadd0-genassoc)
    (defret genassoc-list-unambp-of-simpadd0-genassoc-list
      (genassoc-list-unambp new-genassocs)
      :fn simpadd0-genassoc-list)
    (defret member-designor-unambp-of-simpadd0-member-designor
      (member-designor-unambp new-memdes)
      :fn simpadd0-member-designor)
    (defret type-spec-unambp-of-simpadd0-type-spec
      (type-spec-unambp new-tyspec)
      :fn simpadd0-type-spec)
    (defret spec/qual-unambp-of-simpadd0-spec/qual
      (spec/qual-unambp new-specqual)
      :fn simpadd0-spec/qual)
    (defret spec/qual-list-unambp-of-simpadd0-spec/qual-list
      (spec/qual-list-unambp new-specquals)
      :fn simpadd0-spec/qual-list)
    (defret align-spec-unambp-of-simpadd0-align-spec
      (align-spec-unambp new-alignspec)
      :fn simpadd0-align-spec)
    (defret decl-spec-unambp-of-simpadd0-decl-spec
      (decl-spec-unambp new-declspec)
      :fn simpadd0-decl-spec)
    (defret decl-spec-list-unambp-of-simpadd0-decl-spec-list
      (decl-spec-list-unambp new-declspecs)
      :fn simpadd0-decl-spec-list)
    (defret initer-unambp-of-simpadd0-initer
      (initer-unambp new-initer)
      :fn simpadd0-initer)
    (defret initer-option-unambp-of-simpadd0-initer-option
      (initer-option-unambp new-initer?)
      :fn simpadd0-initer-option)
    (defret desiniter-unambp-of-simpadd0-desiniter
      (desiniter-unambp new-desiniter)
      :fn simpadd0-desiniter)
    (defret desiniter-list-unambp-of-simpadd0-desiniter-list
      (desiniter-list-unambp new-desiniters)
      :fn simpadd0-desiniter-list)
    (defret designor-unambp-of-simpadd0-designor
      (designor-unambp new-designor)
      :fn simpadd0-designor)
    (defret designor-list-unambp-of-simpadd0-designor-list
      (designor-list-unambp new-designors)
      :fn simpadd0-designor-list)
    (defret declor-unambp-of-simpadd0-declor
      (declor-unambp new-declor)
      :fn simpadd0-declor)
    (defret declor-option-unambp-of-simpadd0-declor-option
      (declor-option-unambp new-declor?)
      :fn simpadd0-declor-option)
    (defret dirdeclor-unambp-of-simpadd0-dirdeclor
      (dirdeclor-unambp new-dirdeclor)
      :fn simpadd0-dirdeclor)
    (defret absdeclor-unambp-of-simpadd0-absdeclor
      (absdeclor-unambp new-absdeclor)
      :fn simpadd0-absdeclor)
    (defret absdeclor-option-unambp-of-simpadd0-absdeclor-option
      (absdeclor-option-unambp new-absdeclor?)
      :fn simpadd0-absdeclor-option)
    (defret dirabsdeclor-unambp-of-simpadd0-dirabsdeclor
      (dirabsdeclor-unambp new-dirabsdeclor)
      :fn simpadd0-dirabsdeclor)
    (defret dirabsdeclor-option-unambp-of-simpadd0-dirabsdeclor-option
      (dirabsdeclor-option-unambp new-dirabsdeclor?)
      :fn simpadd0-dirabsdeclor-option)
    (defret paramdecl-unambp-of-simpadd0-paramdecl
      (paramdecl-unambp new-paramdecl)
      :fn simpadd0-paramdecl)
    (defret paramdecl-list-unambp-of-simpadd0-paramdecl-list
      (paramdecl-list-unambp new-paramdecls)
      :fn simpadd0-paramdecl-list)
    (defret paramdeclor-unambp-of-simpadd0-paramdeclor
      (paramdeclor-unambp new-paramdeclor)
      :fn simpadd0-paramdeclor)
    (defret tyname-unambp-of-simpadd0-tyname
      (tyname-unambp new-tyname)
      :fn simpadd0-tyname)
    (defret strunispec-unambp-of-simpadd0-strunispec
      (strunispec-unambp new-strunispec)
      :fn simpadd0-strunispec)
    (defret structdecl-unambp-of-simpadd0-structdecl
      (structdecl-unambp new-structdecl)
      :fn simpadd0-structdecl)
    (defret structdecl-list-unambp-of-simpadd0-structdecl-list
      (structdecl-list-unambp new-structdecls)
      :fn simpadd0-structdecl-list)
    (defret structdeclor-unambp-of-simpadd0-structdeclor
      (structdeclor-unambp new-structdeclor)
      :fn simpadd0-structdeclor)
    (defret structdeclor-list-unambp-of-simpadd0-structdeclor-list
      (structdeclor-list-unambp new-structdeclors)
      :fn simpadd0-structdeclor-list)
    (defret enumspec-unambp-of-simpadd0-enumspec
      (enumspec-unambp new-enumspec)
      :fn simpadd0-enumspec)
    (defret enumer-unambp-of-simpadd0-enumer
      (enumer-unambp new-enumer)
      :fn simpadd0-enumer)
    (defret enumer-list-unambp-of-simpadd0-enumer-list
      (enumer-list-unambp new-enumers)
      :fn simpadd0-enumer-list)
    (defret statassert-unambp-of-simpadd0-statassert
      (statassert-unambp new-statassert)
      :fn simpadd0-statassert)
    (defret initdeclor-unambp-of-simpadd0-initdeclor
      (initdeclor-unambp new-initdeclor)
      :fn simpadd0-initdeclor)
    (defret initdeclor-list-unambp-of-simpadd0-initdeclor-list
      (initdeclor-list-unambp new-initdeclors)
      :fn simpadd0-initdeclor-list)
    (defret decl-unambp-of-simpadd0-decl
      (decl-unambp new-decl)
      :fn simpadd0-decl)
    (defret decl-list-unambp-of-simpadd0-decl-list
      (decl-list-unambp new-decls)
      :fn simpadd0-decl-list)
    (defret label-unambp-of-simpadd0-label
      (label-unambp new-label)
      :fn simpadd0-label)
    (defret stmt-unambp-of-simpadd0-stmt
      (stmt-unambp new-stmt)
      :fn simpadd0-stmt)
    (defret block-item-unambp-of-simpadd0-block-item
      (block-item-unambp new-item)
      :fn simpadd0-block-item)
    (defret block-item-list-unambp-of-simpadd0-block-item-list
      (block-item-list-unambp new-items)
      :fn simpadd0-block-item-list)
    :hints (("Goal" :in-theory (enable simpadd0-expr
                                       simpadd0-expr-list
                                       simpadd0-expr-option
                                       simpadd0-const-expr
                                       simpadd0-const-expr-option
                                       simpadd0-genassoc
                                       simpadd0-genassoc-list
                                       simpadd0-type-spec
                                       simpadd0-spec/qual
                                       simpadd0-spec/qual-list
                                       simpadd0-align-spec
                                       simpadd0-decl-spec
                                       simpadd0-decl-spec-list
                                       simpadd0-initer
                                       simpadd0-initer-option
                                       simpadd0-desiniter
                                       simpadd0-desiniter-list
                                       simpadd0-designor
                                       simpadd0-designor-list
                                       simpadd0-declor
                                       simpadd0-declor-option
                                       simpadd0-dirdeclor
                                       simpadd0-absdeclor
                                       simpadd0-absdeclor-option
                                       simpadd0-dirabsdeclor
                                       simpadd0-dirabsdeclor-option
                                       simpadd0-paramdecl
                                       simpadd0-paramdecl-list
                                       simpadd0-paramdeclor
                                       simpadd0-tyname
                                       simpadd0-strunispec
                                       simpadd0-structdecl
                                       simpadd0-structdecl-list
                                       simpadd0-structdeclor
                                       simpadd0-structdeclor-list
                                       simpadd0-enumspec
                                       simpadd0-enumer
                                       simpadd0-enumer-list
                                       simpadd0-statassert
                                       simpadd0-initdeclor
                                       simpadd0-initdeclor-list
                                       simpadd0-decl
                                       simpadd0-decl-list
                                       simpadd0-label
                                       simpadd0-stmt
                                       simpadd0-block-item
                                       simpadd0-block-item-list
                                       irr-expr
                                       irr-const-expr
                                       irr-align-spec
                                       irr-dirabsdeclor
                                       irr-paramdeclor
                                       irr-type-spec
                                       irr-stmt
                                       irr-block-item)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-fundef ((fundef fundefp))
  :guard (fundef-unambp fundef)
  :returns (new-fundef fundefp)
  :short "Transform a function definition."
  (b* (((fundef fundef) fundef))
    (make-fundef
     :extension fundef.extension
     :spec (simpadd0-decl-spec-list fundef.spec)
     :declor (simpadd0-declor fundef.declor)
     :asm? fundef.asm?
     :attribs fundef.attribs
     :decls (simpadd0-decl-list fundef.decls)
     :body (simpadd0-stmt fundef.body)))
  :hooks (:fix)

  ///

  (defret fundef-unambp-of-simpadd0-fundef
    (fundef-unambp new-fundef)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl ((extdecl extdeclp))
  :guard (extdecl-unambp extdecl)
  :returns (new-extdecl extdeclp)
  :short "Transform an external declaration."
  (extdecl-case
   extdecl
   :fundef (extdecl-fundef (simpadd0-fundef extdecl.unwrap))
   :decl (extdecl-decl (simpadd0-decl extdecl.unwrap))
   :empty (extdecl-empty)
   :asm (extdecl-fix extdecl))
  :hooks (:fix)

  ///

  (defret extdecl-unambp-of-simpadd0-extdecl
    (extdecl-unambp new-extdecl)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl-list ((extdecls extdecl-listp))
  :guard (extdecl-list-unambp extdecls)
  :returns (new-extdecls extdecl-listp)
  :short "Transform a list of external declarations."
  (cond ((endp extdecls) nil)
        (t (cons (simpadd0-extdecl (car extdecls))
                 (simpadd0-extdecl-list (cdr extdecls)))))
  :hooks (:fix)

  ///

  (defret extdecl-list-unambp-of-simpadd0-extdecl-list
    (extdecl-list-unambp new-extdecls)
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit ((tunit transunitp))
  :guard (transunit-unambp tunit)
  :returns (new-tunit transunitp)
  :short "Transform a translation unit."
  (b* (((transunit tunit) tunit))
    (transunit (simpadd0-extdecl-list tunit.decls)))
  :hooks (:fix)

  ///

  (defret transunit-unambp-of-simpadd0-transunit
    (transunit-unambp new-tunit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-filepath ((path filepathp))
  :returns (new-path filepathp)
  :short "Transform a file path."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only support file paths that consist of strings.
     We transform the path by interposing @('.simpadd0')
     just before the rightmost dot of the file extension, if any;
     if there is no file extension, we just add @('.simpadd0') at the end.
     So for instance a path @('path/to/file.c')
     becomes @('path/to/file.simpadd0.c').")
   (xdoc::p
    "Note that this kind of file path transformations
     supports chaining of transformations,
     e.g. @('path/to/file.xform1.xform2.xform3.c')."))
  (b* ((string (filepath->unwrap path))
       ((unless (stringp string))
        (raise "Misusage error: file path ~x0 is not a string." string)
        (filepath "irrelevant"))
       (chars (str::explode string))
       (dot-pos-in-rev (index-of #\. (rev chars)))
       ((when (not dot-pos-in-rev))
        (filepath (str::implode (append chars
                                        (str::explode ".simpadd0")))))
       (last-dot-pos (- (len chars) dot-pos-in-rev))
       (new-chars (append (take last-dot-pos chars)
                          (str::explode "simpadd0.")
                          (nthcdr last-dot-pos chars)))
       (new-string (str::implode new-chars)))
    (filepath new-string))
  :guard-hints
  (("Goal"
    :use (:instance acl2::index-of-<-len
                    (k #\.)
                    (x (rev (str::explode (filepath->unwrap path)))))
    :in-theory (e/d (nfix) (acl2::index-of-<-len))))
  :hooks (:fix)
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-filepath-transunit-map ((map filepath-transunit-mapp))
  :guard (transunit-ensemble-unambp-loop map)
  :returns (new-map filepath-transunit-mapp
                    :hyp (filepath-transunit-mapp map))
  :short "Transform a map from file paths to translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform both the file paths and the translation units."))
  (b* (((when (omap::emptyp map)) nil)
       ((mv path tunit) (omap::head map))
       (new-path (simpadd0-filepath path))
       (new-tunit (simpadd0-transunit tunit))
       (new-map (simpadd0-filepath-transunit-map (omap::tail map))))
    (omap::update new-path new-tunit new-map))
  :verify-guards :after-returns

  ///

  (defret transunit-ensemble-unambp-loop-of-simpadd-filepath-transunit-map
    (transunit-ensemble-unambp-loop new-map)
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit-ensemble ((tunits transunit-ensemblep))
  :guard (transunit-ensemble-unambp tunits)
  :returns (new-tunits transunit-ensemblep)
  :short "Transform a translation unit ensemble."
  (b* (((transunit-ensemble tunits) tunits))
    (transunit-ensemble (simpadd0-filepath-transunit-map tunits.unwrap)))
  :hooks (:fix)

  ///

  (defret transunit-ensemble-unambp-of-simpadd0-transunit-ensemble
    (transunit-ensemble-unambp new-tunits)))
