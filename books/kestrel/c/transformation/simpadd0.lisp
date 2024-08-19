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

(defines simpadd0-exprs/decls
  :short "Transform expressions, declarations, and related artifacts."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr ((expr exprp))
    :returns (new-expr exprp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform an expression."
    (expr-case
     expr
     :ident (expr-fix expr)
     :const (expr-fix expr)
     :string (expr-fix expr)
     :paren (expr-paren (simpadd0-expr expr.unwrap))
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
     :sizeof-ambig (prog2$
                    (raise "Misusage error: ~x0." (expr-fix expr))
                    (expr-fix expr))
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
            :then (simpadd0-expr expr.then)
            :else (simpadd0-expr expr.else))
     :comma (make-expr-comma
             :first (simpadd0-expr expr.first)
             :next (simpadd0-expr expr.next))
     :cast/call-ambig (prog2$
                       (raise "Misusage error: ~x0." (expr-fix expr))
                       (expr-fix expr))
     :cast/mul-ambig (prog2$
                      (raise "Misusage error: ~x0." (expr-fix expr))
                      (expr-fix expr))
     :cast/add-ambig (prog2$
                      (raise "Misusage error: ~x0." (expr-fix expr))
                      (expr-fix expr))
     :cast/sub-ambig (prog2$
                      (raise "Misusage error: ~x0." (expr-fix expr))
                      (expr-fix expr))
     :cast/and-ambig (prog2$
                      (raise "Misusage error: ~x0." (expr-fix expr))
                      (expr-fix expr)))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr-list ((exprs expr-listp))
    :returns (new-exprs expr-listp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a list of expressions."
    (cond ((endp exprs) nil)
          (t (cons (simpadd0-expr (car exprs))
                   (simpadd0-expr-list (cdr exprs)))))
    :measure (expr-list-count exprs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr-option ((expr? expr-optionp))
    :returns (new-expr? expr-optionp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform an optional expression."
    (expr-option-case
     expr?
     :some (simpadd0-expr expr?.val)
     :none nil)
    :measure (expr-option-count expr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-const-expr ((cexpr const-exprp))
    :returns (new-cexpr const-exprp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a constant expression."
    (const-expr (simpadd0-expr (const-expr->unwrap cexpr)))
    :measure (const-expr-count cexpr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-const-expr-option ((const-expr? const-expr-optionp))
    :returns (new-const-expr? const-expr-optionp)
    :parents (simpadd0 simpadd0-const-exprs/decls)
    :short "Transform an optional constant expression."
    (const-expr-option-case
     const-expr?
     :some (simpadd0-const-expr const-expr?.val)
     :none nil)
    :measure (const-expr-option-count const-expr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-genassoc ((genassoc genassocp))
    :returns (new-genassoc genassocp)
    :parents (simpadd0 simpadd0-exprs/decls)
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
    :returns (new-genassocs genassoc-listp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a list of generic associations."
    (cond ((endp genassocs) nil)
          (t (cons (simpadd0-genassoc (car genassocs))
                   (simpadd0-genassoc-list (cdr genassocs)))))
    :measure (genassoc-list-count genassocs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-type-spec ((tyspec type-specp))
    :returns (new-tyspec type-specp)
    :parents (simpadd0 simpadd0-exprs/decls)
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
     :struct (type-spec-struct (simpadd0-strunispec tyspec.unwrap))
     :union (type-spec-union (simpadd0-strunispec tyspec.unwrap))
     :enum (type-spec-enum (simpadd0-enumspec tyspec.unwrap))
     :typedef (type-spec-fix tyspec))
    :measure (type-spec-count tyspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-spec/qual ((specqual spec/qual-p))
    :returns (new-specqual spec/qual-p)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a type specifier or qualifier."
    (spec/qual-case
     specqual
     :tyspec (spec/qual-tyspec (simpadd0-type-spec specqual.unwrap))
     :tyqual (spec/qual-fix specqual)
     :align (spec/qual-align (simpadd0-align-spec specqual.unwrap)))
    :measure (spec/qual-count specqual))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-spec/qual-list ((specquals spec/qual-listp))
    :returns (new-specquals spec/qual-listp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a list of type specifiers and qualifiers."
    (cond ((endp specquals) nil)
          (t (cons (simpadd0-spec/qual (car specquals))
                   (simpadd0-spec/qual-list (cdr specquals)))))
    :measure (spec/qual-list-count specquals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-align-spec ((alignspec align-specp))
    :returns (new-alignspec align-specp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform an alignment specifier."
    (align-spec-case
     alignspec
     :alignas-type (align-spec-alignas-type (simpadd0-tyname alignspec.type))
     :alignas-expr (align-spec-alignas-expr (simpadd0-const-expr alignspec.arg))
     :alignas-ambig (prog2$
                     (raise "Misusage error: ~x0." (align-spec-fix alignspec))
                     (align-spec-fix alignspec)))
    :measure (align-spec-count alignspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declspec ((declspec declspecp))
    :returns (new-declspec declspecp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a declaration specifier."
    (declspec-case
     declspec
     :stocla (declspec-fix declspec)
     :tyspec (declspec-tyspec (simpadd0-type-spec declspec.unwrap))
     :tyqual (declspec-fix declspec)
     :funspec (declspec-fix declspec)
     :align (declspec-align (simpadd0-align-spec declspec.unwrap)))
    :measure (declspec-count declspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declspec-list ((declspecs declspec-listp))
    :returns (new-declspecs declspec-listp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a list of declaration specifiers."
    (cond ((endp declspecs) nil)
          (t (cons (simpadd0-declspec (car declspecs))
                   (simpadd0-declspec-list (cdr declspecs)))))
    :measure (declspec-list-count declspecs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initer ((initer initerp))
    :returns (new-initer initerp)
    :parents (simpadd0 simpadd0-exprs/decls)
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
    :returns (new-initer? initer-optionp)
    :parents (simpadd0 simpadd0-initers/decls)
    :short "Transform an optional initializer."
    (initer-option-case
     initer?
     :some (simpadd0-initer initer?.val)
     :none nil)
    :measure (initer-option-count initer?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-desiniter ((desiniter desiniterp))
    :returns (new-desiniter desiniterp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform an initializer with optional designations."
    (b* (((desiniter desiniter) desiniter))
      (make-desiniter
       :design (simpadd0-designor-list desiniter.design)
       :init (simpadd0-initer desiniter.init)))
    :measure (desiniter-count desiniter))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-desiniter-list ((desiniters desiniter-listp))
    :returns (new-desiniters desiniter-listp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a list of initializers with optional designations."
    (cond ((endp desiniters) nil)
          (t (cons (simpadd0-desiniter (car desiniters))
                   (simpadd0-desiniter-list (cdr desiniters)))))
    :measure (desiniter-list-count desiniters))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-designor ((designor designorp))
    :returns (new-designor designorp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a designator."
    (designor-case
     designor
     :sub (designor-sub (simpadd0-const-expr designor.index))
     :dot (designor-fix designor))
    :measure (designor-count designor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-designor-list ((designors designor-listp))
    :returns (new-designors designor-listp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a list of designators."
    (cond ((endp designors) nil)
          (t (cons (simpadd0-designor (car designors))
                   (simpadd0-designor-list (cdr designors)))))
    :measure (designor-list-count designors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declor ((declor declorp))
    :returns (new-declor declorp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a declarator."
    (b* (((declor declor) declor))
      (make-declor
       :pointers declor.pointers
       :decl (simpadd0-dirdeclor declor.decl)))
    :measure (declor-count declor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declor-option ((declor? declor-optionp))
    :returns (new-declor? declor-optionp)
    :parents (simpadd0 simpadd0-declors/decls)
    :short "Transform an optional declarator."
    (declor-option-case
     declor?
     :some (simpadd0-declor declor?.val)
     :none nil)
    :measure (declor-option-count declor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirdeclor ((dirdeclor dirdeclorp))
    :returns (new-dirdeclor dirdeclorp)
    :parents (simpadd0 simpadd0-exprs/decls)
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
    :returns (new-absdeclor absdeclorp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform an abstract declarator."
    (b* (((absdeclor absdeclor) absdeclor))
      (make-absdeclor
       :pointers absdeclor.pointers
       :decl? (simpadd0-dirabsdeclor-option absdeclor.decl?)))
    :measure (absdeclor-count absdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-absdeclor-option ((absdeclor? absdeclor-optionp))
    :returns (new-absdeclor? absdeclor-optionp)
    :parents (simpadd0 simpadd0-absdeclors/decls)
    :short "Transform an optional abstract declarator."
    (absdeclor-option-case
     absdeclor?
     :some (simpadd0-absdeclor absdeclor?.val)
     :none nil)
    :measure (absdeclor-option-count absdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirabsdeclor ((dirabsdeclor dirabsdeclorp))
    :returns (new-dirabsdeclor dirabsdeclorp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a direct abstract declarator."
    (dirabsdeclor-case
     dirabsdeclor
     :dummy-base (prog2$
                  (raise "Misusage error: ~x0." (dirabsdeclor-fix dirabsdeclor))
                  (dirabsdeclor-fix dirabsdeclor))
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
    :returns (new-dirabsdeclor? dirabsdeclor-optionp)
    :parents (simpadd0 simpadd0-dirabsdeclors/decls)
    :short "Transform an optional direct abstract declarator."
    (dirabsdeclor-option-case
     dirabsdeclor?
     :some (simpadd0-dirabsdeclor dirabsdeclor?.val)
     :none nil)
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-paramdecl ((paramdecl paramdeclp))
    :returns (new-paramdecl paramdeclp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a parameter declaration."
    (b* (((paramdecl paramdecl) paramdecl))
      (make-paramdecl :spec (simpadd0-declspec-list paramdecl.spec)
                      :decl (simpadd0-paramdeclor paramdecl.decl)))
    :measure (paramdecl-count paramdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-paramdecl-list ((paramdecls paramdecl-listp))
    :returns (new-paramdecls paramdecl-listp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a list of parameter declarations."
    (cond ((endp paramdecls) nil)
          (t (cons (simpadd0-paramdecl (car paramdecls))
                   (simpadd0-paramdecl-list (cdr paramdecls)))))
    :measure (paramdecl-list-count paramdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-paramdeclor ((paramdeclor paramdeclorp))
    :returns (new-paramdeclor paramdeclorp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a parameter declarator."
    (paramdeclor-case
     paramdeclor
     :declor (paramdeclor-declor (simpadd0-declor paramdeclor.unwrap))
     :absdeclor (paramdeclor-absdeclor (simpadd0-absdeclor paramdeclor.unwrap))
     :none (paramdeclor-none)
     :ambig (prog2$
             (raise "Misusage error: ~x0." (paramdeclor-fix paramdeclor))
             (paramdeclor-fix paramdeclor)))
    :measure (paramdeclor-count paramdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-tyname ((tyname tynamep))
    :returns (new-tyname tynamep)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a type name."
    (b* (((tyname tyname) tyname))
      (make-tyname
       :specqual (simpadd0-spec/qual-list tyname.specqual)
       :decl? (simpadd0-absdeclor-option tyname.decl?)))
    :measure (tyname-count tyname))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-strunispec ((strunispec strunispecp))
    :returns (new-strunispec strunispecp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a structure or union specifier."
    (b* (((strunispec strunispec) strunispec))
      (make-strunispec
       :name strunispec.name
       :members (simpadd0-structdecl-list strunispec.members)))
    :measure (strunispec-count strunispec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdecl ((structdecl structdeclp))
    :returns (new-structdecl structdeclp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a structure declaration."
    (structdecl-case
     structdecl
     :member (make-structdecl-member
              :extension structdecl.extension
              :specqual (simpadd0-spec/qual-list structdecl.specqual)
              :declor (simpadd0-structdeclor-list structdecl.declor)
              :attrib structdecl.attrib)
     :statassert (structdecl-statassert
                  (simpadd0-statassert structdecl.unwrap)))
    :measure (structdecl-count structdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdecl-list ((structdecls structdecl-listp))
    :returns (new-structdecls structdecl-listp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a list of structure declarations."
    (cond ((endp structdecls) nil)
          (t (cons (simpadd0-structdecl (car structdecls))
                   (simpadd0-structdecl-list (cdr structdecls)))))
    :measure (structdecl-list-count structdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdeclor ((structdeclor structdeclorp))
    :returns (new-structdeclor structdeclorp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a structure declarator."
    (b* (((structdeclor structdeclor) structdeclor))
      (make-structdeclor
       :declor? (simpadd0-declor-option structdeclor.declor?)
       :expr? (simpadd0-const-expr-option structdeclor.expr?)))
    :measure (structdeclor-count structdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdeclor-list ((structdeclors structdeclor-listp))
    :returns (new-structdeclors structdeclor-listp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a list of structure declarators."
    (cond ((endp structdeclors) nil)
          (t (cons (simpadd0-structdeclor (car structdeclors))
                   (simpadd0-structdeclor-list (cdr structdeclors)))))
    :measure (structdeclor-list-count structdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumspec ((enumspec enumspecp))
    :returns (new-enumspec enumspecp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform an enumeration specifier."
    (b* (((enumspec enumspec) enumspec))
      (make-enumspec
       :name enumspec.name
       :list (simpadd0-enumer-list enumspec.list)
       :final-comma enumspec.final-comma))
    :measure (enumspec-count enumspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumer ((enumer enumerp))
    :returns (new-enumer enumerp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform an enumerator."
    (b* (((enumer enumer) enumer))
      (make-enumer
       :name enumer.name
       :value (simpadd0-const-expr-option enumer.value)))
    :measure (enumer-count enumer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumer-list ((enumers enumer-listp))
    :returns (new-enumers enumer-listp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform a list of enumerators."
    (cond ((endp enumers) nil)
          (t (cons (simpadd0-enumer (car enumers))
                   (simpadd0-enumer-list (cdr enumers)))))
    :measure (enumer-list-count enumers))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-statassert ((statassert statassertp))
    :returns (new-statassert statassertp)
    :parents (simpadd0 simpadd0-exprs/decls)
    :short "Transform an static assertion declaration."
    (b* (((statassert statassert) statassert))
      (make-statassert
       :test (simpadd0-const-expr statassert.test)
       :message statassert.message))
    :measure (statassert-count statassert))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 :hints (("Goal" :in-theory (enable o< o-finp)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards simpadd0-expr)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual simpadd0-exprs/decls))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-initdeclor ((initdeclor initdeclorp))
  :returns (new-initdeclor initdeclorp)
  :short "Transform an initializer declarator."
  (b* (((initdeclor initdeclor) initdeclor))
    (make-initdeclor
     :declor (simpadd0-declor initdeclor.declor)
     :init? (simpadd0-initer-option initdeclor.init?)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-initdeclor-list ((initdeclors initdeclor-listp))
  :returns (new-initdeclors initdeclor-listp)
  :short "Transform a list of initializer declarators."
  (cond ((endp initdeclors) nil)
        (t (cons (simpadd0-initdeclor (car initdeclors))
                 (simpadd0-initdeclor-list (cdr initdeclors)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-decl ((decl declp))
  :returns (new-decl declp)
  :short "Transform a declaration."
  (decl-case
   decl
   :decl (make-decl-decl
          :extension decl.extension
          :specs (simpadd0-declspec-list decl.specs)
          :init (simpadd0-initdeclor-list decl.init)
          :asm? decl.asm?
          :attrib decl.attrib)
   :statassert (decl-statassert
                (simpadd0-statassert decl.unwrap)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-decl-list ((decls decl-listp))
  :returns (new-decls decl-listp)
  :short "Transform a list of declarations."
  (cond ((endp decls) nil)
        (t (cons (simpadd0-decl (car decls))
                 (simpadd0-decl-list (cdr decls)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-label ((label labelp))
  :returns (new-label labelp)
  :short "Transform a label."
  (label-case
   label
   :name (label-fix label)
   :const (label-const (simpadd0-const-expr label.unwrap))
   :default (label-fix label))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines simpadd0-stmts/blocks
  :short "Transform statements, blocks, and related entities."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-stmt ((stmt stmtp))
    :returns (new-stmt stmtp)
    :parents (simpadd0 simpadd0-stmts/blocks)
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
     :for-ambig (prog2$
                 (raise "Misusage error: ~x0." (stmt-fix stmt))
                 (stmt-fix stmt))
     :goto (stmt-fix stmt)
     :continue (stmt-fix stmt)
     :break (stmt-fix stmt)
     :return (stmt-return (simpadd0-expr-option stmt.expr?)))
    :measure (stmt-count stmt))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-block-item ((item block-itemp))
    :returns (new-item block-itemp)
    :parents (simpadd0 simpadd0-stmts/blocks)
    :short "Transform a block item."
    (block-item-case
     item
     :decl (block-item-decl (simpadd0-decl item.unwrap))
     :stmt (block-item-stmt (simpadd0-stmt item.unwrap))
     :ambig (prog2$
             (raise "Misusage error: ~x0." (block-item-fix item))
             (block-item-fix item)))
    :measure (block-item-count item))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-block-item-list ((items block-item-listp))
    :returns (new-items block-item-listp)
    :parents (simpadd0 simpadd0-stmts/blocks)
    :short "Transform a list of block items."
    (cond ((endp items) nil)
          (t (cons (simpadd0-block-item (car items))
                   (simpadd0-block-item-list (cdr items)))))
    :measure (block-item-list-count items))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o< o-finp)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards simpadd0-stmt)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual simpadd0-stmts/blocks))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-fundef ((fundef fundefp))
  :returns (new-fundef fundefp)
  :short "Transform a function definition."
  (b* (((fundef fundef) fundef))
    (make-fundef
     :extension fundef.extension
     :spec (simpadd0-declspec-list fundef.spec)
     :declor (simpadd0-declor fundef.declor)
     :decls (simpadd0-decl-list fundef.decls)
     :body (simpadd0-stmt fundef.body)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl ((extdecl extdeclp))
  :returns (new-extdecl extdeclp)
  :short "Transform an external declaration."
  (extdecl-case
   extdecl
   :fundef (extdecl-fundef (simpadd0-fundef extdecl.unwrap))
   :decl (extdecl-decl (simpadd0-decl extdecl.unwrap)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl-list ((extdecls extdecl-listp))
  :returns (new-extdecls extdecl-listp)
  :short "Transform a list of external declarations."
  (cond ((endp extdecls) nil)
        (t (cons (simpadd0-extdecl (car extdecls))
                 (simpadd0-extdecl-list (cdr extdecls)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit ((tunit transunitp))
  :returns (new-tunit transunitp)
  :short "Transform a translation unit."
  (b* (((transunit tunit) tunit))
    (transunit (simpadd0-extdecl-list tunit.decls)))
  :hooks (:fix))

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
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit-ensemble ((tunits transunit-ensemblep))
  :returns (new-tunits transunit-ensemblep)
  :short "Transform a translation unit ensemble."
  (b* (((transunit-ensemble tunits) tunits))
    (transunit-ensemble (simpadd0-filepath-transunit-map tunits.unwrap)))
  :hooks (:fix))
