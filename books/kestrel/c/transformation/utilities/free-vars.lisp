; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
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

(include-book "../../syntax/abstract-syntax-operations")

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
      "This returns a set of all ordinary identifiers used as variables within
       the AST, excluding those variables which have first been declared,
       i.e. in a statement declaration or as a function parameter.")
    (xdoc::p
      "Note that ordinary identifiers do not include label names, the tags of
       structure, union, and enumeration type names, or the members of
       structures or unions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: add tests beyond its use in the split-fn transformation

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines free-vars-exprs/decls/stmts
  (define free-vars-expr
    ((expr exprp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an expression."
    :returns (free-vars ident-setp)
    (expr-case
     expr
     :ident (if (in expr.ident bound-vars)
                nil
              (insert expr.ident nil))
     :const nil
     :string nil
     :paren (free-vars-expr expr.inner bound-vars)
     :gensel (union (free-vars-expr expr.control bound-vars)
                    (free-vars-genassoc-list expr.assocs bound-vars))
     :arrsub (union (free-vars-expr expr.arg1 bound-vars)
                    (free-vars-expr expr.arg2 bound-vars))
     :funcall (union (free-vars-expr expr.fun bound-vars)
                     (free-vars-expr-list expr.args bound-vars))
     :member (free-vars-expr expr.arg bound-vars)
     :memberp (free-vars-expr expr.arg bound-vars)
     :complit (free-vars-desiniter-list expr.elems bound-vars)
     :unary (free-vars-expr expr.arg bound-vars)
     :sizeof (free-vars-tyname expr.type bound-vars)
     :alignof (free-vars-tyname expr.type bound-vars)
     :cast (free-vars-expr expr.arg bound-vars)
     :binary (union (free-vars-expr expr.arg1 bound-vars)
                    (free-vars-expr expr.arg2 bound-vars))
     :cond (union (free-vars-expr expr.test bound-vars)
                  (union (free-vars-expr-option expr.then bound-vars)
                         (free-vars-expr expr.else bound-vars)))
     :comma (union (free-vars-expr expr.first bound-vars)
                   (free-vars-expr expr.next bound-vars))
     :stmt (b* (((mv free-vars -)
                 (free-vars-block-item-list expr.items bound-vars)))
             free-vars)
     :tycompat (union (free-vars-tyname expr.type1 bound-vars)
                      (free-vars-tyname expr.type2 bound-vars))
     :offsetof (free-vars-tyname expr.type bound-vars)
     :va-arg (union (free-vars-expr expr.list bound-vars)
                    (free-vars-tyname expr.type bound-vars))
     :extension (free-vars-expr expr.expr bound-vars)
     :sizeof-ambig (raise "Unexpected ambiguous expression")
     :cast/call-ambig (raise "Unexpected ambiguous expression")
     :cast/mul-ambig (raise "Unexpected ambiguous expression")
     :cast/add-ambig (raise "Unexpected ambiguous expression")
     :cast/sub-ambig (raise "Unexpected ambiguous expression")
     :cast/and-ambig (raise "Unexpected ambiguous expression"))
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

  (define free-vars-const-expr
    ((cexpr const-exprp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a constant expression."
    :returns (free-vars ident-setp)
    (b* (((const-expr cexpr) cexpr))
      (free-vars-expr cexpr.expr bound-vars))
    :measure (const-expr-count cexpr))

  (define free-vars-const-expr-option
    ((cexpr? const-expr-optionp)
     (bound-vars ident-setp))
    :returns (free-vars ident-setp)
    (const-expr-option-case
     cexpr?
     :some (free-vars-const-expr cexpr?.val bound-vars)
     :none nil)
    :measure (const-expr-option-count cexpr?))

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

  (define free-vars-type-spec
    ((type-spec type-specp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a type specifier."
    :returns (free-vars ident-setp)
    (type-spec-case
     type-spec
     :void nil
     :char nil
     :short nil
     :int nil
     :long nil
     :float nil
     :double nil
     :signed nil
     :unsigned nil
     :bool nil
     :complex nil
     :atomic (free-vars-tyname type-spec.type bound-vars)
     :struct (free-vars-strunispec type-spec.spec bound-vars)
     :union (free-vars-strunispec type-spec.spec bound-vars)
     :enum (free-vars-enumspec type-spec.spec bound-vars)
     :typedef (if (in type-spec.name bound-vars)
                nil
              (insert type-spec.name nil))
     :int128 nil
     :float32 nil
     :float32x nil
     :float64 nil
     :float64x nil
     :float128 nil
     :float128x nil
     :builtin-va-list nil
     :struct-empty nil
     :typeof-expr (free-vars-expr type-spec.expr bound-vars)
     :typeof-type (free-vars-tyname type-spec.type bound-vars)
     :auto-type nil
     :typeof-ambig (raise "Unexpected ambiguous expression"))
    :measure (type-spec-count type-spec))

  (define free-vars-spec/qual
    ((spec/qual spec/qual-p)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a specifier or qualifier."
    :returns (free-vars ident-setp)
    (spec/qual-case
     spec/qual
     :typespec (free-vars-type-spec spec/qual.spec bound-vars)
     :typequal nil
     :align (free-vars-align-spec spec/qual.spec bound-vars)
     :attrib (free-vars-attrib-spec spec/qual.spec bound-vars))
    :measure (spec/qual-count spec/qual))

  (define free-vars-spec/qual-list
    ((specquals spec/qual-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of specifiers or
            qualifiers."
    :returns (free-vars ident-setp)
    (if (endp specquals)
        nil
      (union (free-vars-spec/qual (first specquals) bound-vars)
             (free-vars-spec/qual-list (rest specquals) bound-vars)))
    :measure (spec/qual-list-count specquals))

  (define free-vars-align-spec
    ((align-spec align-specp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a alignment specifier."
    :returns (free-vars ident-setp)
    (align-spec-case
     align-spec
     :alignas-type (free-vars-tyname align-spec.type bound-vars)
     :alignas-expr (free-vars-const-expr align-spec.expr bound-vars)
     :alignas-ambig (raise "Unexpected ambiguous expression"))
    :measure (align-spec-count align-spec))

  (define free-vars-decl-spec
    ((decl-spec decl-specp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a declaration specifier."
    :returns (free-vars ident-setp)
    (decl-spec-case
     decl-spec
     :stoclass nil
     :typespec (free-vars-type-spec decl-spec.spec bound-vars)
     :typequal nil
     :function nil
     :align (free-vars-align-spec decl-spec.spec bound-vars)
     :attrib (free-vars-attrib-spec decl-spec.spec bound-vars)
     :stdcall nil
     ;; TODO: can a __declspec attribute ever include relevant variables?
     :declspec nil)
    :measure (decl-spec-count decl-spec))

  (define free-vars-decl-spec-list
    ((decl-specs decl-spec-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of declaration
            specifiers."
    :returns (free-vars ident-setp)
    (if (endp decl-specs)
        nil
      (union (free-vars-decl-spec (first decl-specs) bound-vars)
             (free-vars-decl-spec-list (rest decl-specs) bound-vars)))
    :measure (decl-spec-list-count decl-specs))

  (define free-vars-typequal/attribspec
    ((typequal/attribspec c$::typequal/attribspec-p)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a type qualifiers or attribute
            specifiers."
    :returns (free-vars ident-setp)
    (c$::typequal/attribspec-case
     typequal/attribspec
     :type nil
     :attrib (free-vars-attrib-spec typequal/attribspec.unwrap bound-vars))
    :measure (c$::typequal/attribspec-count typequal/attribspec))

  (define free-vars-typequal/attribspec-list
    ((typequal/attribspecs c$::typequal/attribspec-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of type qualifiers and
            attribute specifiers."
    :returns (free-vars ident-setp)
    (if (endp typequal/attribspecs)
        nil
      (union (free-vars-typequal/attribspec (first typequal/attribspecs) bound-vars)
             (free-vars-typequal/attribspec-list (rest typequal/attribspecs) bound-vars)))
    :measure (c$::typequal/attribspec-list-count typequal/attribspecs))

  (define free-vars-typequal/attribspec-list-list
    ((typequal/attribspec-lists c$::typequal/attribspec-list-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of lists of type
            qualifiers and attribute specifiers."
    :returns (free-vars ident-setp)
    (if (endp typequal/attribspec-lists)
        nil
      (union (free-vars-typequal/attribspec-list (first typequal/attribspec-lists) bound-vars)
             (free-vars-typequal/attribspec-list-list (rest typequal/attribspec-lists) bound-vars)))
    :measure (c$::typequal/attribspec-list-list-count typequal/attribspec-lists))

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
      (union (free-vars-designor-list desiniter.designors bound-vars)
             (free-vars-initer desiniter.initer bound-vars)))
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

  (define free-vars-designor
    ((designor designorp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a designator."
    :returns (free-vars ident-setp)
    (designor-case
     designor
     :sub (free-vars-const-expr designor.index bound-vars)
     :dot nil)
    :measure (designor-count designor))

  (define free-vars-designor-list
    ((designors designor-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of designators."
    :returns (free-vars ident-setp)
    (if (endp designors)
        nil
      (union (free-vars-designor (first designors) bound-vars)
             (free-vars-designor-list (rest designors) bound-vars)))
    :measure (designor-list-count designors))

  (define free-vars-declor
    ((declor declorp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a declarator."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* (((declor declor) declor)
         (free-vars0
           (free-vars-typequal/attribspec-list-list declor.pointers bound-vars))
         ((mv free-vars1 bound-vars)
          (free-vars-dirdeclor declor.direct bound-vars)))
      (mv (union free-vars0 free-vars1)
          bound-vars))
    :measure (declor-count declor))

  (define free-vars-declor-option
    ((declor? declor-optionp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an optional declarator."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (declor-option-case
     declor?
     :some (free-vars-declor declor?.val bound-vars)
     :none (mv nil (ident-set-fix bound-vars)))
    :measure (declor-option-count declor?))

  (define free-vars-dirdeclor
    ((dirdeclor dirdeclorp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a direct declarator."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (dirdeclor-case
     dirdeclor
     :ident (mv nil
                (insert dirdeclor.ident (ident-set-fix bound-vars)))
     :paren (free-vars-declor dirdeclor.inner bound-vars)
     :array
     (b* ((free-vars0
            (free-vars-typequal/attribspec-list dirdeclor.qualspecs bound-vars))
          (free-vars1
            (free-vars-expr-option dirdeclor.size? bound-vars))
          ((mv free-vars2 bound-vars)
           (free-vars-dirdeclor dirdeclor.declor bound-vars)))
       (mv (union free-vars0 (union free-vars1 free-vars2))
           bound-vars))
     :array-static1
     (b* ((free-vars0
            (free-vars-typequal/attribspec-list dirdeclor.qualspecs bound-vars))
          (free-vars1
            (free-vars-expr dirdeclor.size bound-vars))
          ((mv free-vars2 bound-vars)
           (free-vars-dirdeclor dirdeclor.declor bound-vars)))
       (mv (union free-vars0 (union free-vars1 free-vars2))
           bound-vars))
     :array-static2
     (b* ((free-vars0
            (free-vars-typequal/attribspec-list dirdeclor.qualspecs bound-vars))
          (free-vars1
            (free-vars-expr dirdeclor.size bound-vars))
          ((mv free-vars2 bound-vars)
           (free-vars-dirdeclor dirdeclor.declor bound-vars)))
       (mv (union free-vars0 (union free-vars1 free-vars2))
           bound-vars))
     :array-star
     (b* ((free-vars0
            (free-vars-typequal/attribspec-list dirdeclor.qualspecs bound-vars))
          ((mv free-vars1 bound-vars)
           (free-vars-dirdeclor dirdeclor.declor bound-vars)))
       (mv (union free-vars0 free-vars1)
           bound-vars))
     :function-params
     (b* (((mv free-vars0 bound-vars)
           (free-vars-dirdeclor dirdeclor.declor bound-vars))
          ((mv free-vars1 -)
            (free-vars-param-declon-list dirdeclor.params bound-vars)))
       (mv (union free-vars0 free-vars1)
           bound-vars))
     :function-names (free-vars-dirdeclor dirdeclor.declor bound-vars))
    :measure (dirdeclor-count dirdeclor))

  (define free-vars-absdeclor
    ((absdeclor absdeclorp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an abstract declarator."
    :returns (free-vars ident-setp)
    (b* (((absdeclor absdeclor) absdeclor))
      (union (free-vars-typequal/attribspec-list-list absdeclor.pointers bound-vars)
             (free-vars-dirabsdeclor-option absdeclor.direct? bound-vars)))
    :measure (absdeclor-count absdeclor))

  (define free-vars-absdeclor-option
    ((absdeclor? absdeclor-optionp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an optional abstract declarator."
    :returns (free-vars ident-setp)
    (absdeclor-option-case
     absdeclor?
     :some (free-vars-absdeclor absdeclor?.val bound-vars)
     :none nil)
    :measure (absdeclor-option-count absdeclor?))

  (define free-vars-dirabsdeclor
    ((dirabsdeclor dirabsdeclorp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a direct abstract declarator."
    :returns (free-vars ident-setp)
    (dirabsdeclor-case
     dirabsdeclor
     :dummy-base nil
     :paren (free-vars-absdeclor dirabsdeclor.inner bound-vars)
     :array
     (union (free-vars-dirabsdeclor-option dirabsdeclor.declor? bound-vars)
            (union (free-vars-typequal/attribspec-list dirabsdeclor.qualspecs bound-vars)
                   (free-vars-expr-option dirabsdeclor.size? bound-vars)))
     :array-static1
     (union (free-vars-dirabsdeclor-option dirabsdeclor.declor? bound-vars)
            (union (free-vars-typequal/attribspec-list dirabsdeclor.qualspecs bound-vars)
                   (free-vars-expr dirabsdeclor.size bound-vars)))
     :array-static2
     (union (free-vars-dirabsdeclor-option dirabsdeclor.declor? bound-vars)
            (union (free-vars-typequal/attribspec-list dirabsdeclor.qualspecs bound-vars)
                   (free-vars-expr dirabsdeclor.size bound-vars)))
     :array-star (free-vars-dirabsdeclor-option dirabsdeclor.declor? bound-vars)
     :function
     (b* (((mv free-vars -)
           (free-vars-param-declon-list dirabsdeclor.params bound-vars)))
       (union (free-vars-dirabsdeclor-option dirabsdeclor.declor? bound-vars)
              free-vars)))
    :measure (dirabsdeclor-count dirabsdeclor))

  (define free-vars-dirabsdeclor-option
    ((dirabsdeclor? dirabsdeclor-optionp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an optional direct abstract
            declarator."
    :returns (free-vars ident-setp)
    (dirabsdeclor-option-case
     dirabsdeclor?
     :some (free-vars-dirabsdeclor dirabsdeclor?.val bound-vars)
     :none nil)
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  (define free-vars-param-declon
    ((paramdecl param-declonp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a parameter declaration."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* (((param-declon paramdecl) paramdecl)
         (free-vars0 (free-vars-decl-spec-list paramdecl.specs bound-vars))
         ((mv free-vars1 bound-vars)
          (free-vars-param-declor paramdecl.declor bound-vars)))
      (mv (union free-vars0 free-vars1)
          bound-vars))
    :measure (param-declon-count paramdecl))

  (define free-vars-param-declon-list
    ((paramdecls param-declon-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of parameter
            declarations."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* (((when (endp paramdecls))
          (mv nil (ident-set-fix bound-vars)))
         ((mv free-vars0 bound-vars)
          (free-vars-param-declon (first paramdecls) bound-vars))
         ((mv free-vars1 bound-vars)
          (free-vars-param-declon-list (rest paramdecls) bound-vars)))
      (mv (union free-vars0 free-vars1)
          bound-vars))
    :measure (param-declon-list-count paramdecls))

  (define free-vars-param-declor
    ((paramdeclor param-declorp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of parameter
            declarations."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (param-declor-case
     paramdeclor
     :nonabstract (free-vars-declor paramdeclor.declor bound-vars)
     :abstract (mv (free-vars-absdeclor paramdeclor.declor bound-vars)
                   (ident-set-fix bound-vars))
     :none (mv nil (ident-set-fix bound-vars))
     :ambig (mv (raise "Unexpected ambiguous expression")
                (ident-set-fix bound-vars)))
    :measure (param-declor-count paramdeclor))

  (define free-vars-tyname
    ((tyname tynamep)
     (bound-vars ident-setp))
    :returns (free-vars ident-setp)
    (b* (((tyname tyname) tyname))
      (union (free-vars-spec/qual-list tyname.specquals bound-vars)
             (free-vars-absdeclor-option tyname.declor? bound-vars)))
    :measure (tyname-count tyname))

  (define free-vars-strunispec
    ((strunispec strunispecp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a structure or union
            specifier."
    :returns (free-vars ident-setp)
    (b* (((strunispec strunispec) strunispec)
         ((mv free-vars -)
          (free-vars-structdecl-list strunispec.members bound-vars)))
      ;; Note: we are only tracking *ordinary* variables, so we don't add the
      ;;   struct tag to the set of bound variables.
      free-vars)
    :measure (strunispec-count strunispec))

  (define free-vars-structdecl
    ((structdecl structdeclp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a structure declaration."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* ((bound-vars (ident-set-fix bound-vars)))
      (structdecl-case
        structdecl
        :member
        (b* ((free-vars0
               (free-vars-spec/qual-list structdecl.specqual bound-vars))
             ((mv free-vars1 bound-vars)
              (free-vars-structdeclor-list structdecl.declor bound-vars)))
          (mv (union free-vars0
                     (union free-vars1
                            (free-vars-attrib-spec-list structdecl.attrib
                                                        bound-vars)))
              bound-vars))
        :statassert (mv (free-vars-statassert structdecl.unwrap bound-vars)
                        bound-vars)
        :empty (mv nil bound-vars)))
    :measure (structdecl-count structdecl))

  (define free-vars-structdecl-list
    ((structdecls structdecl-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of structure
            declarations."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* (((when (endp structdecls))
          (mv nil (ident-set-fix bound-vars)))
         ((mv free-vars0 bound-vars)
          (free-vars-structdecl (first structdecls) bound-vars))
         ((mv free-vars1 bound-vars)
          (free-vars-structdecl-list (rest structdecls) bound-vars)))
      (mv (union free-vars0 free-vars1)
          bound-vars))
    :measure (structdecl-list-count structdecls))

  (define free-vars-structdeclor
    ((structdeclor structdeclorp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a structure declarator."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* (((structdeclor structdeclor) structdeclor)
         (free-vars0
           (free-vars-const-expr-option structdeclor.expr? bound-vars))
         ((mv free-vars1 bound-vars)
          (free-vars-declor-option structdeclor.declor? bound-vars)))
      (mv (union free-vars0 free-vars1)
          bound-vars))
    :measure (structdeclor-count structdeclor))

  (define free-vars-structdeclor-list
    ((structdeclors structdeclor-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of structure
            declarators."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* (((when (endp structdeclors))
          (mv nil (ident-set-fix bound-vars)))
         ((mv free-vars0 bound-vars)
          (free-vars-structdeclor (first structdeclors) bound-vars))
         ((mv free-vars1 bound-vars)
          (free-vars-structdeclor-list (rest structdeclors) bound-vars)))
      (mv (union free-vars0 free-vars1)
          bound-vars))
    :measure (structdeclor-list-count structdeclors))

  (define free-vars-enumspec
    ((enumspec enumspecp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a enumeration specifier."
    :returns (free-vars ident-setp)
    (b* (((enumspec enumspec) enumspec)
         ((mv free-vars -)
          (free-vars-enumer-list enumspec.list bound-vars)))
      ;; Note: we are only tracking *ordinary* variables, so we don't add the
      ;;   enum tag to the set of bound variables.
      free-vars)
    :measure (enumspec-count enumspec))

  (define free-vars-enumer
    ((enumer enumerp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a enumerator."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* ((bound-vars (ident-set-fix bound-vars))
         ((enumer enumer) enumer))
      (mv (free-vars-const-expr-option enumer.value bound-vars)
          (insert enumer.name bound-vars)))
    :measure (enumer-count enumer))

  (define free-vars-enumer-list
    ((enumers enumer-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of enumerators."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* (((when (endp enumers))
          (mv nil (ident-set-fix bound-vars)))
         ((mv free-vars0 bound-vars)
          (free-vars-enumer (first enumers) bound-vars))
         ((mv free-vars1 bound-vars)
          (free-vars-enumer-list (rest enumers) bound-vars)))
      (mv (union free-vars0 free-vars1)
          bound-vars))
    :measure (enumer-list-count enumers))

  (define free-vars-statassert
    ((statassert statassertp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a static assertion declaration."
    :returns (free-vars ident-setp)
    (b* (((statassert statassert) statassert))
      (free-vars-const-expr statassert.test bound-vars))
    :measure (statassert-count statassert))

  (define free-vars-attrib
    ((attrib c$::attribp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a GCC attribute."
    :returns (free-vars ident-setp)
    (c$::attrib-case
     attrib
     :name-only nil
     :name-param (free-vars-expr-list attrib.param bound-vars))
    :measure (c$::attrib-count attrib))

  (define free-vars-attrib-list
    ((attribs c$::attrib-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of GCC attribute."
    :returns (free-vars ident-setp)
    (if (endp attribs)
        nil
      (union (free-vars-attrib (first attribs) bound-vars)
             (free-vars-attrib-list (rest attribs) bound-vars)))
    :measure (c$::attrib-list-count attribs))

  (define free-vars-attrib-spec
    ((attrib-spec c$::attrib-specp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a GCC attribute specifier."
    :returns (free-vars ident-setp)
    (b* (((c$::attrib-spec attrib-spec) attrib-spec))
      (free-vars-attrib-list attrib-spec.attribs bound-vars))
    :measure (c$::attrib-spec-count attrib-spec))

  (define free-vars-attrib-spec-list
    ((attrib-specs c$::attrib-spec-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of GCC attribute
            specifiers."
    :returns (free-vars ident-setp)
    (if (endp attrib-specs)
        nil
      (union (free-vars-attrib-spec (first attrib-specs) bound-vars)
             (free-vars-attrib-spec-list (rest attrib-specs) bound-vars)))
    :measure (c$::attrib-spec-list-count attrib-specs))

  (define free-vars-initdeclor
    ((initdeclor initdeclorp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an initializer declarator."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* (((initdeclor initdeclor) initdeclor)
         (free-vars0 (free-vars-initer-option initdeclor.init? bound-vars))
         (free-vars1 (free-vars-attrib-spec-list initdeclor.attribs bound-vars))
         ((mv free-vars2 bound-vars)
          (free-vars-declor initdeclor.declor bound-vars)))
      (mv (union free-vars0 (union free-vars1 free-vars2))
          bound-vars))
    :measure (initdeclor-count initdeclor))

  (define free-vars-initdeclor-list
    ((initdeclors initdeclor-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of initializer
            declarators."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* (((when (endp initdeclors))
          (mv nil (ident-set-fix bound-vars)))
         ((mv free-vars0 bound-vars)
          (free-vars-initdeclor (first initdeclors) bound-vars))
         ((mv free-vars1 bound-vars)
          (free-vars-initdeclor-list (rest initdeclors) bound-vars)))
      (mv (union free-vars0 free-vars1)
          bound-vars))
    :measure (initdeclor-list-count initdeclors))

  (define free-vars-decl
    ((decl declp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a declaration."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (decl-case
     decl
     :decl (free-vars-initdeclor-list decl.init bound-vars)
     :statassert (mv (free-vars-statassert decl.unwrap bound-vars)
                     (ident-set-fix bound-vars)))
    :measure (decl-count decl))

  (define free-vars-decl-list
    ((decls decl-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of declarations."
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* (((when (endp decls))
          (mv nil (ident-set-fix bound-vars)))
         ((mv free-vars0 bound-vars)
          (free-vars-decl (first decls) bound-vars))
         ((mv free-vars1 bound-vars)
          (free-vars-decl-list (rest decls) bound-vars)))
      (mv (union free-vars0 free-vars1)
          bound-vars))
    :measure (decl-list-count decls))

  (define free-vars-label
    ((label labelp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a label."
    :returns (free-vars ident-setp)
    (label-case
     label
     :name nil
     :casexpr (union (free-vars-const-expr label.expr bound-vars)
                     (free-vars-const-expr-option label.range? bound-vars))
     :default nil)
    :measure (label-count label))

  (define free-vars-asm-output
    ((asm-output c$::asm-outputp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an assembler output operand."
    :returns (free-vars ident-setp)
    (b* (((c$::asm-output asm-output) asm-output))
      (free-vars-expr asm-output.lvalue bound-vars))
    :measure (c$::asm-output-count asm-output))

  (define free-vars-asm-output-list
    ((asm-outputs c$::asm-output-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of assembler output
            operands."
    :returns (free-vars ident-setp)
    (if (endp asm-outputs)
        nil
      (union (free-vars-asm-output (first asm-outputs) bound-vars)
             (free-vars-asm-output-list (rest asm-outputs) bound-vars)))
    :measure (c$::asm-output-list-count asm-outputs))

  (define free-vars-asm-input
    ((asm-input c$::asm-inputp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an assembler input operand."
    :returns (free-vars ident-setp)
    (b* (((c$::asm-input asm-input) asm-input))
      (free-vars-expr asm-input.rvalue bound-vars))
    :measure (c$::asm-input-count asm-input))

  (define free-vars-asm-input-list
    ((asm-inputs c$::asm-input-listp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a list of assembler input
            operands."
    :returns (free-vars ident-setp)
    (if (endp asm-inputs)
        nil
      (union (free-vars-asm-input (first asm-inputs) bound-vars)
             (free-vars-asm-input-list (rest asm-inputs) bound-vars)))
    :measure (c$::asm-input-list-count asm-inputs))

  (define free-vars-asm-stmt
    ((asm-stmt c$::asm-stmtp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in an assembler statement."
    :returns (free-vars ident-setp)
    (b* (((c$::asm-stmt asm-stmt) asm-stmt))
      (union (free-vars-asm-output-list asm-stmt.outputs bound-vars)
             (free-vars-asm-input-list asm-stmt.inputs bound-vars)))
    :measure (c$::asm-stmt-count asm-stmt))

  (define free-vars-stmt
    ((stmt stmtp)
     (bound-vars ident-setp))
    :short "Collect free variables appearing in a statement."
    :returns (free-vars ident-setp)
    (stmt-case
     stmt
     :labeled (union (free-vars-label stmt.label bound-vars)
                     (free-vars-stmt stmt.stmt bound-vars))
     :compound (b* (((mv free-vars -)
                     (free-vars-block-item-list stmt.items bound-vars)))
                 free-vars)
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
     :goto nil
     :continue nil
     :break nil
     :return (free-vars-expr-option stmt.expr? bound-vars)
     :asm (free-vars-asm-stmt stmt.unwrap bound-vars)
     :for-ambig (raise "Unexpected ambiguous expression"))
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
    :returns (mv (free-vars ident-setp)
                 (bound-vars ident-setp))
    (b* (((when (endp items))
          (mv nil (ident-set-fix bound-vars)))
         ((mv free-vars0 bound-vars)
          (free-vars-block-item (first items) bound-vars))
         ((mv free-vars1 bound-vars)
          (free-vars-block-item-list (rest items) bound-vars)))
      (mv (union free-vars0 free-vars1)
          bound-vars))
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
