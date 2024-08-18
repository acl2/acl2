; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unambiguity
  :parents (abstract-syntax)
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
     i.e. there are no ambiguous constructs.
     The definition is simple, just structural.")
   (xdoc::p
    "For now we do not make any checks on GCC extensions,
     even though they may contain expressions.
     This mirrors the treatment in the @(see disambiguator):
     the reason for this (temporary) limitation is explained there."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines exprs/decls-unambp
  :short "Check if expressions, declarations, and related entities
          are unambiguous."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define expr-unambp ((expr exprp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an expression is unambiguous."
    (expr-case expr
               :ident t
               :const t
               :string t
               :paren (expr-unambp expr.unwrap)
               :gensel (and (expr-unambp expr.control)
                            (genassoc-list-unambp expr.assoc))
               :arrsub (and (expr-unambp expr.arg1)
                            (expr-unambp expr.arg2))
               :funcall (and (expr-unambp expr.fun)
                             (expr-list-unambp expr.args))
               :member (expr-unambp expr.arg)
               :memberp (expr-unambp expr.arg)
               :complit (and (tyname-unambp expr.type)
                             (desiniter-list-unambp expr.elems))
               :unary (expr-unambp expr.arg)
               :sizeof (tyname-unambp expr.type)
               :sizeof-ambig nil
               :alignof (tyname-unambp expr.type)
               :cast (and (tyname-unambp expr.type)
                          (expr-unambp expr.arg))
               :binary (and (expr-unambp expr.arg1)
                            (expr-unambp expr.arg2))
               :cond (and (expr-unambp expr.test)
                          (expr-unambp expr.then)
                          (expr-unambp expr.else))
               :comma (and (expr-unambp expr.first)
                           (expr-unambp expr.next))
               :cast/call-ambig nil
               :cast/mul-ambig nil
               :cast/add-ambig nil
               :cast/sub-ambig nil
               :cast/and-ambig nil)
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define expr-list-unambp ((exprs expr-listp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a list of expressions is unambiguous."
    (or (endp exprs)
        (and (expr-unambp (car exprs))
             (expr-list-unambp (cdr exprs))))
    :measure (expr-list-count exprs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define expr-option-unambp ((expr? expr-optionp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an optaional expression is unambiguous."
    (expr-option-case expr?
                      :some (expr-unambp expr?.val)
                      :none t)
    :measure (expr-option-count expr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define const-expr-unambp ((cexpr const-exprp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a constant expression is unambiguous."
    (expr-unambp (const-expr->unwrap cexpr))
    :measure (const-expr-count cexpr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define const-expr-option-unambp ((cexpr? const-expr-optionp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an optional constant expression is unambiguous."
    (const-expr-option-case cexpr?
                            :some (const-expr-unambp cexpr?.val)
                            :none t)
    :measure (const-expr-option-count cexpr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define genassoc-unambp ((assoc genassocp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a generic association is unambiguous."
    (genassoc-case assoc
                   :type (and (tyname-unambp assoc.type)
                              (expr-unambp assoc.expr))
                   :default (expr-unambp assoc.expr))
    :measure (genassoc-count assoc))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define genassoc-list-unambp ((assocs genassoc-listp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a list of generic associations is unambiguous."
    (or (endp assocs)
        (and (genassoc-unambp (car assocs))
             (genassoc-list-unambp (cdr assocs))))
    :measure (genassoc-list-count assocs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-spec-unambp ((tyspec type-specp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a type specifier is unambiguous."
    (type-spec-case tyspec
                    :void t
                    :char t
                    :short t
                    :int t
                    :long t
                    :float t
                    :double t
                    :signed t
                    :unsigned t
                    :bool t
                    :complex t
                    :atomic (tyname-unambp tyspec.type)
                    :struct (strunispec-unambp tyspec.unwrap)
                    :union (strunispec-unambp tyspec.unwrap)
                    :enum (enumspec-unambp tyspec.unwrap)
                    :typedef t)
    :measure (type-spec-count tyspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define spec/qual-unambp ((specqual spec/qual-p))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a specifier or qualifier is unambiguous."
    (spec/qual-case specqual
                    :tyspec (type-spec-unambp specqual.unwrap)
                    :tyqual t
                    :align (align-spec-unambp specqual.unwrap))
    :measure (spec/qual-count specqual))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define spec/qual-list-unambp ((specquals spec/qual-listp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a list of specifiers and qualifiers is unambiguous."
    (or (endp specquals)
        (and (spec/qual-unambp (car specquals))
             (spec/qual-list-unambp (cdr specquals))))
    :measure (spec/qual-list-count specquals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define align-spec-unambp ((alignspec align-specp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an alignment specifier is unambiguous."
    (align-spec-case alignspec
                     :alignas-type (tyname-unambp alignspec.type)
                     :alignas-expr (const-expr-unambp alignspec.arg)
                     :alignas-ambig nil)
    :measure (align-spec-count alignspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define declspec-unambp ((declspec declspecp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a declaration specifier is unambiguous."
    (declspec-case declspec
                   :stocla t
                   :tyspec (type-spec-unambp declspec.unwrap)
                   :tyqual t
                   :funspec t
                   :align (align-spec-unambp declspec.unwrap))
    :measure (declspec-count declspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define declspec-list-unambp ((declspecs declspec-listp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a list of declaration specifiers is unambiguous."
    (or (endp declspecs)
        (and (declspec-unambp (car declspecs))
             (declspec-list-unambp (cdr declspecs))))
    :measure (declspec-list-count declspecs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define initer-unambp ((initer initerp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an initializer is unambiguous."
    (initer-case initer
                 :single (expr-unambp initer.expr)
                 :list (desiniter-list-unambp initer.elems))
    :measure (initer-count initer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define initer-option-unambp ((initer? initer-optionp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an optional initializer is unambiguous."
    (initer-option-case initer?
                        :some (initer-unambp initer?.val)
                        :none t)
    :measure (initer-option-count initer?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define desiniter-unambp ((desiniter desiniterp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an initializer with optional designations is unambiguous."
    (and (designor-list-unambp (desiniter->design desiniter))
         (initer-unambp (desiniter->init desiniter)))
    :measure (desiniter-count desiniter))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define desiniter-list-unambp ((desiniters desiniter-listp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a list of initialziers with optional designations
            is unambiguous."
    (or (endp desiniters)
        (and (desiniter-unambp (car desiniters))
             (desiniter-list-unambp (cdr desiniters))))
    :measure (desiniter-list-count desiniters))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define designor-unambp ((designor designorp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a designator is unambiguous."
    (designor-case designor
                   :sub (const-expr-unambp designor.index)
                   :dot t)
    :measure (designor-count designor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define designor-list-unambp ((designors designor-listp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a list of designators is unambiguous."
    (or (endp designors)
        (and (designor-unambp (car designors))
             (designor-list-unambp (cdr designors))))
    :measure (designor-list-count designors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define declor-unambp ((declor declorp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a declarator is unambiguous."
    (dirdeclor-unambp (declor->decl declor))
    :measure (declor-count declor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define declor-option-unambp ((declor? declor-optionp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an optional declarator is unambiguous."
    (declor-option-case declor?
                        :some (declor-unambp declor?.val)
                        :none t)
    :measure (declor-option-count declor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define dirdeclor-unambp ((dirdeclor dirdeclorp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a direct declarator is unambiguous."
    (dirdeclor-case
     dirdeclor
     :ident t
     :paren (declor-unambp dirdeclor.unwrap)
     :array (and (dirdeclor-unambp dirdeclor.decl)
                 (expr-option-unambp dirdeclor.expr?))
     :array-static1 (and (dirdeclor-unambp dirdeclor.decl)
                         (expr-unambp dirdeclor.expr))
     :array-static2 (and (dirdeclor-unambp dirdeclor.decl)
                         (expr-unambp dirdeclor.expr))
     :array-star (dirdeclor-unambp dirdeclor.decl)
     :function-params (and (dirdeclor-unambp dirdeclor.decl)
                           (paramdecl-list-unambp dirdeclor.params))
     :function-names (dirdeclor-unambp dirdeclor.decl))
    :measure (dirdeclor-count dirdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define absdeclor-unambp ((absdeclor absdeclorp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an abstract declarator is unambiguous."
    (dirabsdeclor-option-unambp (absdeclor->decl? absdeclor))
    :measure (absdeclor-count absdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define absdeclor-option-unambp ((absdeclor? absdeclor-optionp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an optional abstract declarator is unambiguous."
    (absdeclor-option-case absdeclor?
                           :some (absdeclor-unambp absdeclor?.val)
                           :none t)
    :measure (absdeclor-option-count absdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define dirabsdeclor-unambp ((dirabsdeclor dirabsdeclorp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a direct abstract declarator is unambiguous."
    :long
    (xdoc::topstring
     (xdoc::p
      "Although the dummy base case is not an ambiguous construct,
       we have a good opportunity to exclude it here."))
    (dirabsdeclor-case
     dirabsdeclor
     :dummy-base nil
     :paren (absdeclor-unambp dirabsdeclor.unwrap)
     :array (and (dirabsdeclor-option-unambp dirabsdeclor.decl?)
                 (expr-option-unambp dirabsdeclor.expr?))
     :array-static1 (and (dirabsdeclor-option-unambp dirabsdeclor.decl?)
                         (expr-unambp dirabsdeclor.expr))
     :array-static2 (and (dirabsdeclor-option-unambp dirabsdeclor.decl?)
                         (expr-unambp dirabsdeclor.expr))
     :array-star (dirabsdeclor-option-unambp dirabsdeclor.decl?)
     :function (and (dirabsdeclor-option-unambp dirabsdeclor.decl?)
                    (paramdecl-list-unambp dirabsdeclor.params)))
    :measure (dirabsdeclor-count dirabsdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define dirabsdeclor-option-unambp ((dirabsdeclor? dirabsdeclor-optionp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an optional direct abstract declarator is unambiguous."
    (dirabsdeclor-option-case dirabsdeclor?
                              :some (dirabsdeclor-unambp dirabsdeclor?.val)
                              :none t)
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define paramdecl-unambp ((paramdecl paramdeclp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a parameter declaration is unambiguous."
    (and (declspec-list-unambp (paramdecl->spec paramdecl))
         (paramdeclor-unambp (paramdecl->decl paramdecl)))
    :measure (paramdecl-count paramdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define paramdecl-list-unambp ((paramdecls paramdecl-listp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a list parameter declarations is unambiguous."
    (or (endp paramdecls)
        (and (paramdecl-unambp (car paramdecls))
             (paramdecl-list-unambp (cdr paramdecls))))
    :measure (paramdecl-list-count paramdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define paramdeclor-unambp ((paramdeclor paramdeclorp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a parameter declarator is unambiguous."
    (paramdeclor-case paramdeclor
                      :declor (declor-unambp paramdeclor.unwrap)
                      :absdeclor (absdeclor-unambp paramdeclor.unwrap)
                      :none t
                      :ambig nil)
    :measure (paramdeclor-count paramdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define tyname-unambp ((tyname tynamep))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a type name is unambiguous."
    (and (spec/qual-list-unambp (tyname->specqual tyname))
         (absdeclor-option-unambp (tyname->decl? tyname)))
    :measure (tyname-count tyname))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define strunispec-unambp ((strunispec strunispecp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a structure or union specifier is unambiguous."
    (structdecl-list-unambp (strunispec->members strunispec))
    :measure (strunispec-count strunispec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define structdecl-unambp ((structdecl structdeclp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a structure declaration is unambiguous."
    (structdecl-case structdecl
                     :member (and (spec/qual-list-unambp structdecl.specqual)
                                  (structdeclor-list-unambp structdecl.declor))
                     :statassert (statassert-unambp structdecl.unwrap))
    :measure (structdecl-count structdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define structdecl-list-unambp ((structdecls structdecl-listp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a list of structure declarations is unambiguous."
    (or (endp structdecls)
        (and (structdecl-unambp (car structdecls))
             (structdecl-list-unambp (cdr structdecls))))
    :measure (structdecl-list-count structdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define structdeclor-unambp ((structdeclor structdeclorp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a structure declarator is unambiguous."
    (and (declor-option-unambp (structdeclor->declor? structdeclor))
         (const-expr-option-unambp (structdeclor->expr? structdeclor)))
    :measure (structdeclor-count structdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define structdeclor-list-unambp ((structdeclors structdeclor-listp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a list of structure declarators is unambiguous."
    (or (endp structdeclors)
        (and (structdeclor-unambp (car structdeclors))
             (structdeclor-list-unambp (cdr structdeclors))))
    :measure (structdeclor-list-count structdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define enumspec-unambp ((enumspec enumspecp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an enumeration specifier is unambiguous."
    (enumer-list-unambp (enumspec->list enumspec))
    :measure (enumspec-count enumspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define enumer-unambp ((enumer enumerp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if an enumerator is unambiguous."
    (const-expr-option-unambp (enumer->value enumer))
    :measure (enumer-count enumer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define enumer-list-unambp ((enumers enumer-listp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a list of enumerators is unambiguous."
    (or (endp enumers)
        (and (enumer-unambp (car enumers))
             (enumer-list-unambp (cdr enumers))))
    :measure (enumer-list-count enumers))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define statassert-unambp ((statassert statassertp))
    :returns (yes/no booleanp)
    :parents (unambiguity expr-unambps/decls)
    :short "Check if a static assertion declaration is unambiguous."
    (const-expr-unambp (statassert->test statassert))
    :measure (statassert-count statassert))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o< o-finp)))

  ///

  (fty::deffixequiv-mutual exprs/decls-unambp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (std::deflist expr-list-unambp (x)
    :guard (expr-listp x)
    :parents nil
    (expr-unambp x))

  (std::deflist genassoc-list-unambp (x)
    :guard (genassoc-listp x)
    :parents nil
    (genassoc-unambp x))

  (std::deflist spec/qual-list-unambp (x)
    :guard (spec/qual-listp x)
    :parents nil
    (spec/qual-unambp x))

  (std::deflist declspec-list-unambp (x)
    :guard (declspec-listp x)
    :parents nil
    (declspec-unambp x))

  (std::deflist desiniter-list-unambp (x)
    :guard (desiniter-listp x)
    :parents nil
    (desiniter-unambp x))

  (std::deflist designor-list-unambp (x)
    :guard (designor-listp x)
    :parents nil
    (designor-unambp x))

  (std::deflist paramdecl-list-unambp (x)
    :guard (paramdecl-listp x)
    :parents nil
    (paramdecl-unambp x))

  (std::deflist structdecl-list-unambp (x)
    :guard (structdecl-listp x)
    :parents nil
    (structdecl-unambp x))

  (std::deflist structdeclor-list-unambp (x)
    :guard (structdeclor-listp x)
    :parents nil
    (structdeclor-unambp x))

  (std::deflist enumer-list-unambp (x)
    :guard (enumer-listp x)
    :parents nil
    (enumer-unambp x))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

  ;;;;;;;;;;;;;;;;;;;;

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

  ;;;;;;;;;;;;;;;;;;;;

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

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defrule expr-unambp-of-expr-paren->unwrap
    (implies (and (expr-unambp expr)
                  (expr-case expr :paren))
             (expr-unambp (expr-paren->unwrap expr)))
    :expand (expr-unambp expr))

  (defrule expr-unambp-of-expr-gensel->control
    (implies (and (expr-unambp expr)
                  (expr-case expr :gensel))
             (expr-unambp (expr-gensel->control expr)))
    :expand (expr-unambp expr))

  (defrule genassoc-list-unambp-of-expr-gensel->assoc
    (implies (and (expr-unambp expr)
                  (expr-case expr :gensel))
             (genassoc-list-unambp (expr-gensel->assoc expr)))
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

  (defrule not-sizeof-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :sizeof-ambig)))
    :rule-classes :forward-chaining)

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
             (expr-unambp (expr-cond->then expr)))
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

  (defrule not-cast/call-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :cast/call-ambig)))
    :rule-classes :forward-chaining)

  (defrule not-cast/mul-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :cast/mul-ambig)))
    :rule-classes :forward-chaining)

  (defrule not-cast/add-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :cast/add-ambig)))
    :rule-classes :forward-chaining)

  (defrule not-cast/sub-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :cast/sub-ambig)))
    :rule-classes :forward-chaining)

  (defrule not-cast/and-ambig-when-expr-unambp
    (implies (expr-unambp expr)
             (not (equal (expr-kind expr) :cast/and-ambig)))
    :rule-classes :forward-chaining)

  (defrule expr-unambp-of-expr-const-expr->unwrap
    (implies (const-expr-unambp cexpr)
             (expr-unambp (const-expr->unwrap cexpr)))
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

  (defrule tyname-unambp-of-type-spec-atomic->type
    (implies (and (type-spec-unambp tyspec)
                  (type-spec-case tyspec :atomic))
             (tyname-unambp (type-spec-atomic->type tyspec)))
    :expand (type-spec-unambp tyspec))

  (defrule strunispec-unambp-of-type-spec-struct->unwrap
    (implies (and (type-spec-unambp tyspec)
                  (type-spec-case tyspec :struct))
             (strunispec-unambp (type-spec-struct->unwrap tyspec)))
    :expand (type-spec-unambp tyspec))

  (defrule strunispec-unambp-of-type-spec-union->unwrap
    (implies (and (type-spec-unambp tyspec)
                  (type-spec-case tyspec :union))
             (strunispec-unambp (type-spec-union->unwrap tyspec)))
    :expand (type-spec-unambp tyspec))

  (defrule enumspec-unambp-of-type-spec-enum->unwrap
    (implies (and (type-spec-unambp tyspec)
                  (type-spec-case tyspec :enum))
             (enumspec-unambp (type-spec-enum->unwrap tyspec)))
    :expand (type-spec-unambp tyspec))

  (defrule type-spec-unambp-of-spec/qual-tyspec->unwrap
    (implies (and (spec/qual-unambp specqual)
                  (spec/qual-case specqual :tyspec))
             (type-spec-unambp (spec/qual-tyspec->unwrap specqual)))
    :expand (spec/qual-unambp specqual))

  (defrule align-spec-unambp-of-spec/qual-align->unwrap
    (implies (and (spec/qual-unambp specqual)
                  (spec/qual-case specqual :align))
             (align-spec-unambp (spec/qual-align->unwrap specqual)))
    :expand (spec/qual-unambp specqual))

  (defrule tyname-unambp-of-align-spec-alignas-type->type
    (implies (and (align-spec-unambp alignspec)
                  (align-spec-case alignspec :alignas-type))
             (tyname-unambp (align-spec-alignas-type->type alignspec)))
    :expand (align-spec-unambp alignspec))

  (defrule const-expr-unambp-of-align-spec-alignas-expr->arg
    (implies (and (align-spec-unambp alignspec)
                  (align-spec-case alignspec :alignas-expr))
             (const-expr-unambp (align-spec-alignas-expr->arg alignspec)))
    :expand (align-spec-unambp alignspec))

  (defrule not-alignas-ambig-when-align-spec-unambp
    (implies (align-spec-unambp alignspec)
             (not (equal (align-spec-kind alignspec) :alignas-ambig)))
    :rule-classes :forward-chaining
    :expand (align-spec-unambp alignspec))

  (defrule type-spec-unambp-of-declspec-tyspec->unwrap
    (implies (and (declspec-unambp declspec)
                  (declspec-case declspec :tyspec))
             (type-spec-unambp (declspec-tyspec->unwrap declspec)))
    :expand (declspec-unambp declspec))

  (defrule align-spec-unambp-of-declspec-align->unwrap
    (implies (and (declspec-unambp declspec)
                  (declspec-case declspec :align))
             (align-spec-unambp (declspec-align->unwrap declspec)))
    :expand (declspec-unambp declspec))

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

  (defrule designor-list-unambp-of-desiniter->design
    (implies (desiniter-unambp desiniter)
             (designor-list-unambp (desiniter->design desiniter)))
    :expand (desiniter-unambp desiniter))

  (defrule initer-unambp-of-desiniter->init
    (implies (desiniter-unambp desiniter)
             (initer-unambp (desiniter->init desiniter)))
    :expand (desiniter-unambp desiniter))

  (defrule const-expr-unambp-of-designor-sub->index
    (implies (and (designor-unambp designor)
                  (designor-case designor :sub))
             (const-expr-unambp (designor-sub->index designor)))
    :expand (designor-unambp designor))

  (defrule dirdeclor-unambp-of-declor->decl
    (implies (declor-unambp declor)
             (dirdeclor-unambp (declor->decl declor)))
    :expand (declor-unambp declor))

  (defrule declor-unambp-of-dirdeclor-paren->unwrap
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :paren))
             (declor-unambp (dirdeclor-paren->unwrap dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-array->decl
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array))
             (dirdeclor-unambp (dirdeclor-array->decl dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule expr-option-unambp-of-dirdeclor-array->expr?
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array))
             (expr-option-unambp (dirdeclor-array->expr? dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-array-static1->decl
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array-static1))
             (dirdeclor-unambp (dirdeclor-array-static1->decl dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule expr-unambp-of-dirdeclor-array-static1->expr
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array-static1))
             (expr-unambp (dirdeclor-array-static1->expr dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-array-static2->decl
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array-static2))
             (dirdeclor-unambp (dirdeclor-array-static2->decl dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule expr-unambp-of-dirdeclor-array-static2->expr
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array-static2))
             (expr-unambp (dirdeclor-array-static2->expr dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-array-star->decl
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :array-star))
             (dirdeclor-unambp (dirdeclor-array-star->decl dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-function-params->decl
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :function-params))
             (dirdeclor-unambp (dirdeclor-function-params->decl dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule paramdecl-list-unambp-of-dirdeclor-function-params->params
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :function-params))
             (paramdecl-list-unambp
              (dirdeclor-function-params->params dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirdeclor-unambp-of-dirdeclor-function-names->decl
    (implies (and (dirdeclor-unambp dirdeclor)
                  (dirdeclor-case dirdeclor :function-names))
             (dirdeclor-unambp (dirdeclor-function-names->decl dirdeclor)))
    :expand (dirdeclor-unambp dirdeclor))

  (defrule dirabsdeclor-option-unambp-of-absdeclor->decl?
    (implies (absdeclor-unambp absdeclor)
             (dirabsdeclor-option-unambp (absdeclor->decl? absdeclor)))
    :expand (absdeclor-unambp absdeclor))

  (defrule absdeclor-unambp-of-dirabsdeclor-paren->unwrap
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :paren))
             (absdeclor-unambp (dirabsdeclor-paren->unwrap dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule dirabsdeclor-option-unambp-of-dirabsdeclor-array->decl?
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array))
             (dirabsdeclor-option-unambp
              (dirabsdeclor-array->decl? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule expr-option-unambp-of-dirabsdeclor-array->expr?
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array))
             (expr-option-unambp (dirabsdeclor-array->expr? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-array-static1->decl
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array-static1))
             (dirabsdeclor-option-unambp
              (dirabsdeclor-array-static1->decl? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule expr-unambp-of-dirabsdeclor-array-static1->expr
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array-static1))
             (expr-unambp (dirabsdeclor-array-static1->expr dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-array-static2->decl?
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array-static2))
             (dirabsdeclor-option-unambp
              (dirabsdeclor-array-static2->decl? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule expr-unambp-of-dirabsdeclor-array-static2->expr
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array-static2))
             (expr-unambp (dirabsdeclor-array-static2->expr dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-array-star->decl?
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :array-star))
             (dirabsdeclor-option-unambp
              (dirabsdeclor-array-star->decl? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule dirabsdeclor-unambp-of-dirabsdeclor-function->decl?
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :function))
             (dirabsdeclor-option-unambp
              (dirabsdeclor-function->decl? dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule paramdecl-list-unambp-of-dirabsdeclor-function->params
    (implies (and (dirabsdeclor-unambp dirabsdeclor)
                  (dirabsdeclor-case dirabsdeclor :function))
             (paramdecl-list-unambp
              (dirabsdeclor-function->params dirabsdeclor)))
    :expand (dirabsdeclor-unambp dirabsdeclor))

  (defrule declspec-list-unambp-of-paramdecl->spec
    (implies (paramdecl-unambp paramdecl)
             (declspec-list-unambp (paramdecl->spec paramdecl)))
    :expand (paramdecl-unambp paramdecl))

  (defrule paramdeclor-unambp-of-paramdecl->decl
    (implies (paramdecl-unambp paramdecl)
             (paramdeclor-unambp (paramdecl->decl paramdecl)))
    :expand (paramdecl-unambp paramdecl))

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

  (defrule not-ambig-when-paramdeclor-unambp
    (implies (paramdeclor-unambp paramdeclor)
             (not (equal (paramdeclor-kind paramdeclor) :ambig)))
    :rule-classes :forward-chaining
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
    :expand (statassert-unambp statassert)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr/tyname-unambp ((expr/tyname expr/tyname-p))
  :returns (yes/no booleanp)
  :short "Check if an expression or type name is unambiguous."
  :long
  (xdoc::topstring
   (xdoc::p
    "This fixtype does not appear in the abstract syntax trees,
     but it is the result of @(tsee dimb-amb-expr/tyname),
     so we need to define this predicate to state and prove, by induction,
     that the disambiguator returns unambiguous abstract syntax."))
  (expr/tyname-case expr/tyname
                    :expr (expr-unambp expr/tyname.unwrap)
                    :tyname (tyname-unambp expr/tyname.unwrap))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define declor/absdeclor-unambp ((declor/absdeclor declor/absdeclor-p))
  :returns (yes/no booleanp)
  :short "Check if a declarator or abstract declarator is unambiguous."
  :long
  (xdoc::topstring
   (xdoc::p
    "The purpose of this predicate is similar to @(tsee expr/tyname-unambp):
     see its documentation."))
  (declor/absdeclor-case declor/absdeclor
                         :declor (declor-unambp declor/absdeclor.unwrap)
                         :absdeclor (absdeclor-unambp declor/absdeclor.unwrap))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initdeclor-unambp ((initdeclor initdeclorp))
  :returns (yes/no booleanp)
  :short "Check if an initializer declarator is unambiguous."
  (and (declor-unambp (initdeclor->declor initdeclor))
       (initer-option-unambp (initdeclor->init? initdeclor)))
  :hooks (:fix)

  ///

  (defrule declor-unambp-of-initdeclor->declor
    (implies (initdeclor-unambp initdeclor)
             (declor-unambp (initdeclor->declor initdeclor))))

  (defrule initer-option-unambp-of-initdeclor->init?
    (implies (initdeclor-unambp initdeclor)
             (initer-option-unambp (initdeclor->init? initdeclor)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist initdeclor-list-unambp (x)
  :guard (initdeclor-listp x)
  :short "Check if a list of initializer declarators is unambiguous."
  (initdeclor-unambp x)
  ///
  (fty::deffixequiv initdeclor-list-unambp
    :args ((x initdeclor-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl-unambp ((decl declp))
  :returns (yes/no booleanp)
  :short "Check if a declaration is unambiguous."
  (decl-case decl
             :decl (and (declspec-list-unambp decl.specs)
                        (initdeclor-list-unambp decl.init))
             :statassert (statassert-unambp decl.unwrap))
  :hooks (:fix)

  ///

  (defrule declspec-list-unambp-of-decl-decl->specs
    (implies (and (decl-unambp decl)
                  (decl-case decl :decl))
             (declspec-list-unambp (decl-decl->specs decl))))

  (defrule initdeclor-list-unambp-of-decl-decl->init
    (implies (and (decl-unambp decl)
                  (decl-case decl :decl))
             (initdeclor-list-unambp (decl-decl->init decl))))

  (defrule statassert-unambp-of-decl-statassert->unwrap
    (implies (and (decl-unambp decl)
                  (decl-case decl :statassert))
             (statassert-unambp (decl-statassert->unwrap decl)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist decl-list-unambp (x)
  :guard (decl-listp x)
  :short "Check if a list of declarations is unambiguous."
  (decl-unambp x)
  ///
  (fty::deffixequiv decl-list-unambp
    :args ((x decl-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define label-unambp ((label labelp))
  :returns (yes/no booleanp)
  :short "Check if a label is unambiguous."
  (label-case label
              :name t
              :const (const-expr-unambp label.unwrap)
              :default t)
  :hooks (:fix)

  ///

  (defrule const-expr-unambp-of-label-const->unwrap
    (implies (and (label-unambp label)
                  (label-case label :const))
             (const-expr-unambp (label-const->unwrap label)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl/stmt-unambp ((decl/stmt decl/stmt-p))
  :returns (yes/no booleanp)
  :short "Check if a declaration or statement is unambiguous."
  :long
  (xdoc::topstring
   (xdoc::p
    "The purpose of this predicate is similar to @(tsee expr/tyname-unambp):
     see its documentation."))
  (decl/stmt-case decl/stmt
                  :decl (decl-unambp decl/stmt.unwrap)
                  :stmt (expr-unambp decl/stmt.unwrap))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines stmts/blocks-unambp
  :short "Check if statements, blocks, and related entities."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define stmt-unambp ((stmt stmtp))
    :returns (yes/no booleanp)
    :parents (unambiguity stmts/blocks-unambp)
    :short "Check if a statement is unambiguous."
    (stmt-case stmt
               :labeled (and (label-unambp stmt.label)
                             (stmt-unambp stmt.stmt))
               :compound (block-item-list-unambp stmt.items)
               :expr (expr-option-unambp stmt.expr?)
               :if (and (expr-unambp stmt.test)
                        (stmt-unambp stmt.then))
               :ifelse (and (expr-unambp stmt.test)
                            (stmt-unambp stmt.then)
                            (stmt-unambp stmt.else))
               :switch (and (expr-unambp stmt.target)
                            (stmt-unambp stmt.body))
               :while (and (expr-unambp stmt.test)
                           (stmt-unambp stmt.body))
               :dowhile (and (stmt-unambp stmt.body)
                             (expr-unambp stmt.test))
               :for-expr (and (expr-option-unambp stmt.init)
                              (expr-option-unambp stmt.test)
                              (expr-option-unambp stmt.next)
                              (stmt-unambp stmt.body))
               :for-decl (and (decl-unambp stmt.init)
                              (expr-option-unambp stmt.test)
                              (expr-option-unambp stmt.next)
                              (stmt-unambp stmt.body))
               :for-ambig nil
               :goto t
               :continue t
               :break t
               :return (expr-option-unambp stmt.expr?))
    :measure (stmt-count stmt))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define block-item-unambp ((item block-itemp))
    :returns (yes/no booleanp)
    :parents (unambiguity stmts/blocks-unambp)
    :short "Check if a block item is unambiguous."
    (block-item-case item
                     :decl (decl-unambp item.unwrap)
                     :stmt (stmt-unambp item.unwrap)
                     :ambig nil)
    :measure (block-item-count item))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define block-item-list-unambp ((items block-item-listp))
    :returns (yes/no booleanp)
    :parents (unambiguity stmts/blocks-unambp)
    :short "Check if a list of block items is unambiguous."
    (or (endp items)
        (and (block-item-unambp (car items))
             (block-item-list-unambp (cdr items))))
    :measure (block-item-list-count items))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o< o-finp)))

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (std::deflist block-item-list-unambp (x)
    :guard (block-item-listp x)
    :parents nil
    (block-item-unambp x))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

  (defrule not-for-ambig-when-stmt-unambp
    (implies (stmt-unambp stmt)
             (not (equal (stmt-kind stmt) :for-ambig)))
    :rule-classes :forward-chaining
    :expand (stmt-unambp stmt))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

  (defrule not-ambig-when-block-item-unambp
    (implies (block-item-unambp item)
             (not (equal (block-item-kind item) :ambig)))
    :rule-classes :forward-chaining
    :expand (block-item-unambp item))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual stmts/blocks-unambp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-unambp ((fundef fundefp))
  :returns (yes/no booleanp)
  :short "Check if a function definition is unambiguous."
  (and (declspec-list-unambp (fundef->spec fundef))
       (declor-unambp (fundef->declor fundef))
       (decl-list-unambp (fundef->decls fundef))
       (stmt-unambp (fundef->body fundef)))
  :hooks (:fix)

  ///

  (defrule declspec-list-unambp-of-fundef->spec
    (implies (fundef-unambp fundef)
             (declspec-list-unambp (fundef->spec fundef))))

  (defrule declor-unambp-of-fundef->declor
    (implies (fundef-unambp fundef)
             (declor-unambp (fundef->declor fundef))))

  (defrule decl-list-unambp-of-fundef->decls
    (implies (fundef-unambp fundef)
             (decl-list-unambp (fundef->decls fundef))))

  (defrule stmt-unambp-of-fundef->body
    (implies (fundef-unambp fundef)
             (stmt-unambp (fundef->body fundef)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extdecl-unambp ((edecl extdeclp))
  :returns (yes/no booleanp)
  :short "Check if an external declaration is unambiguous."
  (extdecl-case edecl
                :fundef (fundef-unambp edecl.unwrap)
                :decl (decl-unambp edecl.unwrap))
  :hooks (:fix)

  ///

  (defrule fundef-unambp-of-extdecl-fundef->unwrap
    (implies (and (extdecl-unambp edecl)
                  (extdecl-case edecl :fundef))
             (fundef-unambp (extdecl-fundef->unwrap edecl))))

  (defrule decl-unambp-of-extdecl-decl->unwrap
    (implies (and (extdecl-unambp edecl)
                  (extdecl-case edecl :decl))
             (decl-unambp (extdecl-decl->unwrap edecl)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist extdecl-list-unambp (x)
  :guard (extdecl-listp x)
  :short "Check if a list of external declarations is unambiguous."
  (extdecl-unambp x)
  ///
  (fty::deffixequiv extdecl-list-unambp
    :args ((x extdecl-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-unambp ((tunit transunitp))
  :returns (yes/no booleanp)
  :short "Check if a translation unit is unambiguous."
  (extdecl-list-unambp (transunit->decls tunit))
  :hooks (:fix)

  ///

  (defrule transunit-unambp-of-transunit
    (equal (transunit-unambp (transunit edecls))
           (extdecl-list-unambp edecls)))

  (defrule extdecl-list-unambp-of-transunit->decls
    (implies (transunit-unambp tunit)
             (extdecl-list-unambp (transunit->decls tunit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-ensemble-unambp ((tunits transunit-ensemblep))
  :returns (yes/no booleanp)
  :short "Check if a translation unit ensemble is unambiguous."
  (transunit-ensemble-unambp-loop (transunit-ensemble->unwrap tunits))
  :hooks (:fix)

  :prepwork

  ((define transunit-ensemble-unambp-loop ((map filepath-transunit-mapp))
     :returns (yes/no booleanp)
     :parents nil
     (or (omap::emptyp map)
         (and (transunit-unambp (omap::head-val map))
              (transunit-ensemble-unambp-loop (omap::tail map))))

     ///

     (defrule transunit-ensemble-unambp-loop-of-empty
       (implies (omap::emptyp tumap)
                (transunit-ensemble-unambp-loop tumap)))

     (defrule transunit-ensemble-unambp-loop-of-update
       (implies (and (transunit-unambp tunit)
                     (transunit-ensemble-unambp-loop tumap))
                (transunit-ensemble-unambp-loop (omap::update path
                                                              tunit
                                                              tumap)))
       :induct t
       :enable (omap::update
                omap::emptyp
                omap::mfix
                omap::mapp
                omap::head
                omap::tail))

     (defrule transunit-unambp-of-head-when-transunit-ensemble-unambp-loop
       (implies (and (transunit-ensemble-unambp-loop tumap)
                     (not (omap::emptyp tumap)))
                (transunit-unambp (mv-nth 1 (omap::head tumap)))))

     (defrule transunit-ensemble-unambp-loop-of-tail
       (implies (transunit-ensemble-unambp-loop tumap)
                (transunit-ensemble-unambp-loop (omap::tail tumap))))))

  ///

  (defrule transunit-ensemble-unambp-of-transunit-ensemble
    (equal (transunit-ensemble-unambp (transunit-ensemble tumap))
           (transunit-ensemble-unambp-loop (filepath-transunit-map-fix tumap))))

  (defrule transunit-ensemble-unambp-loop-of-transunit-ensemble->unwrap
    (implies (transunit-ensemble-unambp tunits)
             (transunit-ensemble-unambp-loop
              (transunit-ensemble->unwrap tunits)))))
