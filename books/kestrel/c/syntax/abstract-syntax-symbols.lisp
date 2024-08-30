; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; List of symbols that provide an API to the abstract syntax,
; importable in a package definition.
; The list does not contain all the symbols yet; it can be extended as needed.

(defconst *abstract-syntax-symbols*
  '(

    ;; fixtypes operations:

    identp
    ident
    ident-fix
    ident->unwrap

    ident-listp

    ident-setp
    ident-set-fix

    ident-option
    ident-optionp
    ident-option-fix

    ident-option-set
    ident-option-setp
    ident-option-set-fix

    dec/oct/hex-const-case
    dec/oct/hex-const-oct

    iconst

    constp
    const-fix
    const-case
    const-int->unwrap

    type-qual-list-listp

    exprp
    expr-fix
    expr-count
    expr-case
    expr-ident
    expr-const
    expr-const->unwrap
    expr-paren
    make-expr-gensel
    make-expr-arrsub
    make-expr-funcall
    make-expr-member
    make-expr-memberp
    make-expr-complit
    make-expr-unary
    expr-sizeof
    expr-alignof
    make-expr-alignof
    make-expr-cast
    make-expr-binary
    make-expr-cond
    make-expr-comma
    irr-expr

    expr-listp
    expr-list-fix
    expr-list-count

    expr-optionp
    expr-option-fix
    expr-option-count
    expr-option-case

    const-exprp
    const-expr-count
    const-expr
    const-expr->unwrap
    irr-const-expr

    const-expr-optionp
    const-expr-option-fix
    const-expr-option-count
    const-expr-option-case

    genassocp
    genassoc-fix
    genassoc-count
    genassoc-case
    make-genassoc-type
    genassoc-default

    genassoc-listp
    genassoc-list-fix
    genassoc-list-count

    type-specp
    type-spec-fix
    type-spec-count
    type-spec-case
    type-spec-atomic
    type-spec-struct
    type-spec-union
    type-spec-enum
    make-type-spec-typeof-expr
    make-type-spec-typeof-type
    irr-type-spec

    spec/qual-p
    spec/qual-fix
    spec/qual-count
    spec/qual-case
    spec/qual-tyspec
    spec/qual-align
    spec/qual-attrib

    spec/qual-listp
    spec/qual-list-fix
    spec/qual-list-count

    align-specp
    align-spec-fix
    align-spec-count
    align-spec-case
    align-spec-alignas-type
    align-spec-alignas-expr
    irr-align-spec

    declspecp
    declspec-fix
    declspec-count
    declspec-case
    declspec-tyspec
    declspec-align
    declspec-attrib

    declspec-listp
    declspec-list-fix
    declspec-list-count

    initerp
    initer-fix
    initer-count
    initer-case
    initer-single
    make-initer-list

    initer-optionp
    initer-option-fix
    initer-option-count
    initer-option-case

    desiniterp
    desiniter-fix
    desiniter-count
    desiniter
    make-desiniter

    desiniter-listp
    desiniter-list-fix
    desiniter-list-count

    designorp
    designor-fix
    designor-count
    designor-case
    designor-sub

    designor-listp
    designor-list-fix
    designor-list-count

    declorp
    declor-fix
    declor-count
    declor
    make-declor
    declor->ident

    declor-optionp
    declor-option-fix
    declor-option-count
    declor-option-case

    dirdeclorp
    dirdeclor-fix
    dirdeclor-ident
    dirdeclor-count
    dirdeclor-case
    dirdeclor-paren
    dirdeclor
    make-dirdeclor-array
    make-dirdeclor-array-static1
    make-dirdeclor-array-static2
    make-dirdeclor-array-star
    make-dirdeclor-function-params
    make-dirdeclor-function-names

    absdeclorp
    absdeclor-fix
    absdeclor-count
    absdeclor
    make-absdeclor
    irr-absdeclor

    absdeclor-optionp
    absdeclor-option-fix
    absdeclor-option-count
    absdeclor-option-case

    dirabsdeclorp
    dirabsdeclor-fix
    dirabsdeclor-count
    dirabsdeclor-case
    dirabsdeclor-paren
    make-dirabsdeclor-array
    make-dirabsdeclor-array-static1
    make-dirabsdeclor-array-static2
    dirabsdeclor-array-star
    make-dirabsdeclor-function

    dirabsdeclor-optionp
    dirabsdeclor-option-fix
    dirabsdeclor-option-count
    dirabsdeclor-option-case
    irr-dirabsdeclor

    paramdecl
    paramdeclp
    paramdecl-fix
    paramdecl-count
    make-paramdecl

    paramdecl-listp
    paramdecl-list-fix
    paramdecl-list-count

    paramdeclorp
    paramdeclor-fix
    paramdeclor-count
    paramdeclor-case
    paramdeclor-declor
    paramdeclor-absdeclor
    paramdeclor-none
    irr-paramdeclor

    tynamep
    tyname-fix
    tyname-count
    tyname
    make-tyname

    strunispecp
    strunispec-fix
    strunispec-count
    strunispec
    make-strunispec

    structdeclp
    structdecl-fix
    structdecl-count
    structdecl-case
    make-structdecl-member
    structdecl-statassert

    structdecl-listp
    structdecl-list-fix
    structdecl-list-count

    structdeclorp
    structdeclor-fix
    structdeclor-count
    structdeclor
    make-structdeclor

    structdeclor-listp
    structdeclor-list-fix
    structdeclor-list-count

    enumspecp
    enumspec-fix
    enumspec-count
    enumspec
    make-enumspec

    enumerp
    enumer-fix
    enumer-count
    enumer
    make-enumer

    enumer-listp
    enumer-list-fix
    enumer-list-count

    statassertp
    statassert-fix
    statassert-count
    statassert
    make-statassert

    initdeclorp
    initdeclor-fix
    initdeclor
    make-initdeclor

    initdeclor-listp
    initdeclor-list-fix

    declp
    decl
    decl-fix
    decl-case
    make-decl-decl
    decl-statassert

    decl-listp

    labelp
    label-fix
    label-case
    label-const

    stmtp
    stmt-fix
    stmt-count
    stmt-case
    make-stmt-labeled
    stmt-compound
    stmt-expr
    make-stmt-if
    make-stmt-ifelse
    make-stmt-switch
    make-stmt-while
    make-stmt-dowhile
    make-stmt-for-expr
    make-stmt-for-decl
    stmt-return
    irr-stmt

    block-itemp
    block-item-fix
    block-item-count
    block-item-case
    block-item-decl
    block-item-stmt
    irr-block-item

    block-item-listp
    block-item-list-fix
    block-item-list-count

    fundefp
    fundef
    fundef-fix
    make-fundef
    fundef->declor

    fundef-optionp
    fundef-option-case

    extdeclp
    extdecl-fix
    extdecl-case
    extdecl-fundef
    extdecl-fundef->unwrap
    extdecl-decl

    extdecl-listp
    extdecl-list-fix

    transunitp
    transunit
    transunit->decls

    filepath-transunit-mapp

    transunit-ensemblep
    transunit-ensemble
    transunit-ensemble->unwrap

    filepathp
    filepath
    filepath->unwrap

    filedatap
    filedata
    filedata->unwrap

    filesetp
    fileset
    fileset->unwrap

    ;; unambiguity predicates:

    expr-unambp
    expr-list-unambp
    expr-option-unambp
    const-expr-unambp
    const-expr-option-unambp
    genassoc-unambp
    genassoc-list-unambp
    type-spec-unambp
    type-spec-list-unambp
    spec/qual-unambp
    spec/qual-list-unambp
    align-spec-unambp
    declspec-unambp
    declspec-list-unambp
    initer-unambp
    initer-option-unambp
    desiniter-unambp
    desiniter-list-unambp
    designor-unambp
    designor-list-unambp
    declor-unambp
    declor-option-unambp
    dirdeclor-unambp
    absdeclor-unambp
    absdeclor-option-unambp
    dirabsdeclor-unambp
    dirabsdeclor-option-unambp
    paramdecl-unambp
    paramdecl-list-unambp
    paramdeclor-unambp
    tyname-unambp
    strunispec-unambp
    structdecl-unambp
    structdecl-list-unambp
    structdeclor-unambp
    structdeclor-list-unambp
    enumspec-unambp
    enumer-unambp
    enumer-list-unambp
    statassert-unambp
    initdeclor-unambp
    initdeclor-list-unambp
    decl-unambp
    decl-list-unambp
    label-unambp
    stmt-unambp
    block-item-unambp
    block-item-list-unambp
    fundef-unambp
    extdecl-unambp
    extdecl-list-unambp
    transunit-unambp
    transunit-ensemble-unambp-loop
    transunit-ensemble-unambp

   ))
