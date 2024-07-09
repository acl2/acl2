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

    identp
    ident->unwrap

    dec/oct/hex-const-case
    dec/oct/hex-const-oct

    iconst

    const-case
    const-int->unwrap

    exprp
    expr-fix
    expr-count
    expr-case
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
    make-expr-cast
    make-expr-binary
    make-expr-cond
    make-expr-comma

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

    tyspecp
    tyspec-fix
    tyspec-count
    tyspec-case
    tyspec-atomic
    tyspec-struct
    tyspec-union
    tyspec-enum

    specqualp
    specqual-fix
    specqual-count
    specqual-case
    specqual-tyspec
    specqual-alignspec

    specqual-listp
    specqual-list-fix
    specqual-list-count

    alignspecp
    alignspec-fix
    alignspec-count
    alignspec-case
    alignspec-alignas-type
    alignspec-alignas-expr

    declspecp
    declspec-fix
    declspec-count
    declspec-case
    declspec-tyspec
    declspec-alignspec

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
    dirdeclor-count
    dirdeclor-case
    dirdeclor-paren
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
    make-stmt-for
    make-stmt-fordecl
    stmt-return

    block-itemp
    block-item-fix
    block-item-count
    block-item-case
    block-item-decl
    block-item-stmt

    block-item-listp
    block-item-list-count

    fundefp
    fundef
    make-fundef
    fundef->declor

    extdeclp
    extdecl-case
    extdecl-fundef
    extdecl-fundef->unwrap
    extdecl-decl

    extdecl-listp

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

   ))
