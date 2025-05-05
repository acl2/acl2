; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; List of symbols that provide an API to
; the abstract syntax and related concepts,
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

    ident-set
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

    typequal/attribspec-list-listp

    unopp
    unop-case
    unop-kind

    binopp
    binop-case
    binop-kind

    exprp
    expr-fix
    expr-count
    expr-case
    expr-ident
    make-expr-ident
    expr-ident->ident
    expr-const
    expr-const->const
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
    expr-stmt
    make-expr-tycompat
    make-expr-offsetof
    make-expr-va-arg
    expr-extension

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
    const-expr->expr

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

    member-designorp
    member-designor-fix
    member-designor-count
    member-designor-case
    make-member-designor-dot
    make-member-designor-sub

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

    type-spec-optionp

    spec/qual-p
    spec/qual-fix
    spec/qual-count
    spec/qual-case
    spec/qual-typespec
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

    decl-specp
    decl-spec-fix
    decl-spec-count
    decl-spec-case
    decl-spec-typespec
    decl-spec-align
    decl-spec-attrib

    decl-spec-listp
    decl-spec-list-fix
    decl-spec-list-count

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
    declor->direct

    declor-optionp
    declor-option-fix
    declor-option-count
    declor-option-case

    dirdeclorp
    dirdeclor-fix
    dirdeclor-ident
    dirdeclor-ident->ident
    dirdeclor-count
    dirdeclor-case
    dirdeclor-kind
    dirdeclor-paren
    dirdeclor
    make-dirdeclor-array
    make-dirdeclor-array-static1
    make-dirdeclor-array-static2
    make-dirdeclor-array-star
    make-dirdeclor-function-params
    make-dirdeclor-function-names
    dirdeclor-function-params->declor
    dirdeclor-function-params->params
    dirdeclor-function-names->names

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

    param-declon
    param-declonp
    param-declon-fix
    param-declon-count
    make-param-declon

    param-declon-listp
    param-declon-list-fix
    param-declon-list-count

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
    structdecl-empty

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
    initdeclor-count
    initdeclor
    make-initdeclor

    initdeclor-listp
    initdeclor-list-fix
    initdeclor-list-count

    declp
    decl
    decl-fix
    decl-count
    decl-case
    make-decl-decl
    decl-statassert

    decl-listp
    decl-list-count

    labelp
    label-fix
    label-count
    label-case
    make-label-casexpr

    stmtp
    stmt-fix
    stmt-count
    stmt-case
    make-stmt-labeled
    stmt-compound
    stmt-compound->items
    stmt-expr
    make-stmt-if
    make-stmt-ifelse
    make-stmt-switch
    make-stmt-while
    make-stmt-dowhile
    make-stmt-for-expr
    make-stmt-for-decl
    stmt-return

    block-itemp
    block-item-fix
    block-item-count
    block-item-case
    block-item-decl
    block-item-stmt

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
    extdecl-empty

    extdecl-listp
    extdecl-list-fix

    transunitp
    transunit
    make-transunit
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

    ;; irrelevants:

    irr-expr
    irr-const-expr
    irr-type-spec
    irr-align-spec
    irr-absdeclor
    irr-dirabsdeclor
    irr-param-declon
    irr-paramdeclor
    irr-decl
    irr-stmt
    irr-block-item
    irr-fundef
    irr-transunit-ensemble

    ;; unambiguity:

    expr-unambp
    expr-list-unambp
    expr-option-unambp
    const-expr-unambp
    const-expr-option-unambp
    genassoc-unambp
    genassoc-list-unambp
    member-designor-unambp
    type-spec-unambp
    type-spec-list-unambp
    spec/qual-unambp
    spec/qual-list-unambp
    align-spec-unambp
    decl-spec-unambp
    decl-spec-list-unambp
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
    param-declon-unambp
    param-declon-list-unambp
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
    filepath-transunit-map-unambp
    transunit-ensemble-unambp

    ;; formalized:

    expr-pure-formalp
    stmt-formalp
    block-item-formalp
    block-item-list-formalp
    fundef-formalp

    ;; language mapping:

    ldm-ident
    ldm-binop
    ldm-expr
    ldm-stmt
    ldm-block-item
    ldm-block-item-list
    ldm-param-declon-list
    ldm-fundef

    ;; validation information:

    type-case
    type-kind
    type-sint

    ident-type-map
    ident-type-mapp
    ident-type-map-fix

    type-formalp
    ldm-type
    type-to-value-kind

    iconst-info
    coerce-iconst-info

    var-info
    var-infop
    var-info-fix
    coerce-var-info

    unary-infop
    coerce-unary-info

    binary-infop
    coerce-binary-info

    expr-type
    stmt-type
    block-item-type
    block-item-list-type

    transunit-ensemble-annop

    ;; other operations:

    expr-zerop

   ))
