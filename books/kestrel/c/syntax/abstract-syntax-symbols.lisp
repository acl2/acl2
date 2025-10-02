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

    ;; code representation:

    identp
    ident
    ident-fix
    ident->unwrap

    ident-listp

    ident-list-listp

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

    asm-name-spec-optionp

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
    expr-binary->op
    expr-binary->arg1
    expr-binary->arg2
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

    type-spec-listp

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
    make-designor-sub

    designor-listp
    designor-list-fix
    designor-list-count

    declorp
    declor-fix
    declor-count
    declor
    make-declor
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

    param-declorp
    param-declor-fix
    param-declor-count
    param-declor-case
    make-param-declor-nonabstract
    param-declor-nonabstract->declor
    param-declor-abstract
    param-declor-none

    tynamep
    tyname-fix
    tyname-count
    tyname
    make-tyname
    tyname->info

    struni-specp
    struni-spec-fix
    struni-spec-count
    struni-spec
    make-struni-spec

    struct-declonp
    struct-declon-fix
    struct-declon-count
    struct-declon-case
    make-struct-declon-member
    struct-declon-statassert
    struct-declon-empty

    struct-declon-listp
    struct-declon-list-fix
    struct-declon-list-count

    struct-declorp
    struct-declor-fix
    struct-declor-count
    struct-declor
    make-struct-declor

    struct-declor-listp
    struct-declor-list-fix
    struct-declor-list-count

    enum-specp
    enum-spec-fix
    enum-spec-count
    enum-spec
    make-enum-spec

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

    attrib-spec-listp

    initdeclorp
    initdeclor-fix
    initdeclor-count
    initdeclor
    make-initdeclor
    initdeclor->declor
    initdeclor->init?

    initdeclor-listp
    initdeclor-list-fix
    initdeclor-list-count

    declp
    decl
    decl-fix
    decl-count
    decl-case
    make-decl-decl
    decl-decl->extension
    decl-decl->specs
    decl-decl->init
    decl-statassert

    decl-listp
    decl-list-count

    labelp
    label-fix
    label-count
    label-case
    make-label-name
    make-label-casexpr

    stmtp
    stmt-fix
    stmt-count
    stmt-case
    make-stmt-labeled
    stmt-compound
    make-stmt-compound
    stmt-compound->items
    make-stmt-expr
    make-stmt-if
    make-stmt-ifelse
    make-stmt-switch
    make-stmt-while
    make-stmt-dowhile
    make-stmt-for-expr
    make-stmt-for-decl
    make-stmt-return

    block-itemp
    block-item-fix
    block-item-count
    block-item-case
    make-block-item-decl
    make-block-item-stmt

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

    code-ensemble
    code-ensemblep
    code-ensemble->transunits
    code-ensemble->ienv
    make-code-ensemble
    change-code-ensemble

    ienv

    ;; irrelevants:

    irr-expr
    irr-const-expr
    irr-type-spec
    irr-align-spec
    irr-dirdeclor
    irr-absdeclor
    irr-dirabsdeclor
    irr-param-declon
    irr-param-declor
    irr-decl
    irr-stmt
    irr-block-item
    irr-fundef
    irr-transunit-ensemble
    irr-code-ensemble

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
    param-declor-unambp
    tyname-unambp
    struni-spec-unambp
    struct-declon-unambp
    struct-declon-list-unambp
    struct-declor-unambp
    struct-declor-list-unambp
    enum-spec-unambp
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
    code-ensemble-unambp

    ;; purity:

    expr-purep
    expr-option-purep

    ;; ASCII identifiers:

    ident-aidentp
    ident-list-list-aidentp
    const-aidentp
    expr-aidentp
    expr-list-aidentp
    expr-option-aidentp
    const-expr-aidentp
    const-expr-option-aidentp
    genassoc-aidentp
    genassoc-list-aidentp
    member-designor-aidentp
    type-spec-aidentp
    spec/qual-aidentp
    spec/qual-list-aidentp
    align-spec-aidentp
    decl-spec-aidentp
    decl-spec-list-aidentp
    initer-aidentp
    initer-option-aidentp
    desiniter-aidentp
    desiniter-list-aidentp
    designor-aidentp
    designor-list-aidentp
    declor-aidentp
    declor-option-aidentp
    dirdeclor-aidentp
    absdeclor-aidentp
    absdeclor-option-aidentp
    dirabsdeclor-aidentp
    dirabsdeclor-option-aidentp
    param-declon-aidentp
    param-declon-list-aidentp
    param-declor-aidentp
    tyname-aidentp
    struni-spec-aidentp
    struct-declon-aidentp
    struct-declon-list-aidentp
    struct-declor-aidentp
    struct-declor-list-aidentp
    enum-spec-aidentp
    enumer-aidentp
    enumer-list-aidentp
    statassert-aidentp
    attrib-spec-list-aidentp
    initdeclor-aidentp
    initdeclor-list-aidentp
    decl-aidentp
    decl-list-aidentp
    label-aidentp
    stmt-aidentp
    block-item-aidentp
    block-item-list-aidentp
    fundef-aidentp
    extdecl-aidentp
    extdecl-list-aidentp
    transunit-aidentp
    filepath-transunit-map-aidentp
    transunit-ensemble-aidentp
    code-ensemble-aidentp

    ;; formalized subset:

    ident-formalp
    expr-pure-formalp
    expr-asg-formalp
    initer-formalp
    dirdeclor-block-formalp
    declor-block-formalp
    initdeclor-block-formalp
    decl-block-formalp
    stmt-formalp
    block-item-formalp
    block-item-list-formalp
    fundef-formalp

    ;; language mapping:

    ldm-ident
    ldm-tyname
    ldm-binop
    ldm-expr
    ldm-expr-option
    ldm-initer
    ldm-type-spec-list
    ldm-decl-obj
    ldm-stmt
    ldm-block-item
    ldm-block-item-list
    ldm-param-declon-list
    ldm-fundef
    ldm-type
    ldm-type-set
    ldm-type-option-set

    ildm-type

    ;; validation information:

    type-case
    type-kind
    type-void
    type-sint

    ident-type-map
    ident-type-mapp
    ident-type-map-fix

    type-formalp
    type-to-value-kind
    type-integerp

    iconst-info

    var-info
    var-infop
    var-info-fix
    coerce-var-info

    expr-unary-infop

    expr-binary-infop

    tyname-info
    tyname-infop

    param-declor-nonabstract-info
    param-declor-nonabstract-info->type

    initdeclor-info
    initdeclor-info->type
    initdeclor-info->typedefp

    fundef-info
    fundef-infop
    fundef-info->type
    fundef-info->table-body-start

    expr-type
    initer-type
    stmt-types
    block-item-types
    block-item-list-types
    fundef-types

    valid-ord-info-case
    valid-ord-info-objfun->type

    valid-ord-scopep

    valid-scopep
    valid-scope->ord

    valid-scope-listp

    valid-tablep
    valid-table->scopes

    iconst-annop
    const-annop
    expr-annop
    expr-list-annop
    expr-option-annop
    const-expr-annop
    const-expr-option-annop
    genassoc-annop
    genassoc-list-annop
    member-designor-annop
    type-spec-annop
    spec/qual-annop
    spec/qual-list-annop
    align-spec-annop
    decl-spec-annop
    decl-spec-list-annop
    initer-annop
    initer-option-annop
    desiniter-annop
    desiniter-list-annop
    designor-annop
    designor-list-annop
    declor-annop
    declor-option-annop
    dirdeclor-annop
    absdeclor-annop
    absdeclor-option-annop
    dirabsdeclor-annop
    dirabsdeclor-option-annop
    param-declon-annop
    param-declon-list-annop
    param-declor-annop
    tyname-annop
    struni-spec-annop
    struct-declon-annop
    struct-declon-list-annop
    struct-declor-annop
    struct-declor-list-annop
    enum-spec-annop
    enumer-annop
    enumer-list-annop
    statassert-annop
    initdeclor-annop
    initdeclor-list-annop
    decl-annop
    decl-list-annop
    label-annop
    stmt-annop
    block-item-annop
    block-item-list-annop
    fundef-annop
    extdecl-annop
    extdecl-list-annop
    transunit-annop
    filepath-transunit-map-annop
    transunit-ensemble-annop
    code-ensemble-annop

    ;; other operations:

    expr-zerop
    check-decl-spec-list-all-typespec
    declor->ident

   ))
