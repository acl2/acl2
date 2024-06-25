; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/c/portcullis" :dir :system)
(include-book "kestrel/c/syntax/portcullis" :dir :system)
(include-book "kestrel/utilities/omaps/portcullis" :dir :system)
(include-book "oslib/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "C2C" (append
               (set-difference-eq *std-pkg-symbols*
                                  '())
               '(defxdoc+
                 index-of

                 c$::identp
                 c$::ident->unwrap

                 c$::dec/oct/hex-const-case
                 c$::dec/oct/hex-const-oct

                 c$::iconst

                 c$::const-case
                 c$::const-int->unwrap

                 c$::exprp
                 c$::expr-fix
                 c$::expr-count
                 c$::expr-case
                 c$::expr-const
                 c$::expr-const->unwrap
                 c$::expr-paren
                 c$::make-expr-gensel
                 c$::make-expr-arrsub
                 c$::make-expr-funcall
                 c$::make-expr-member
                 c$::make-expr-memberp
                 c$::make-expr-complit
                 c$::make-expr-unary
                 c$::expr-sizeof
                 c$::expr-alignof
                 c$::make-expr-cast
                 c$::make-expr-binary
                 c$::make-expr-cond
                 c$::make-expr-comma

                 c$::expr-listp
                 c$::expr-list-fix
                 c$::expr-list-count

                 c$::expr-optionp
                 c$::expr-option-fix
                 c$::expr-option-count
                 c$::expr-option-case

                 c$::const-exprp
                 c$::const-expr-count
                 c$::const-expr
                 c$::const-expr->unwrap

                 c$::const-expr-optionp
                 c$::const-expr-option-fix
                 c$::const-expr-option-count
                 c$::const-expr-option-case

                 c$::genassocp
                 c$::genassoc-fix
                 c$::genassoc-count
                 c$::genassoc-case
                 c$::make-genassoc-type
                 c$::genassoc-default

                 c$::genassoc-listp
                 c$::genassoc-list-fix
                 c$::genassoc-list-count

                 c$::tyspecp
                 c$::tyspec-fix
                 c$::tyspec-count
                 c$::tyspec-case
                 c$::tyspec-atomic
                 c$::tyspec-struct
                 c$::tyspec-union
                 c$::tyspec-enum

                 c$::specqualp
                 c$::specqual-fix
                 c$::specqual-count
                 c$::specqual-case
                 c$::specqual-tyspec
                 c$::specqual-alignspec

                 c$::specqual-listp
                 c$::specqual-list-fix
                 c$::specqual-list-count

                 c$::alignspecp
                 c$::alignspec-fix
                 c$::alignspec-count
                 c$::alignspec-case
                 c$::alignspec-alignas-type
                 c$::alignspec-alignas-expr

                 c$::declspecp
                 c$::declspec-fix
                 c$::declspec-count
                 c$::declspec-case
                 c$::declspec-tyspec
                 c$::declspec-alignspec

                 c$::declspec-listp
                 c$::declspec-list-fix
                 c$::declspec-list-count

                 c$::initerp
                 c$::initer-fix
                 c$::initer-count
                 c$::initer-case
                 c$::initer-single
                 c$::make-initer-list

                 c$::initer-optionp
                 c$::initer-option-fix
                 c$::initer-option-count
                 c$::initer-option-case

                 c$::desiniterp
                 c$::desiniter-fix
                 c$::desiniter-count
                 c$::desiniter
                 c$::make-desiniter

                 c$::desiniter-listp
                 c$::desiniter-list-fix
                 c$::desiniter-list-count

                 c$::designorp
                 c$::designor-fix
                 c$::designor-count
                 c$::designor-case
                 c$::designor-sub

                 c$::designor-listp
                 c$::designor-list-fix
                 c$::designor-list-count

                 c$::declorp
                 c$::declor-fix
                 c$::declor-count
                 c$::declor
                 c$::make-declor
                 c$::declor->ident

                 c$::declor-optionp
                 c$::declor-option-fix
                 c$::declor-option-count
                 c$::declor-option-case

                 c$::dirdeclorp
                 c$::dirdeclor-fix
                 c$::dirdeclor-count
                 c$::dirdeclor-case
                 c$::dirdeclor-paren
                 c$::make-dirdeclor-array
                 c$::make-dirdeclor-array-static1
                 c$::make-dirdeclor-array-static2
                 c$::make-dirdeclor-array-star
                 c$::make-dirdeclor-function-params
                 c$::make-dirdeclor-function-names

                 c$::absdeclorp
                 c$::absdeclor-fix
                 c$::absdeclor-count
                 c$::absdeclor
                 c$::make-absdeclor

                 c$::absdeclor-optionp
                 c$::absdeclor-option-fix
                 c$::absdeclor-option-count
                 c$::absdeclor-option-case

                 c$::dirabsdeclorp
                 c$::dirabsdeclor-fix
                 c$::dirabsdeclor-count
                 c$::dirabsdeclor-case
                 c$::dirabsdeclor-paren
                 c$::make-dirabsdeclor-array
                 c$::make-dirabsdeclor-array-static1
                 c$::make-dirabsdeclor-array-static2
                 c$::dirabsdeclor-array-star
                 c$::make-dirabsdeclor-function

                 c$::dirabsdeclor-optionp
                 c$::dirabsdeclor-option-fix
                 c$::dirabsdeclor-option-count
                 c$::dirabsdeclor-option-case

                 c$::paramdecl
                 c$::paramdeclp
                 c$::paramdecl-fix
                 c$::paramdecl-count
                 c$::make-paramdecl

                 c$::paramdecl-listp
                 c$::paramdecl-list-fix
                 c$::paramdecl-list-count

                 c$::paramdeclorp
                 c$::paramdeclor-fix
                 c$::paramdeclor-count
                 c$::paramdeclor-case
                 c$::paramdeclor-declor
                 c$::paramdeclor-absdeclor
                 c$::paramdeclor-none

                 c$::tynamep
                 c$::tyname-fix
                 c$::tyname-count
                 c$::tyname
                 c$::make-tyname

                 c$::strunispecp
                 c$::strunispec-fix
                 c$::strunispec-count
                 c$::strunispec
                 c$::make-strunispec

                 c$::structdeclp
                 c$::structdecl-fix
                 c$::structdecl-count
                 c$::structdecl-case
                 c$::make-structdecl-member
                 c$::structdecl-statassert

                 c$::structdecl-listp
                 c$::structdecl-list-fix
                 c$::structdecl-list-count

                 c$::structdeclorp
                 c$::structdeclor-fix
                 c$::structdeclor-count
                 c$::structdeclor
                 c$::make-structdeclor

                 c$::structdeclor-listp
                 c$::structdeclor-list-fix
                 c$::structdeclor-list-count

                 c$::enumspecp
                 c$::enumspec-fix
                 c$::enumspec-count
                 c$::enumspec
                 c$::make-enumspec

                 c$::enumerp
                 c$::enumer-fix
                 c$::enumer-count
                 c$::enumer
                 c$::make-enumer

                 c$::enumer-listp
                 c$::enumer-list-fix
                 c$::enumer-list-count

                 c$::statassertp
                 c$::statassert-fix
                 c$::statassert-count
                 c$::statassert
                 c$::make-statassert

                 c$::initdeclorp
                 c$::initdeclor-fix
                 c$::initdeclor
                 c$::make-initdeclor

                 c$::initdeclor-listp
                 c$::initdeclor-list-fix

                 c$::declp
                 c$::decl-case
                 c$::make-decl-decl
                 c$::decl-statassert

                 c$::decl-listp

                 c$::labelp
                 c$::label-fix
                 c$::label-case
                 c$::label-const

                 c$::stmtp
                 c$::stmt-fix
                 c$::stmt-count
                 c$::stmt-case
                 c$::make-stmt-labeled
                 c$::stmt-compound
                 c$::stmt-expr
                 c$::make-stmt-if
                 c$::make-stmt-ifelse
                 c$::make-stmt-switch
                 c$::make-stmt-while
                 c$::make-stmt-dowhile
                 c$::make-stmt-for
                 c$::make-stmt-fordecl
                 c$::stmt-return

                 c$::block-itemp
                 c$::block-item-count
                 c$::block-item-case
                 c$::block-item-decl
                 c$::block-item-stmt

                 c$::block-item-listp
                 c$::block-item-list-count

                 c$::fundefp
                 c$::fundef
                 c$::make-fundef
                 c$::fundef->declor

                 c$::extdeclp
                 c$::extdecl-case
                 c$::extdecl-fundef
                 c$::extdecl-fundef->unwrap
                 c$::extdecl-decl

                 c$::extdecl-listp

                 c$::transunitp
                 c$::transunit
                 c$::transunit->decls

                 c$::filepath-transunit-mapp

                 c$::transunit-ensemblep
                 c$::transunit-ensemble
                 c$::transunit-ensemble->unwrap

                 c$::filepathp
                 c$::filepath
                 c$::filepath->unwrap

                 c$::filedatap
                 c$::filedata
                 c$::filedata->unwrap

                 c$::filesetp
                 c$::fileset
                 c$::fileset->unwrap

                 )))
