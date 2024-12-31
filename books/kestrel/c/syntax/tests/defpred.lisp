; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../defpred")
(include-book "../unambiguity")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpred unambp$
  :default t
  :override
  ((expr :sizeof-ambig nil)
   (expr :cast/call-ambig nil)
   (expr :cast/mul-ambig nil)
   (expr :cast/add-ambig nil)
   (expr :cast/sub-ambig nil)
   (expr :cast/and-ambig nil)
   (type-spec :typeof-ambig nil)
   (align-spec :alignas-ambig nil)
   (typequal/attribspec t)
   (dirabsdeclor :dummy-base nil)
   (attrib t)
   (attrib-spec t)
   (asm-output t)
   (asm-input t)
   (asm-stmt t)
   (stmt :for-ambig nil)
   (block-item :ambig nil)
   (amb-expr/tyname nil)
   (amb-declor/absdeclor nil)
   (amb-decl/stmt nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm-exprs/decls/stmts-unambp-flag
  (defthm theorem-for-expr-unambp
    (equal (expr-unambp expr)
           (expr-unambp$ expr))
    :flag expr-unambp)
  (defthm theorem-for-expr-list-unambp
    (equal (expr-list-unambp exprs)
           (expr-list-unambp$ exprs))
    :flag expr-list-unambp)
  (defthm theorem-for-expr-option-unambp
    (equal (expr-option-unambp expr?)
           (expr-option-unambp$ expr?))
    :flag expr-option-unambp)
  (defthm theorem-for-const-expr-unambp
    (equal (const-expr-unambp cexpr)
           (const-expr-unambp$ cexpr))
    :flag const-expr-unambp)
  (defthm theorem-for-const-expr-option-unambp
    (equal (const-expr-option-unambp cexpr?)
           (const-expr-option-unambp$ cexpr?))
    :flag const-expr-option-unambp)
  (defthm theorem-for-genassoc-unambp
    (equal (genassoc-unambp assoc)
           (genassoc-unambp$ assoc))
    :flag genassoc-unambp)
  (defthm theorem-for-genassoc-list-unambp
    (equal (genassoc-list-unambp assocs)
           (genassoc-list-unambp$ assocs))
    :flag genassoc-list-unambp)
  (defthm theorem-for-member-designor-unambp
    (equal (member-designor-unambp memdes)
           (member-designor-unambp$ memdes))
    :flag member-designor-unambp)
  (defthm theorem-for-type-spec-unambp
    (equal (type-spec-unambp tyspec)
           (type-spec-unambp$ tyspec))
    :flag type-spec-unambp)
  (defthm theorem-for-spec/qual-unambp
    (equal (spec/qual-unambp specqual)
           (spec/qual-unambp$ specqual))
    :flag spec/qual-unambp)
  (defthm theorem-for-spec/qual-list-unambp
    (equal (spec/qual-list-unambp specquals)
           (spec/qual-list-unambp$ specquals))
    :flag spec/qual-list-unambp)
  (defthm theorem-for-align-spec-unambp
    (equal (align-spec-unambp alignspec)
           (align-spec-unambp$ alignspec))
    :flag align-spec-unambp)
  (defthm theorem-for-decl-spec-unambp
    (equal (decl-spec-unambp declspec)
           (decl-spec-unambp$ declspec))
    :flag decl-spec-unambp)
  (defthm theorem-for-decl-spec-list-unambp
    (equal (decl-spec-list-unambp declspecs)
           (decl-spec-list-unambp$ declspecs))
    :flag decl-spec-list-unambp)
  (defthm theorem-for-initer-unambp
    (equal (initer-unambp initer)
           (initer-unambp$ initer))
    :flag initer-unambp)
  (defthm theorem-for-initer-option-unambp
    (equal (initer-option-unambp initer?)
           (initer-option-unambp$ initer?))
    :flag initer-option-unambp)
  (defthm theorem-for-desiniter-unambp
    (equal (desiniter-unambp desiniter)
           (desiniter-unambp$ desiniter))
    :flag desiniter-unambp)
  (defthm theorem-for-desiniter-list-unambp
    (equal (desiniter-list-unambp desiniters)
           (desiniter-list-unambp$ desiniters))
    :flag desiniter-list-unambp)
  (defthm theorem-for-designor-unambp
    (equal (designor-unambp designor)
           (designor-unambp$ designor))
    :flag designor-unambp)
  (defthm theorem-for-designor-list-unambp
    (equal (designor-list-unambp designors)
           (designor-list-unambp$ designors))
    :flag designor-list-unambp)
  (defthm theorem-for-declor-unambp
    (equal (declor-unambp declor)
           (declor-unambp$ declor))
    :flag declor-unambp)
  (defthm theorem-for-declor-option-unambp
    (equal (declor-option-unambp declor?)
           (declor-option-unambp$ declor?))
    :flag declor-option-unambp)
  (defthm theorem-for-dirdeclor-unambp
    (equal (dirdeclor-unambp dirdeclor)
           (dirdeclor-unambp$ dirdeclor))
    :flag dirdeclor-unambp)
  (defthm theorem-for-absdeclor-unambp
    (equal (absdeclor-unambp absdeclor)
           (absdeclor-unambp$ absdeclor))
    :flag absdeclor-unambp)
  (defthm theorem-for-absdeclor-option-unambp
    (equal (absdeclor-option-unambp absdeclor?)
           (absdeclor-option-unambp$ absdeclor?))
    :flag absdeclor-option-unambp)
  (defthm theorem-for-dirabsdeclor-unambp
    (equal (dirabsdeclor-unambp dirabsdeclor)
           (dirabsdeclor-unambp$ dirabsdeclor))
    :flag dirabsdeclor-unambp)
  (defthm theorem-for-dirabsdeclor-option-unambp
    (equal (dirabsdeclor-option-unambp dirabsdeclor?)
           (dirabsdeclor-option-unambp$ dirabsdeclor?))
    :flag dirabsdeclor-option-unambp)
  (defthm theorem-for-paramdecl-unambp
    (equal (paramdecl-unambp paramdecl)
           (paramdecl-unambp$ paramdecl))
    :flag paramdecl-unambp)
  (defthm theorem-for-paramdecl-list-unambp
    (equal (paramdecl-list-unambp paramdecls)
           (paramdecl-list-unambp$ paramdecls))
    :flag paramdecl-list-unambp)
  (defthm theorem-for-paramdeclor-unambp
    (equal (paramdeclor-unambp paramdeclor)
           (paramdeclor-unambp$ paramdeclor))
    :flag paramdeclor-unambp)
  (defthm theorem-for-tyname-unambp
    (equal (tyname-unambp tyname)
           (tyname-unambp$ tyname))
    :flag tyname-unambp)
  (defthm theorem-for-strunispec-unambp
    (equal (strunispec-unambp strunispec)
           (strunispec-unambp$ strunispec))
    :flag strunispec-unambp)
  (defthm theorem-for-structdecl-unambp
    (equal (structdecl-unambp structdecl)
           (structdecl-unambp$ structdecl))
    :flag structdecl-unambp)
  (defthm theorem-for-structdecl-list-unambp
    (equal (structdecl-list-unambp structdecls)
           (structdecl-list-unambp$ structdecls))
    :flag structdecl-list-unambp)
  (defthm theorem-for-structdeclor-unambp
    (equal (structdeclor-unambp structdeclor)
           (structdeclor-unambp$ structdeclor))
    :flag structdeclor-unambp)
  (defthm theorem-for-structdeclor-list-unambp
    (equal (structdeclor-list-unambp structdeclors)
           (structdeclor-list-unambp$ structdeclors))
    :flag structdeclor-list-unambp)
  (defthm theorem-for-enumspec-unambp
    (equal (enumspec-unambp enumspec)
           (enumspec-unambp$ enumspec))
    :flag enumspec-unambp)
  (defthm theorem-for-enumer-unambp
    (equal (enumer-unambp enumer)
           (enumer-unambp$ enumer))
    :flag enumer-unambp)
  (defthm theorem-for-enumer-list-unambp
    (equal (enumer-list-unambp enumers)
           (enumer-list-unambp$ enumers))
    :flag enumer-list-unambp)
  (defthm theorem-for-statassert-unambp
    (equal (statassert-unambp statassert)
           (statassert-unambp$ statassert))
    :flag statassert-unambp)
  (defthm theorem-for-initdeclor-unambp
    (equal (initdeclor-unambp initdeclor)
           (initdeclor-unambp$ initdeclor))
    :flag initdeclor-unambp)
  (defthm theorem-for-initdeclor-list-unambp
    (equal (initdeclor-list-unambp initdeclors)
           (initdeclor-list-unambp$ initdeclors))
    :flag initdeclor-list-unambp)
  (defthm theorem-for-decl-unambp
    (equal (decl-unambp decl)
           (decl-unambp$ decl))
    :flag decl-unambp)
  (defthm theorem-for-decl-list-unambp
    (equal (decl-list-unambp decls)
           (decl-list-unambp$ decls))
    :flag decl-list-unambp)
  (defthm theorem-for-label-unambp
    (equal (label-unambp label)
           (label-unambp$ label))
    :flag label-unambp)
  (defthm theorem-for-stmt-unambp
    (equal (stmt-unambp stmt)
           (stmt-unambp$ stmt))
    :flag stmt-unambp)
  (defthm theorem-for-block-item-unambp
    (equal (block-item-unambp item)
           (block-item-unambp$ item))
    :flag block-item-unambp)
  (defthm theorem-for-block-item-list-unambp
    (equal (block-item-list-unambp items)
           (block-item-list-unambp$ items))
    :flag block-item-list-unambp)
  :hints (("Goal"
           :expand ((spec/qual-unambp$ specqual)
                    (decl-spec-unambp$ declspec)
                    (dirdeclor-unambp$ dirdeclor)
                    (paramdeclor-unambp$ paramdeclor)
                    (structdecl-unambp$ structdecl)
                    (stmt-unambp$ stmt))
           :in-theory (enable expr-unambp
                              expr-unambp$
                              expr-list-unambp$
                              expr-option-unambp
                              expr-option-unambp$
                              const-expr-unambp
                              const-expr-unambp$
                              const-expr-option-unambp
                              const-expr-option-unambp$
                              genassoc-unambp
                              genassoc-unambp$
                              genassoc-list-unambp$
                              member-designor-unambp
                              member-designor-unambp$
                              type-spec-unambp
                              type-spec-unambp$
                              spec/qual-unambp
                              spec/qual-unambp$
                              spec/qual-list-unambp$
                              align-spec-unambp
                              align-spec-unambp$
                              decl-spec-unambp
                              decl-spec-unambp$
                              decl-spec-list-unambp$
                              initer-unambp
                              initer-unambp$
                              initer-option-unambp
                              initer-option-unambp$
                              desiniter-unambp
                              desiniter-unambp$
                              desiniter-list-unambp$
                              designor-unambp
                              designor-unambp$
                              designor-list-unambp$
                              declor-unambp
                              declor-unambp$
                              declor-option-unambp
                              declor-option-unambp$
                              dirdeclor-unambp
                              dirdeclor-unambp$
                              absdeclor-unambp
                              absdeclor-unambp$
                              absdeclor-option-unambp
                              absdeclor-option-unambp$
                              dirabsdeclor-unambp
                              dirabsdeclor-unambp$
                              dirabsdeclor-option-unambp
                              dirabsdeclor-option-unambp$
                              paramdecl-unambp
                              paramdecl-unambp$
                              paramdecl-list-unambp$
                              paramdeclor-unambp
                              paramdeclor-unambp$
                              tyname-unambp
                              tyname-unambp$
                              strunispec-unambp
                              strunispec-unambp$
                              structdecl-unambp
                              structdecl-unambp$
                              structdecl-list-unambp$
                              structdeclor-unambp
                              structdeclor-unambp$
                              structdeclor-list-unambp$
                              enumspec-unambp
                              enumspec-unambp$
                              enumer-unambp
                              enumer-unambp$
                              enumer-list-unambp$
                              statassert-unambp
                              statassert-unambp$
                              initdeclor-unambp
                              initdeclor-unambp$
                              initdeclor-list-unambp$
                              decl-unambp
                              decl-unambp$
                              decl-list-unambp$
                              label-unambp
                              label-unambp$
                              stmt-unambp
                              stmt-unambp$
                              block-item-unambp
                              block-item-unambp$
                              block-item-list-unambp$))))

;;;;;;;;;;;;;;;;;;;;

(defrule theorem-for-type-spec-list-unambp
  (equal (type-spec-list-unambp tyspecs)
         (type-spec-list-unambp$ tyspecs))
  :induct t
  :enable (type-spec-list-unambp
           type-spec-list-unambp$))

;;;;;;;;;;;;;;;;;;;;

(defrule theorem-for-fundef-unambp
  (equal (fundef-unambp fundef)
         (fundef-unambp$ fundef))
  :enable (fundef-unambp
           fundef-unambp$))

;;;;;;;;;;;;;;;;;;;;

(defrule theorem-for-extdecl-unambp
  (equal (extdecl-unambp edecl)
         (extdecl-unambp$ edecl))
  :enable (extdecl-unambp
           extdecl-unambp$))

;;;;;;;;;;;;;;;;;;;;

(defrule theorem-for-extdecl-list-unambp
  (equal (extdecl-list-unambp edecls)
         (extdecl-list-unambp$ edecls))
  :enable (extdecl-list-unambp
           extdecl-list-unambp$))

;;;;;;;;;;;;;;;;;;;;

(defrule theorem-for-transunit-unambp
  (equal (transunit-unambp tunit)
         (transunit-unambp$ tunit))
  :enable (transunit-unambp
           transunit-unambp$))

;;;;;;;;;;;;;;;;;;;;

(defrule theorem-for-transunit-ensemble-unambp-loop
  (implies (filepath-transunit-mapp tunitmap)
           (equal (transunit-ensemble-unambp-loop tunitmap)
                  (filepath-transunit-map-unambp$ tunitmap)))
  :induct t
  :enable (transunit-ensemble-unambp-loop
           filepath-transunit-map-unambp$))

;;;;;;;;;;;;;;;;;;;;

(defrule theorem-for-transuit-ensemble-unambp
  (equal (transunit-ensemble-unambp tunits)
         (transunit-ensemble-unambp$ tunits))
  :enable (transunit-ensemble-unambp
           transunit-ensemble-unambp$))
