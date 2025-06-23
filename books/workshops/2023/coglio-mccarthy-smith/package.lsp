; Package for the Examples in "r1cs.lisp" and "pfcs.lisp"
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2023 Aleo Systems Inc. (https://www.aleo.org)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (mccarthy@kestrel.edu)
;          Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/crypto/r1cs/portcullis" :dir :system)
(include-book "projects/pfcs/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ZKPAPER" (append *std-pkg-symbols*
                          '(bit-listp
                            lebits=>nat
                            lendian=>nat
                            lookup-equal
                            must-be-redundant
                            dm::primep
                            pfield::add
                            pfield::fep
                            pfield::fe-listp
                            pfield::inv
                            pfield::mul
                            pfield::sub
                            pfcs::assignmentp
                            pfcs::assignment-wfp
                            pfcs::constraint-vars
                            pfcs::constraint-listp
                            pfcs::constraint-list-satp
                            pfcs::constraint-list-vars
                            pfcs::definitionp
                            pfcs::definition->body
                            pfcs::definition->name
                            pfcs::definition->para
                            pfcs::definition-free-vars
                            pfcs::definition-satp
                            pfcs::defs
                            pfcs::eval-expr
                            pfcs::eval-expr-list
                            pfcs::expression-vars
                            pfcs::expression-list-vars
                            pfcs::iname
                            pfcs::iname-list
                            pfcs::lift
                            pfcs::lookup-definition
                            pfcs::name
                            pfcs::name-listp
                            pfcs::name-list-fix
                            pfcs::p
                            pfcs::pf+
                            pfcs::pf*
                            pfcs::pf=
                            pfcs::pfcall
                            pfcs::pfconst
                            pfcs::pfdef
                            pfcs::pfmon
                            pfcs::pfvar
                            r1cs::dot-product
                            r1cs::dot-product-of-append
                            r1cs::make-r1cs-constraint
                            r1cs::r1cs-constraint-holdsp
                            r1cs::r1cs-constraint-listp
                            r1cs::r1cs-constraints-holdp
                            r1cs::r1cs-valuationp
                            r1cs::sparse-vectorp
                            r1cs::valuation-bindsp
                            r1cs::valuation-binds-allp)))
