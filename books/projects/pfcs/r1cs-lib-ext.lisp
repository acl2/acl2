; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS library extensions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule r1cs::sparse-vectorp-of-rev
  (equal (r1cs::sparse-vectorp (rev x))
         (r1cs::sparse-vectorp (true-list-fix x)))
  :induct t
  :enable (r1cs::sparse-vectorp
           rev))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule r1cs::r1cs-constraint-listp-of-rev
  (equal (r1cs::r1cs-constraint-listp (rev vector))
         (r1cs::r1cs-constraint-listp (true-list-fix vector)))
  :induct t
  :enable rev)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule r1cs::valuation-binds-allp-of-rev
  (equal (r1cs::valuation-binds-allp valuation (rev vars))
         (r1cs::valuation-binds-allp valuation vars))
  :induct t
  :enable r1cs::valuation-binds-allp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule r1cs::r1cs-constraints-holdp-of-rev
  (equal (r1cs::r1cs-constraints-holdp (rev vector) valuation prime)
         (r1cs::r1cs-constraints-holdp vector valuation prime))
  :induct t)
