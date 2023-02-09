; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ r1cs-library-extensions
  :parents (prime-field-constraint-systems)
  :short "Extensions of the R1CS library."
  :long
  (xdoc::topstring
   (xdoc::p
    "These may be moved to the R1CS library."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule r1cs::sparse-vectorp-of-rev
  (equal (r1cs::sparse-vectorp (rev x))
         (r1cs::sparse-vectorp (true-list-fix x)))
  :enable (r1cs::sparse-vectorp
           rev))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule r1cs::r1cs-constraint-listp-of-rev
  (equal (r1cs::r1cs-constraint-listp (rev vector))
         (r1cs::r1cs-constraint-listp (true-list-fix vector)))
  :enable rev)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule r1cs::valuation-binds-allp-of-rev
  (equal (r1cs::valuation-binds-allp valuation (rev vars))
         (r1cs::valuation-binds-allp valuation vars))
  :enable r1cs::valuation-binds-allp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule r1cs::r1cs-constraints-holdp-of-rev
  (equal (r1cs::r1cs-constraints-holdp (rev vector) valuation prime)
         (r1cs::r1cs-constraints-holdp vector valuation prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule r1cs::valuation-binds-allp-of-nthcdr
  (implies (r1cs::valuation-binds-allp valuation vars)
           (r1cs::valuation-binds-allp valuation (nthcdr n vars)))
  :enable r1cs::valuation-binds-allp)
