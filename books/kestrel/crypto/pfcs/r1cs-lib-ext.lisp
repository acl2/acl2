; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
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

(defrule sparse-vectorp-of-append
  (equal (r1cs::sparse-vectorp (append x y))
         (and (r1cs::sparse-vectorp (true-list-fix x))
              (r1cs::sparse-vectorp y)))
  :enable r1cs::sparse-vectorp)

(defrule sparse-vectorp-of-rev
  (equal (r1cs::sparse-vectorp (rev x))
         (r1cs::sparse-vectorp (true-list-fix x)))
  :enable (r1cs::sparse-vectorp
           rev))
