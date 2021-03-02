; Documentation for the (sparse) R1CS formalization
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; (depends-on r1cs.lisp")

(include-book "kestrel/utilities/gen-xdoc-for-file" :dir :system)

;; Introduced by defaggregate
(acl2::defxdoc r1cs-constraintp
  :short "Recognize An R1CS constraint"
  :long "An R1CS constraint is a defaggregate with 3 fields, A, B, and C, each of which is a sparse vector.")

(acl2::gen-xdoc-for-file
 "r1cs.lisp"
 ((pseudo-varp "Recognize a pseudo-variable (a symbol or 1).")
  (pseudo-var-listp "Recognize a true-list of pseudo-variables.")
  (sparse-vectorp "Recognize a sparse vector in an R1CS constraint.")
  ;; r1cs-constraintp documented above
  (r1cs-constraint-listp "Recognize a true list of R1CS constraints.")
  (dot-product "Dot product of R1CS coefficients and values.")
  (r1cs-constraint-holdsp "Check whether a valuation satisfies an R1CS constraint")
  (r1cs-constraints-holdp "Check whether a valuation satisfies a list of R1CS constraints")
  (r1cs-holdsp "Check whether a valuation satisifies an R1CS."))
 (r1cs))
