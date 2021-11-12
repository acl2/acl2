; Documentation for the (sparse) R1CS formalization
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/utilities/gen-xdoc-for-file" :dir :system)

;; Introduced by defaggregate
(acl2::defxdoc r1csp
  :short "Recognize An R1CS"
  :long "An R1CS is a defaggregate whose fields represent a prime, a list of variables, and a list of constraints.  The constructor is @('r1cs'), and the accessors are @('r1cs->prime'), @('r1cs->vars') and @('r1cs->constraints') ."
  :parents (r1cs))

;; Introduced by defaggregate
(acl2::defxdoc r1cs-constraintp
  :short "Recognize An R1CS constraint"
  :long "An R1CS constraint is a defaggregate with 3 fields, A, B, and C, each of which is a sparse vector.  The constructor is @('r1cs-constraint'), and the accessors are @('r1cs-constraint->a'), @('r1cs-constraint->b'), and @('r1cs-constraint->c')."
  :parents (r1cs))

;; (depends-on "r1cs.lisp")
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
