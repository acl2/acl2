; Lists of rules about R1CSes (for Axe)
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/prime-fields/rule-lists" :dir :system)

(defun r1cs-rules ()
  (declare (xargs :guard t))
  '(r1cs-holdsp
    r1cs-constraints-holdp-opener
    r1cs-constraints-holdp-base
    r1cs-constraint-holdsp
    r1cs
    r1cs-constraint
    acl2::assoc-equal-of-cons
    ;; fep-when-constant ;todo: drop or move
    endp
    atom
    r1cs->constraints$inline
    r1cs->prime$inline
    r1cs-constraint->a$inline
    r1cs-constraint->b$inline
    r1cs-constraint->c$inline
    dot-product-unroll
    dot-product-base
    acl2::lookup-eq-becomes-lookup-equal
    acl2::lookup-equal-of-cons-safe
    car-cons
    cdr-cons
    acl2::equal-self
    ))

(defun r1cs-proof-rules ()
  (declare (xargs :guard t))
  (append (pfield::prime-field-proof-rules)
          (r1cs-rules)))
