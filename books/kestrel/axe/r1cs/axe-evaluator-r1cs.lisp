; An evaluator supporting R1CS Axe reasoning
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; An Axe evaluator for R1CS proofs (really, for proofs about prime-fields).

(include-book "kestrel/axe/evaluator-basic" :dir :system)
(include-book "kestrel/prime-fields/unguarded-defuns" :dir :system)
(include-book "kestrel/arithmetic-light/mod-expt-fast-unguarded" :dir :system)

;; TODO: Add more functions!  Add more bv functions.
(defconst *axe-evaluator-r1cs-fns-and-aliases*
  (append acl2::*axe-evaluator-basic-fns-and-aliases* ;remove some?
          '((add add-unguarded)
            (neg neg-unguarded)
            (sub sub-unguarded)
            (mul mul-unguarded)
            (inv inv-unguarded)
            (div div-unguarded)
            (pow pow-unguarded)
            pos-fix
            (fep fep-unguarded)
            rtl::primep ;; could be dangerous if called on a large prime for which add-io-pairs has not been called
            (acl2::floor acl2::floor-unguarded)
            (acl2::slice acl2::slice-unguarded)
            bitp
            (acl2::mod-expt-fast acl2::mod-expt-fast-unguarded))))

;; Make the evaluator:
(acl2::make-evaluator-simple r1cs *axe-evaluator-r1cs-fns-and-aliases*)
