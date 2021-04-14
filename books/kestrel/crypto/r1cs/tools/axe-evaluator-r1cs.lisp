; An evaluator supporting R1CS Axe reasoning
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; A simple version of the Axe evaluator with verified guards and without skip-proofs.

(include-book "kestrel/axe/evaluator-basic" :dir :system)
(include-book "kestrel/prime-fields/unguarded-defuns" :dir :system)

;; TODO: Consider adding primep (now that we have add-io-pairs), but we'd have to ensure it's only called on known primes.
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
            bitp)))

;; Make the evaluator:
(acl2::make-evaluator-simple axe-evaluator-r1cs *axe-evaluator-r1cs-fns-and-aliases*)
