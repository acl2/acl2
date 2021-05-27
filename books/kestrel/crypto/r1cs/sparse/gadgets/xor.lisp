; An R1CS gadget for XORing two bits
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; Make an R1CS constraint (in sparse form) that asserts that C is equal to the
;; xor of bits A and B.  A and B should be separately constrained to be bits.
;; The constraint has the form: (2a)(b)=(a+b-c).
(defund make-bitxor-constraint (a b c)
  (declare (xargs :guard (and (symbolp a)
                              (symbolp b)
                              (symbolp c))))
  (r1cs-constraint
   (list `(2 ,a))                  ;; a vector
   (list `(1 ,b))                  ;; b vector
   (list `(1 ,a) `(1 ,b) `(-1 ,c)) ;; c vector
   ))

(defthm r1cs-constraintp-of-make-bitxor-constraint
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp c))
           (r1cs::r1cs-constraintp (make-bitxor-constraint a b c)))
  :hints (("Goal" :in-theory (enable make-bitxor-constraint))))

;; Prove that, if we make an xor constraint for some vars A, B and C, then the
;; constraint holds over a valuation (that binds the vars) iff the value of C
;; is the XOR of the values of A and B.  The values of A and B in the valuation
;; must be bits.
(defthm make-bitxor-constraint-correct
  (implies (and (r1cs-valuationp valuation p)
                (valuation-bindsp valuation a)
                (valuation-bindsp valuation b)
                (valuation-bindsp valuation c)
                (bitp (lookup-eq a valuation))
                (bitp (lookup-eq b valuation))
                (rtl::primep p)
                (< 2 p))
           (equal (r1cs-constraint-holdsp (make-bitxor-constraint a b c) valuation p)
                  (equal (lookup-eq c valuation)
                         (acl2::bitxor (lookup-eq a valuation)
                                       (lookup-eq b valuation)))))
  :hints (("Goal" :in-theory (enable make-bitxor-constraint
                                     r1cs-constraint-holdsp
                                     integerp-of-lookup-equal
                                     acl2-numberp-of-lookup-equal))))
