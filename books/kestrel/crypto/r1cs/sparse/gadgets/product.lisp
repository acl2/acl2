; An R1CS gadget for computing a product
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;; Make a constraint asserting that a * b = c
(defund make-product-constraint (a b c)
  (declare (xargs :guard (and (symbolp a)
                              (symbolp b)
                              (symbolp c))))
  (r1cs-constraint (list `(1 ,a))
                   (list `(1 ,b))
                   (list `(1 ,c))))

(defthm r1cs-constraintp-of-make-product-constraint
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp c))
           (r1cs-constraintp (make-product-constraint a b c)))
  :hints (("Goal" :in-theory (enable make-product-constraint))))

(defthm make-product-constraint-correct
  (implies (and (r1cs-valuationp valuation prime)
                (force (valuation-bindsp valuation a))
                (force (valuation-bindsp valuation b))
                (force (valuation-bindsp valuation c))
                (rtl::primep prime))
           (equal (r1cs-constraint-holdsp (make-product-constraint a b c) valuation prime)
                  (equal (mul (lookup-equal a valuation)
                              (lookup-equal b valuation)
                              prime)
                         (lookup-equal c valuation))))
  :hints (("Goal" :in-theory (enable make-product-constraint
                                     r1cs-constraint-holdsp
                                     dot-product
                                     integerp-of-lookup-equal))))
