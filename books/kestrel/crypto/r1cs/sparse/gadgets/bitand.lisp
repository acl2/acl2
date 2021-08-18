; An R1CS gadget for ANDing two bits
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "product")
(include-book "kestrel/bv/bitand" :dir :system)
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;; Make a constraint asserting that a AND b = c, assuming they are all bits.
(defund make-bitand-constraint (a b c)
  (declare (xargs :guard (and (symbolp a)
                              (symbolp b)
                              (symbolp c))))
  (make-product-constraint a b c))

(defthm r1cs-constraintp-of-make-bitand-constraint
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp c))
           (r1cs-constraintp (make-bitand-constraint a b c)))
  :hints (("Goal" :in-theory (enable make-bitand-constraint))))

(defthm make-bitand-constraint-correct
  (implies (and (r1cs-valuationp valuation prime)
                (force (valuation-bindsp valuation a))
                (force (bitp (lookup-equal a valuation)))
                (force (valuation-bindsp valuation b))
                (force (bitp (lookup-equal b valuation)))
                (force (valuation-bindsp valuation c))
                (rtl::primep prime))
           (equal (r1cs-constraint-holdsp (make-bitand-constraint a b c) valuation prime)
                  (equal (acl2::bitand (lookup-equal a valuation)
                                       (lookup-equal b valuation))
                         (lookup-equal c valuation))))
  :hints (("Goal" :in-theory (enable make-bitand-constraint
                                     bitp))))
