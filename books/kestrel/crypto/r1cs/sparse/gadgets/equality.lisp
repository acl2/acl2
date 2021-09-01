; An R1CS gadget for an performing an equality check
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

;; Make a constraint asserting that var1 = var2.
(defund make-equality-constraint (var1 var2)
  (declare (xargs :guard (and (symbolp var1)
                              (symbolp var2))))
  ;; (1*1) * (1*var1) = (1*var2):
  (r1cs-constraint (list `(1 1))
                   (list `(1 ,var1))
                   (list `(1 ,var2))))

(defthm make-equality-constraint-correct
  (implies (and (r1cs-valuationp valuation prime)
                (valuation-bindsp valuation var1)
                (valuation-bindsp valuation var2)
                (rtl::primep prime))
           (equal (r1cs-constraint-holdsp (make-equality-constraint var1 var2) valuation prime)
                  (equal (lookup-equal var1 valuation)
                         (lookup-equal var2 valuation))))
  :hints (("Goal" :in-theory (enable make-equality-constraint
                                     r1cs-constraint-holdsp
                                     dot-product
                                     integerp-of-lookup-equal))))
