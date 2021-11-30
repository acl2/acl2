; An R1CS gadget for computing NAND
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/bv/bitnot" :dir :system)
(include-book "kestrel/bv/bitand" :dir :system)
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(defun bitnand (x y)
  (declare (xargs :guard (and (bitp x)
                              (bitp y))))
  (bitnot (acl2::bitand x y)))

;; Make a constraint asserting that var3 = (bitnand var1 var2)
(defund make-nand-constraint (var1 var2 var3)
  (declare (xargs :guard (and (symbolp var1)
                              (symbolp var2)
                              (symbolp var3))))
  ;; (1*var1) * (1*var2) = (1-var3):
  (r1cs-constraint (list `(1 ,var1))
                   (list `(1 ,var2))
                   (list '(1 1) `(-1 ,var3))))

(defthm make-nand-constraint-correct
  (implies (and (r1cs-valuationp valuation prime)
                (valuation-bindsp valuation var1)
                (valuation-bindsp valuation var2)
                (valuation-bindsp valuation var3)
                ;; inputs must be bits:
                (bitp (lookup-equal var1 valuation))
                (bitp (lookup-equal var2 valuation))
                (rtl::primep prime))
           (equal (r1cs-constraint-holdsp (make-nand-constraint var1 var2 var3) valuation prime)
                  (equal (lookup-equal var3 valuation)
                         (bitnand (lookup-equal var1 valuation)
                                  (lookup-equal var2 valuation)))))
  :hints (("Goal" :in-theory (enable make-nand-constraint
                                     r1cs-constraint-holdsp
                                     dot-product
                                     integerp-of-lookup-equal
                                     acl2::bitand-cases))))
