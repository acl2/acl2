; An R1CS gadget for selection (if-then-else)
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; Make an R1CS constraint (in sparse form) that asserts that z is equal to x
;; (if b is 1) or to y (if b is 0).  This assumes that b is separately
;; constrained to be a bit.  The constraint is of the form: (b)(y - x) = (y -
;; z). This constraint can be understood by considering the two cases b=1 and
;; b=0.  When b=1, it reduces to (y - x) = (y - z), or z=x.  When b=0, it
;; reduces to 0 = (y - z), or z=y.
(defund make-selection-constraint (b x y z)
  (declare (xargs :guard (and (symbolp b)
                              (symbolp x)
                              (symbolp y)
                              (symbolp z))))
  (r1cs-constraint
   (list `(1 ,b))          ;; a vector
   (list `(1 ,y) `(-1 ,x)) ;; b vector
   (list `(1 ,y) `(-1 ,z)) ;; c vector
   ))

(defthm r1cs-constraintp-of-make-selection-constraint
  (implies (and (symbolp b)
                (symbolp x)
                (symbolp y)
                (symbolp z))
           (r1cs::r1cs-constraintp (make-selection-constraint b x y z)))
  :hints (("Goal" :in-theory (enable make-selection-constraint))))

;; Prove that, if we make a selection constraint for some vars b, x, y, and z,
;; then the constraint holds over a valuation (that binds the vars) iff the
;; values of the variables satisfy: z = (if b then x else y).  The value of b
;; in the valuation must be a bit.
(defthm make-selection-constraint-correct
  (implies (and (r1cs-valuationp valuation p)
                (valuation-bindsp valuation b)
                (valuation-bindsp valuation x)
                (valuation-bindsp valuation y)
                (valuation-bindsp valuation z)
                (bitp (lookup-eq b valuation))
                (rtl::primep p))
           (equal (r1cs-constraint-holdsp (make-selection-constraint b x y z) valuation p)
                  (equal (lookup-eq z valuation)
                         (if (equal 1 (lookup-eq b valuation))
                             (lookup-eq x valuation)
                           (lookup-eq y valuation)))))
  :hints (("Goal" :in-theory (enable make-selection-constraint
                                     r1cs-constraint-holdsp
                                     integerp-of-lookup-equal
                                     acl2-numberp-of-lookup-equal))))
