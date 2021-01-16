; An R1CS gadget for conditional equality
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
(local (include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; Make an R1CS constraint (in sparse form) that asserts that either a=0 or
;; b=c.  This is the same as saying that, if a is non-zero, then b=c.  The
;; constraint is of the form: (a)(b - c) = 0.  Our standard rules about prime
;; fields, such as equal-of-0-and-mul and equal-of-0-and-add-of-neg-arg2,
;; should suffice to handle these constraints when expressed in terms of
;; prime-field operations.
(defund make-conditional-equality-constraint (a b c)
  (declare (xargs :guard (and (symbolp a)
                              (symbolp b)
                              (symbolp c))))
  (r1cs-constraint
   (list `(1 ,a))          ;; a vector
   (list `(1 ,b) `(-1 ,c)) ;; b vector
   '()                     ;; c vector (just zero)
   ))

(defthm r1cs-constraintp-of-make-conditional-equality-constraint
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp c))
           (r1cs::r1cs-constraintp (make-conditional-equality-constraint a b c)))
  :hints (("Goal" :in-theory (enable make-conditional-equality-constraint))))

;; Prove that, if we make a conditional-equality constraint for some vars a, b,
;; and c, then the constraint holds over a valuation (that binds the vars) iff
;; either the value of a is 0 or the value of b equals the value of c.
(defthm make-conditional-equality-constraint-correct
  (implies (and (r1cs-valuationp valuation p)
                (valuation-bindsp valuation a)
                (valuation-bindsp valuation b)
                (valuation-bindsp valuation c)
                (rtl::primep p))
           (equal (r1cs-constraint-holdsp (make-conditional-equality-constraint a b c) valuation p)
                  (or (equal (lookup-eq a valuation) 0)
                      (equal (lookup-eq b valuation)
                             (lookup-eq c valuation)))))
  :hints (("Goal" :in-theory (enable make-conditional-equality-constraint
                                     r1cs-constraint-holdsp
                                     integerp-of-lookup-equal
                                     acl2-numberp-of-lookup-equal))))
