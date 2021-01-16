; An R1CS gadget for asserting that a value is non-zero.
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
;(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; Make an R1CS constraint (in sparse form) that asserts that a is non-zero.
;; This is done by exhibiting a multiplicative inverse of a.  If a were zero,
;; no such value would exist.  At least for now, the inverse must be a
;; variable.  The constraint is of the form: (a-inverse)(a) = 1.
(defund make-nonzero-constraint (a a-inverse)
  (declare (xargs :guard (and (symbolp a)
                              (symbolp a-inverse))))
  (r1cs-constraint
   (list `(1 ,a-inverse)) ;; a vector
   (list `(1 ,a))         ;; b vector
   (list '(1 1))          ;; c vector (just 1)
   ))

(defthm r1cs-constraintp-of-make-nonzero-constraint
  (implies (and (symbolp a)
                (symbolp a-inverse))
           (r1cs::r1cs-constraintp (make-nonzero-constraint a a-inverse)))
  :hints (("Goal" :in-theory (enable make-nonzero-constraint))))

;; This gadget is unusual in that there is an implicit existential quantifier
;; (one must exhibit an inverse of a).

;; Prove that, if we make a nonzero constraint for some vars A and A-INVERSE,
;; then if the constraint holds over a valuation (that binds the vars) the
;; variable A must be nonzero in that valuation.
(defthm make-nonzero-constraint-correct-1
  (implies (and (r1cs-valuationp valuation p)
                (valuation-bindsp valuation a)
                (valuation-bindsp valuation a-inverse)
                (rtl::primep p))
           (implies (r1cs-constraint-holdsp (make-nonzero-constraint a a-inverse) valuation p)
                    (not (equal 0 (lookup-eq a valuation)))))
  :hints (("Goal" :in-theory (enable make-nonzero-constraint
                                     r1cs-constraint-holdsp
                                     integerp-of-lookup-equal
                                     acl2-numberp-of-lookup-equal))))

;; Prove that, given a valuation that binds A, if we can exhibit a variable,
;; A-INVERSE, such that the valuation binds A and A-INVERSE to values that are
;; inverses (which implies that the value of A is not 0), then the non-zero
;; constraint will hold over A and A-INVERSE.
(defthm make-nonzero-constraint-correct-2
  (implies (and (r1cs-valuationp valuation p)
                (valuation-bindsp valuation a)
                (valuation-bindsp valuation a-inverse)
                ;; (not (equal 0 (lookup-eq a valuation))) ; implied by the hyp below
                ;; a and a-inverse are inverses:
                (equal (mul (lookup-eq a valuation)
                            (lookup-eq a-inverse valuation)
                            p)
                       1)
                (rtl::primep p))
           (r1cs-constraint-holdsp (make-nonzero-constraint a a-inverse) valuation p))
  :hints (("Goal" :in-theory (enable make-nonzero-constraint
                                     r1cs-constraint-holdsp
                                     integerp-of-lookup-equal
                                     acl2-numberp-of-lookup-equal))))

;; Prove that, if A is nonzero in some valuation, we can always extend the
;; valuation with a witness value for A's inverse in such a way that the new
;; valuation satisfies the nonzero constraint.  The witness will be 1/A.
(defthm make-nonzero-constraint-correct-2-alt
  (implies (and (r1cs-valuationp valuation p)
                (valuation-bindsp valuation a)
                (not (equal 0 (lookup-eq a valuation)))
                (symbolp a-inverse)
                (not (valuation-bindsp valuation a-inverse)) ; the new var should be fresh
                (rtl::primep p))
           (r1cs-constraint-holdsp (make-nonzero-constraint a a-inverse)
                                   ;; bind the new var A-INVERSE to 1/A:
                                   (acons a-inverse (inv (lookup-eq a valuation) p) valuation)
                                   p))
  :hints (("Goal" :in-theory (enable make-nonzero-constraint
                                     r1cs-constraint-holdsp
                                     integerp-of-lookup-equal
                                     acl2-numberp-of-lookup-equal))))
