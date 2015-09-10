; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

; cert_param: (non-acl2r)

(local (include-book "predicate"))

(defthm rationalp-product-when-one-arg-is-rational
  (implies (and (rationalp x)
                (case-split (not (equal x 0)))
                (case-split (acl2-numberp y))
                )
           (and (equal (rationalp (* x y))
                       (rationalp y))
                (equal (rationalp (* y x))
                       (rationalp y)))))

(defthm rationalp-sum-when-one-arg-is-rational
  (implies (and (rationalp x)
                (case-split (acl2-numberp y)))
           (and (equal (rationalp (+ x y))
                       (rationalp y))
                (equal (rationalp (+ y x))
                       (rationalp y)))))

(defthm rationalp-unary-divide
  (implies (case-split (acl2-numberp x))
           (equal (rationalp (/ x))
                  (rationalp x))))





#|

(defthm rationalp-*-when-first-factor-is-rat
  (implies (and (rationalp x)
                (case-split (not (equal x 0))) ;if x is 0, then...
                )
           (equal (rationalp (* x y))
                  (not (complex-rationalp y)))))

(thm
  (implies (and (rationalp x)
                (case-split (not (equal x 0))) ;if x is 0, then...
                )
           (equal (rationalp (* x y))
                  (not (complex-rationalp y)))))

|#


;try

(defthm rationalp-product
  (implies (and (case-split (not (complex-rationalp x)))
                (case-split (not (complex-rationalp y))))
           (rationalp (* x y))))
