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

;These rules may cause case splits, but that's sort of the point.

(local (include-book "product-proofs"))

(defthm product-less-than-zero
  (implies (case-split (or (not (complex-rationalp x))
                           (not (complex-rationalp y)))) ;can't gen: (* #C(-1 9) #C(-1 9))=#c(-80 -18)
           (equal (< (* x y) 0)
                  (if (< x 0)
                      (< 0 y)
                    (if (equal 0 x)
                        nil
                      (if (not (acl2-numberp x))
                          nil
                        (< y 0)))))))


#|
(defthm product-less-than-zero
  (implies (case-split (not (complex-rationalp x))) ;can't gen: (* #C(-1 9) #C(-1 9))=#c(-80 -18)
           (equal (< (* x y) 0)
                  (if (< x 0)
                      (< 0 y)
                    (if (equal 0 x)
                        nil
                      (if (not (acl2-numberp x))
                          nil
                        (< y 0)))))))

;this use hint shouldn't be needed
(defthm product-less-than-zero-2
  (implies (case-split (not (complex-rationalp y))) ;(case-split (rationalp y))
           (equal (< (* x y) 0)
                  (or (and (< x 0) (< 0 y))
                      (and (< y 0) (< 0 x))))))
|#

;combine the next two by case-splittin on an OR?
(defthm product-greater-than-zero
  (implies (case-split (not (complex-rationalp y)))
           (equal (< 0 (* x y))
                  (or (and (< 0 x) (< 0 y))
                      (and (< y 0) (< x 0))))))

(defthm product-greater-than-zero-2
  (implies (case-split (not (complex-rationalp x)))
           (equal (< 0 (* x y))
                  (or (and (< 0 x) (< 0 y))
                      (and (< y 0) (< x 0))))))

;could write the conclusion using an OR...
(defthm product-equal-zero
  (equal (equal 0 (* x y))
         (if (not (acl2-numberp x))
             t
           (if (not (acl2-numberp y))
               t
             (if (equal 0 x)
                 t
               (equal 0 y))))))

