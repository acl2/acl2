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

(include-book "merge") ;BOZO yuck
(local (include-book "add3-proofs"))

(defund add3-measure (x y z)
  (acl2-count (+ x y z)))

(defthm add3-1
  (implies (and (integerp x)
                (> x 0))
           (and (>= (fl (/ x 2)) 0)
                (< (fl (/ x 2)) x)))
  :rule-classes ())

(include-book "land0")
(include-book "lior0")
(include-book "lxor0")

(in-theory (enable bits-tail)) ;BOZO

(defthm add-3-original
  (implies (and (not (zp n))
                (bvecp x n)
                (bvecp y n)
                (bvecp z n))
           (equal (+ x y z)
                  (+ (lxor0 x (lxor0 y z n) n)
                     (* 2 (lior0 (land0 x y n)
                                (lior0 (land0 x z n)
                                      (land0 y z n)
                                      n)
                                n)))))
  :rule-classes ())

(defthm add-2-original
  (implies (and (not (zp n))
                (bvecp x n)
                (bvecp y n))
           (equal (+ x y)
                  (+ (lxor0 x y n)
                     (* 2 (land0 x y n)))))
  :rule-classes ())
