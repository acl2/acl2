; Copyright (C) 2015, Regents of the University of Texas
; Written by Cuong Chau and Matt Kaufmann, May, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; cert_param: (uses-acl2r)

(in-package "ACL2")

(include-book "overspill")

; Test with a single extra formal after the first (natural number) formal.

(encapsulate
 ((r (k y) t)) ; classical predicate (necessary for overspill)
 (local (defun r (k y) (declare (ignore k y)) t))
 (defthm r-prop
   (and (r 0 z)
        (implies (and (natp j)
                      (standardp j))
                 (r j z)))))

(overspill r x)

(defthm r-holds-on-i-large
  (let ((n (r-witness x)))
    (and (natp n)
         (i-large n)
         (implies (and (natp m) (<= m n))
                  (r m x))))
  :hints (("Goal" :use r-overspill))
  :rule-classes nil)

; Test as above, but this time use the keyword parameters and also a variable
; different from x.

(overspill r u
           :pred* r*-2
           :witness r-witness-2
           :pred-overspill r-overspill-2)

(defthm r-holds-on-i-large-2
  (let ((n (r-witness-2 u)))
    (and (natp n)
         (i-large n)
         (implies (and (natp m) (<= m n))
                  (r m u))))
  :hints (("Goal" :use ((:instance r-overspill-2
                                   (x u)))))
  :rule-classes nil)

; Test with a list of formals (after the first natural number formal).

(encapsulate
 ((s (k x y) t)) ; classical predicate (necessary for overspill)
 (local (defun s (k x y) (declare (ignore k x y)) t))
 (defthm s-prop
   (and (s 0 x z)
        (implies (and (natp j)
                      (standardp j))
                 (s j x z)))))

(overspill s (x y))

(defthm s-holds-on-i-large
  (let ((n (s-witness x y)))
    (and (natp n)
         (i-large n)
         (implies (and (natp m) (<= m n))
                  (s m x y))))
  :hints (("Goal" :use (:instance s-overspill
                                  (x (list x y)))))
  :rule-classes nil)

