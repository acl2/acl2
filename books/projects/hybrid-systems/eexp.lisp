; Copyright (C) 2007 by Shant Harutunian
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "arith-nsa4")

(defstub eexp (x) t)

(defaxiom eexp-type
  (implies
   (realp x)
   (and
    (<= 0 (eexp x))
    (realp (eexp x))))
  :rule-classes :type-prescription)

(defaxiom eexp-standard-thm
  (implies
   (and
    (realp x)
    (standard-numberp x))
   (standard-numberp (eexp x)))
  :rule-classes :type-prescription)

(defaxiom eexp-standard-part-thm
  (implies
   (and
    (realp x)
    (i-limited x))
   (equal (standard-part (eexp x))
          (eexp (standard-part x)))))

(defaxiom eexp-i-limited-thm
  (implies
   (and
    (realp x)
    (i-limited x))
   (i-limited (eexp x)))
  :rule-classes ((:type-prescription) (:rewrite)))

(defaxiom eexp-0
  (equal (eexp 0)
         1))

(defaxiom eexp-monotone
  (implies
   (and
    (realp x)
    (realp y)
    (< x y))
   (< (eexp x) (eexp y))))

(defaxiom eexp-pos-arg
  (implies
   (and
    (realp x)
    (< 0 x))
   (< 1 (eexp x)))
  :rule-classes ((:linear) (:type-prescription)))

(defaxiom eexp-neg-arg
  (implies
   (and
    (realp x)
    (< x 0))
   (< (eexp x) 1))
  :rule-classes :linear)

(defaxiom 1+x-<=eexp-thm
  (implies
   (and
    (realp x)
    (<= 0 x))
   (<= (+ 1 x)
       (eexp x)))
  :rule-classes :linear)

(defaxiom eexp-plus-thm
  (implies
   (and
    (realp x)
    (realp y))
   (equal (* (eexp x) (eexp y))
          (eexp (+ x y)))))

(defthm eexp-plus-thm-3way
  (implies
   (and
    (realp x)
    (realp y)
    (realp z))
   (equal (* (eexp x) (eexp y) z)
          (* (eexp (+ x y)) z))))
