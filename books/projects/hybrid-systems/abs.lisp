; Copyright (C) 2007 by Shant Harutunian
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.


(in-package "ACL2")

(include-book "arith-nsa4")

(defthm abs-realp
  (implies
   (realp x)
   (realp (abs x)))
  :rule-classes :type-prescription)

(defthm abs-non-neg-thm
  (implies
   (and
    (realp x)
    (<= 0 x))
   (equal (abs x)
          x)))

(defthm abs-neg-thm
  (implies
   (and
    (realp x)
    (< x 0))
   (equal (abs x)
          (- x))))

(defthm abs-pos-*-left-thm
  (implies
   (and
    (realp x)
    (realp y)
    (<= 0 x))
   (equal (abs (* x y))
          (* x (abs y)))))

(defthm abs-pos-*-right-thm
  (implies
   (and
    (realp x)
    (realp y)
    (<= 0 x))
   (equal (abs (* y x))
          (* x (abs y)))))

(defthm abs-neg-*-left-thm
  (implies
   (and
    (realp x)
    (realp y)
    (< x 0))
   (equal (abs (* x y))
          (* (- x) (abs y)))))

(defthm abs-neg-*-right-thm
  (implies
   (and
    (realp x)
    (realp y)
    (< x 0))
   (equal (abs (* y x))
          (* (- x) (abs y)))))

(defthm abs-triangular-inequality-thm
  (implies
   (and
    (realp x)
    (realp y))
   (<= (abs (+ x y))
       (+ (abs x) (abs y))))
  :rule-classes :linear)

(defthm abs-triangular-inequality-3way-thm
  (implies
   (and
    (realp x)
    (realp y)
    (realp z))
   (<= (abs (+ x y z))
       (+ (abs x) (abs y) (abs z)))))

(defthm abs-is-non-neg-thm
  (implies
   (realp x)
   (<= 0 (abs x)))
  :rule-classes :type-prescription)

(defthm abs0-thm
  (implies
   (equal (abs x) 0)
   (equal x 0))
  :rule-classes :forward-chaining)

(defthm abs-*-thm
  (implies
   (and
    (realp x)
    (realp y))
   (equal (abs (* x y)) (* (abs x) (abs y)))))

(defthm abs-<-*-thm
  (implies
   (and
    (realp x)
    (realp y)
    (realp a)
    (<= (abs x) (abs y)))
   (<= (abs (* a x)) (abs (* a y))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable abs <-*-LEFT-CANCEL)
           :use ((:instance pos-factor-<=-thm (x (abs x))
                            (y (abs y))
                            (a (abs a)))
                 (:instance abs-*-thm (x a) (y x))
                 (:instance abs-*-thm (x a) (y y))))))

(defthm abs-limited-thm
  (implies
   (and
    (realp x)
    (i-limited x))
   (i-limited (abs x)))
  :rule-classes ((:rewrite) (:type-prescription)))

(defthm abs-standard-numberp
  (implies
   (and
    (realp x)
    (standard-numberp x))
   (standard-numberp (abs x))))
