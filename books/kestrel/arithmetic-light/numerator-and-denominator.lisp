; A new book about numerator and denominator
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book doesn't include any libraries outside arithmetic-light/.
;; TODO: Continue fleshing this out and use it to replace numerator.lisp and denominator.lisp.

(defthm denominator-when-integerp
  (implies (integerp x)
           (equal (denominator x)
                  1))
  :hints (("Goal" :in-theory (enable numerator))))

(defthm equal-of-1-and-denominator
  (equal (equal 1 (denominator x))
         (integerp (rfix x))))

(defthm numerator-when-integerp
  (implies (integerp x)
           (equal (numerator x)
                  x))
  :hints (("Goal" :use (:instance rational-implies2)
           :in-theory (disable rational-implies2))))

(defthm equal-of-numerator-same
  (equal (equal x (numerator x))
         (integerp x)))

(defthm <-of-numerator-and-0
  (equal (< (numerator x) 0)
         (and (rationalp x)
              (< x 0)))
  :hints (("Goal" :cases ((not (rationalp x))
                          (and (rationalp x)
                               (< x 0))))))

(include-book "times-and-divide") ; for equal-of-*-of-/

(defthmd denominator-redef
  (implies (rationalp x)
           (equal (denominator x)
                  (if (equal x 0)
                      1
                    (/ (numerator x) x))))
  :hints (("Goal" :use (:instance rational-implies2)
           :in-theory (disable rational-implies2))))

(local
 (defthm helper
   (implies (and (rationalp x)
                 (not (equal 0 x))
                 )
            (equal (denominator (/ x))
                   (* x (numerator (/ x)))))
   :hints (("Goal" :in-theory (enable denominator-redef)))))

(local
 (defthm helper2
   (implies (and (< 0 x) ; this case
                 (integerp x))
            (equal (numerator (/ x))
                   1))
   :hints (("Goal" :use (:instance lowest-terms
                                   (x (/ x))
                                   (n (numerator (/ x)))
                                   (r 1)
                                   (q x))))))

(defthm <-of-0-and-numerator
  (equal (< 0 (numerator x))
         (and (rationalp x)
              (< 0 x)))
  :hints (("Goal" :use (:instance rational-implies2)
           :cases ((not (rationalp x))
                   (and (rationalp x) (< 0 x)))
           :in-theory (disable rational-implies2))))

(local
 (defthmd *-of--1
  (equal (* -1 x)
         (- x))))

(local
 (defthmd --becomes-*-of--1
  (equal (- x)
         (* -1 x))))

(local
 (defthm *-of---arg1
  (equal (* (- x) y)
         (- (* x y)))
  :hints (("Goal" :in-theory (enable --becomes-*-of--1)))))

(local
 (defthm helper2b
   (implies (and (< x 0) ; this case
                 (integerp x))
            (equal (numerator (/ x))
                   -1))
   :hints (("Goal" :use (:instance lowest-terms
                                   (x (/ x))
                                   (n (- (numerator (/ x))))
                                   (r -1)
                                   (q (- x)))))))

(defthm numerator-of-/-when-integerp
  (implies (integerp x)
           (equal (numerator (/ x))
                  (signum x))))

;; TODO: Next prove numerator-of--.
