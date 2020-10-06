; A lightweight book about the built-in function numerator.
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "denominator"))
(local (include-book "../../arithmetic/rationals"))

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

(defthm numerator-of-/-when-integerp
  (implies (integerp x)
           (equal (numerator (/ x))
                  (signum x))))

(defthm numerator-of--
  (equal (numerator (- x))
         (- (numerator x))))

;move
(local
 (defthmd not-rationalp-of--
   (implies (and (not (rationalp x))
                 (complex-rationalp x))
            (not (rationalp (- x))))))

(defthm numerator-of-+-of---and--
  (equal (numerator (+ (- x) (- y)))
         (- (numerator (+ x y))))
  :hints (("Goal" :use ((:instance not-rationalp-of-- (x (+ x y)))
                        (:instance numerator-of-- (x (+ x y))))
           :in-theory (disable numerator-of--))))

(local (include-book "../../arithmetic/mod-gcd"))

(defthm <=-of-numerator-of-*-of-/
  (implies (and (natp i)
                (posp j))
           (<= (numerator (* i (/ j)))
               i))
  :hints (("Goal" :use (:instance least-numerator-denominator-<= (n i) (d j))
           :in-theory (disable least-numerator-denominator-<=))))

(defthm numerator-of-*-of---arg2
  (equal (numerator (* x (- y)))
         (- (numerator (* x y))))
  :hints (("Goal" :use (:instance numerator-of-- (x (* x y)))
           :in-theory (disable numerator-of--))))
