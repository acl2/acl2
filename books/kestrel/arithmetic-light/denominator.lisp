; A lightweight book about the built-in function denominator.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../../arithmetic/rationals"))

(defthm denominator-when-integerp
  (implies (integerp x)
           (equal (denominator x)
                  1))
  :hints (("Goal" :in-theory (enable numerator))))

(defthm equal-of-1-and-denominator
  (equal (equal 1 (denominator x))
         (integerp (rfix x))))

(defthm denominator-of-/-when-integerp
  (implies (integerp x)
           (equal (denominator (/ x))
                  (if (equal x 0)
                      1 ; the denominator of 0 is 1
                    (abs x))))
  :hints (("Goal" :use ((:instance rational-implies2 (x (/ x)))
                        (:instance numerator-/x))
           :in-theory (disable numerator-/x
                               rational-implies2
                               *-r-denominator-r
                               numerator-when-integerp))))

(defthm denominator-of--
  (implies (rationalp x)
           (equal (denominator (- x))
                  (denominator x))))

(local (include-book "../../arithmetic/mod-gcd"))

(defthm <=-of-denominator-of-*-of-/
  (implies (and (integerp i)
                (posp j))
           (<= (denominator (* i (/ j))) j))
  :hints (("Goal" :use (:instance least-numerator-denominator-<= (n i) (d j))
           :in-theory (disable least-numerator-denominator-<=))))
