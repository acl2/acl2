; Centaur Bitops Library
; Copyright (C) 2018 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

; Original authors: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "arithmetic/top" :dir :system)
(include-book "std/util/bstar" :dir :system)

(local (in-theory (disable floor)))

(local (defthm numerator-of-x-minus-1
         (implies (rationalp x)
                  (equal (numerator (+ -1 x))
                         (- (numerator x) (denominator x))))
         :hints (("goal" :use ((:instance rational-implies2
                                (x (+ -1 x))))
                  :in-theory (disable rational-implies2)))))

(local (defthm numerator-of-x-plus-1
         (implies (rationalp x)
                  (equal (numerator (+ 1 x))
                         (+ (numerator x) (denominator x))))
         :hints (("goal" :use ((:instance rational-implies2
                                (x (+ +1 x))))
                  :in-theory (disable rational-implies2)))))

(local (defthm numerator-<-denominator
         (implies (rationalp x)
                  (iff (< (numerator x) (denominator x))
                       (< x 1)))
         :hints (("goal" :use ((:instance rational-implies2))
                  :in-theory (disable rational-implies2
                                      *-r-denominator-r
                                      equal-*-/-1)))))

(defthm floor-of-nonneg-operands-when-less
  (implies (and (rationalp x)
                (<= 0 x)
                (rationalp y)
                (< x y))
           (equal (floor x y) 0))
  :hints(("Goal" :in-theory (enable floor))
         (and stable-under-simplificationp
              '(:cases ((< (/ x y) 1))))))


(defthm mod-of-nonneg-operands-when-less
  (implies (and (rationalp x)
                (<= 0 x)
                (rationalp y)
                (< x y))
           (equal (mod x y) x)))

(defthm floor-of-nonneg-operands-when-not-less
  (implies (and (rationalp x)
                (rationalp y)
                (< 0 y)
                (<= y x))
           (equal (floor x y)
                  (+ 1 (floor (- x y) y))))
  :hints(("Goal" :in-theory (enable floor))))


(defthm mod-of-nonneg-operands-when-not-less
  (implies (and (rationalp x)
                (rationalp y)
                (< 0 y)
                (<= y x))
           (equal (mod x y)
                  (mod (- x y) y))))



(local
 (defthmd floor-redef-when-x-negative-lemma
   (implies (and (and (rationalp x) (< x 0) (rationalp y) (< 0 y))
                 (not (integerp (/ x y))))
            (equal (floor x y)
                   (+ -1 (- (floor (- x) y)))))
   :hints(("Goal" :in-theory (enable floor)))))

(defthm floor-redef-when-x-negative
   (implies (and (rationalp x) (< x 0) (rationalp y) (< 0 y))
            (equal (floor x y)
                   (+ -1 (floor (+ x y) y))))
   :hints(("Goal" :in-theory (e/d (floor-redef-when-x-negative-lemma))
           :cases ((integerp (/ x y))))
          (and stable-under-simplificationp
               '(:cases ((< (+ x y) 0)
                         (equal x (- y)))))
          (and stable-under-simplificationp
               '(:in-theory (enable floor)))
          (and stable-under-simplificationp
               '(:cases ((>= (* x (/ y)) -1))))
          )
   :otf-flg t)

(defthm mod-redef-when-x-negative
   (implies (and (rationalp x) (< x 0) (rationalp y) (< 0 y))
            (equal (mod x y)
                   (mod (+ x y) y)))
   :hints(("Goal" :in-theory (enable mod))))

(defthm floor-redef-when-y-negative
  (implies (< y 0)
           (equal (floor x y)
                  (floor (- x) (- y))))
  :hints(("Goal" :in-theory (enable floor))))

(defthm mod-redef-when-y-negative
  (implies (< y 0)
           (equal (mod x y)
                  (- (mod (- x) (- y)))))
   :hints(("Goal" :in-theory (enable mod))))

(defthm floor-when-y-is-0
  (equal (floor x 0) 0)
  :hints(("Goal" :in-theory (enable floor))))

(defthm mod-when-y-is-0
  (equal (mod x 0) (fix x)))


(defthmd floor-redef-full
  (implies (and (rationalp x) (rationalp y))
           (equal (floor x y)
                  (b* (((when (eql y 0)) 0)
                       ((mv x y) (if (< y 0)
                                     (mv (- x) (- y))
                                   (mv x y))))
                    (if (< x 0)
                        (+ -1 (floor (+ x y) y))
                      (if (< x y)
                          0
                        (+ 1 (floor (- x y) y)))))))
  :hints(("Goal" :in-theory (disable floor)))
  :rule-classes :definition)


(defthmd mod-redef-full
  (implies (and (rationalp x) (rationalp y))
           (equal (mod x y)
                  (b* (((when (eql y 0)) x)
                       ((mv x y neg) (if (< y 0)
                                         (mv (- x) (- y) t)
                                       (mv x y nil)))
                       (ans
                        (if (< x 0)
                            (mod (+ x y) y)
                          (if (< x y)
                              x
                            (mod (- x y) y)))))
                    (if neg (- ans) ans))))
  :hints(("Goal" :in-theory (e/d (floor-redef-full) (floor))))
  :rule-classes :definition)


(local (defthm floor-negative
         (implies (and (< x 0) (< 0 y)
                       (rationalp x) (rationalp y))
                  (< (floor x y) 0))
         :hints(("Goal" :in-theory (enable floor)))
         :rule-classes :linear))

(local (defthm floor-negative-lemma
         (implies (and (< x 0) (< 0 y)
                       (rationalp x) (rationalp y))
                  (< (floor (+ x y) y) 1))
         :hints (("goal" :use floor-negative))
         :rule-classes :linear))

(local (defthm floor-nonnegative
         (implies (and (<= 0 x) (< 0 y)
                       (rationalp x) (rationalp y))
                  (<= 0 (floor x y)))
         :hints(("Goal" :in-theory (enable floor)))
         :rule-classes :linear))



(defun floor/mod-nats-ind (x y)
  (declare (xargs :measure (nfix (floor (nfix x) (nfix y)))))
  (b* ((x (nfix x))
       (y (nfix y))
       ((when (eql y 0)) 0)
       ((when (< x y)) 0))
    (floor/mod-nats-ind (- x y) y)))

(defun floor-mod-ind (x y)
  (declare (xargs :measure (abs (floor (rfix x) (rfix y)))))
  (b* ((x (rfix x))
       (y (rfix y))
       ((when (eql y 0)) 0)
       ((mv x y) (if (< y 0) (mv (- x) (- y)) (mv x y)))
       ((when (< x 0))
        (floor-mod-ind (+ x y) y))
       ((when (< x y)) 0))
    (floor-mod-ind (- x y) y)))


       




