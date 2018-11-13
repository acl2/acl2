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

(local (in-theory (disable floor truncate)))

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

(local (defthm numerator-<-0
         (implies (rationalp x)
                  (iff (< (numerator x) 0)
                       (< x 0)))))

(local (defthm integerp-of-divide-when-less
         (implies (and (rationalp x)
                       (rationalp y)
                       (<= 0 x)
                       (< x y))
                  (iff (integerp (* x (/ y)))
                       (equal x 0)))
         :hints ((and stable-under-simplificationp
                      '(:use ((:instance <-*-/-LEFT (a 1))
                              (:instance <-*-/-LEFT (a 0)))
                        :in-theory (disable <-*-/-LEFT
                                            <-UNARY-/-POSITIVE-RIGHT
                                            <-*-0))))))

(defthmd floor-of-nonneg-operands-base-case
  (implies (and (< x y)
                (<= 0 x)
                ;; note: we actually could get away with rationalp of either x
                ;; or y here, but not in most places
                (rationalp x)
                (rationalp y))
           (equal (floor x y) 0))
  :hints(("Goal" :in-theory (enable floor)
          :cases ((rationalp y)))))

(local (in-theory (enable floor-of-nonneg-operands-base-case)))

(defthmd mod-of-nonneg-operands-base-case
  (implies (and (< x y)
                (<= 0 x)
                (rationalp x)
                (rationalp y))
           (equal (mod x y) x)))

(local (in-theory (enable mod-of-nonneg-operands-base-case)))

(defthmd floor-of-nonneg-operands-step
  (implies (and (<= y x)
                (< 0 y)
                (rationalp x)
                (rationalp y))
           (equal (floor x y)
                  (+ 1 (floor (- x y) y))))
  :hints(("Goal" :in-theory (enable floor))
         (and stable-under-simplificationp
              '(:cases ((<= 0 (* x (/ y))))))))

(local (in-theory (enable floor-of-nonneg-operands-step)))


(defthmd mod-of-nonneg-operands-step
  (implies (and (<= y x)
                (< 0 y)
                (rationalp x)
                (rationalp y))
           (equal (mod x y)
                  (mod (- x y) y))))

(local (in-theory (enable mod-of-nonneg-operands-step)))



(local
 (defthmd floor-redef-when-x-negative-lemma
   (implies (and (and (rationalp x) (< x 0) (rationalp y) (< 0 y))
                 (not (integerp (/ x y))))
            (equal (floor x y)
                   (+ -1 (- (floor (- x) y)))))
   :hints(("Goal" :in-theory (enable floor)))))

(defthmd floor-of-x-negative-step
   (implies (and (< x 0) (< 0 y) (rationalp x) (rationalp y))
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

(local (in-theory (enable floor-of-x-negative-step)))

(defthmd mod-of-x-negative-step
   (implies (and (< x 0) (< 0 y) (rationalp x) (rationalp y))
            (equal (mod x y)
                   (mod (+ x y) y)))
   :hints(("Goal" :in-theory (enable mod))))

(defthmd floor-of-y-negative-invert
  (implies (< y 0)
           (equal (floor x y)
                  (floor (- x) (- y))))
  :hints(("Goal" :in-theory (enable floor))))

(local (in-theory (enable floor-of-y-negative-invert)))

(defthmd mod-of-y-negative-invert
  (implies (< y 0)
           (equal (mod x y)
                  (- (mod (- x) (- y)))))
   :hints(("Goal" :in-theory (enable mod))))

(local (in-theory (enable mod-of-y-negative-invert)))

(defthmd floor-of-y-negative-step
  (implies (and (< 0 x) (< y 0) (rationalp x) (rationalp y))
           (equal (floor x y)
                  (+ -1 (floor (+ x y) y)))))

(defthmd floor-of-negative-operands-base-case
  (implies (and (< y x) (< x 0) (rationalp x) (rationalp y))
           (equal (floor x y) 0)))

(defthmd floor-of-negative-operands-step
  (implies (and (<= x y) (< y 0) (rationalp x) (rationalp y))
           (equal (floor x y)
                  (+ 1 (floor (- x y) y)))))

(defthmd mod-of-y-negative-step
  (implies (and (< 0 x) (< y 0) (rationalp x) (rationalp y))
           (equal (mod x y)
                  (mod (+ x y) y))))

(defthmd mod-of-negative-operands-base-case
  (implies (and (< y x) (< x 0) (rationalp x) (rationalp y))
           (equal (mod x y) x)))

(defthmd mod-of-negative-operands-step
  (implies (and (<= x y) (< y 0) (rationalp x) (rationalp y))
           (equal (mod x y)
                  (mod (- x y) y))))


(defthm floor-when-y-is-0
  (equal (floor x 0) 0)
  :hints(("Goal" :in-theory (enable floor))))

(defthm mod-when-y-is-0
  (equal (mod x 0) (fix x)))

(defthmd floor-redef
  (implies (and (rationalp x) (rationalp y))
           (equal (floor x y)
                  (cond ((eql y 0) 0)
                        ((< 0 y)
                         (cond ((< x 0) (+ -1 (floor (+ x y) y)))
                               ((< x y) 0)
                               (t (+ 1 (floor (- x y) y)))))
                        (t (cond ((> x 0) (+ -1 (floor (+ x y) y)))
                                 ((> x y) 0)
                                 (t (+ 1 (floor (- x y) y))))))))
  :rule-classes :definition)


(defthmd mod-redef
  (implies (and (rationalp x) (rationalp y))
           (equal (mod x y)
                  (cond ((eql y 0) x)
                        ((< 0 y)
                         (cond ((< x 0) (mod (+ x y) y))
                               ((< x y) x)
                               (t (mod (- x y) y))))
                        (t (cond ((> x 0) (mod (+ x y) y))
                                 ((> x y) x)
                                 (t (mod (- x y) y)))))))
  :hints(("Goal" :in-theory (enable floor-redef)))
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
       ((when (< 0 y))
        (cond ((< x 0) (floor-mod-ind (+ x y) y))
              ((< x y) x)
              (t (floor-mod-ind (- x y) y)))))
    (cond ((> x 0) (floor-mod-ind (+ x y) y))
          ((> x y) x)
          (t (floor-mod-ind (- x y) y)))))








(defthmd truncate-of-nonneg-operands-base-case
  (implies (and (< x y)
                (<= 0 x)
                ;; note: we actually could get away with rationalp of either x
                ;; or y here, but not in most places
                (rationalp x)
                (rationalp y))
           (equal (truncate x y) 0))
  :hints(("Goal" :in-theory (enable truncate)
          :cases ((rationalp y)))))

(local (in-theory (enable truncate-of-nonneg-operands-base-case)))

(defthmd rem-of-nonneg-operands-base-case
  (implies (and (< x y)
                (<= 0 x)
                (rationalp x)
                (rationalp y))
           (equal (rem x y) x)))

(local (in-theory (enable rem-of-nonneg-operands-base-case)))

(defthmd truncate-of-nonneg-operands-step
  (implies (and (<= y x)
                (< 0 y)
                (rationalp x)
                (rationalp y))
           (equal (truncate x y)
                  (+ 1 (truncate (- x y) y))))
  :hints(("Goal" :in-theory (enable truncate))
         (and stable-under-simplificationp
              '(:cases ((<= 0 (* x (/ y))))))))

(local (in-theory (enable truncate-of-nonneg-operands-step)))


(defthmd rem-of-nonneg-operands-step
  (implies (and (<= y x)
                (< 0 y)
                (rationalp x)
                (rationalp y))
           (equal (rem x y)
                  (rem (- x y) y))))

(local (in-theory (enable rem-of-nonneg-operands-step)))



(defthmd truncate-of-x-negative-invert
  (implies (and (< x 0) (< 0 y) (rationalp x) (rationalp y))
           (equal (truncate x y)
                  (- (truncate (- x) y))))
  :hints(("Goal" :in-theory (enable truncate))))

(local (in-theory (enable truncate-of-x-negative-invert)))

(defthmd truncate-of-y-negative-invert
  (implies (and (< y 0) (rationalp x) (rationalp y))
           (equal (truncate x y)
                  (truncate (- x) (- y))))
  :hints(("Goal" :in-theory (enable truncate))))

(local (in-theory (enable truncate-of-y-negative-invert)))

(defthmd rem-of-x-negative-invert
  (implies (and (< x 0) (< 0 y) (rationalp x) (rationalp y))
           (equal (rem x y)
                  (- (rem (- x) y))))
  :hints(("Goal" :in-theory (enable rem))))

(local (in-theory (enable rem-of-x-negative-invert)))

(defthmd rem-of-y-negative-invert
  (implies (and (< y 0) (rationalp x) (rationalp y))
           (equal (rem x y)
                  (- (rem (- x) (- y)))))
  :hints(("Goal" :in-theory (enable rem))))

(local (in-theory (enable rem-of-y-negative-invert)))

;; (defthmd truncate-of-x-negative-base-case
;;   (implies (and (< (- y) x) (< 0 y) (<= x 0) (rationalp x) (rationalp y))
;;            (equal (truncate x y) 0))
;;   :hints (("Goal" :cases ((equal x 0)))))

(defthmd truncate-of-y-positive-base-case
  (implies (and (< (- y) x) (< x y) (< 0 y) (rationalp x) (rationalp y))
           (equal (truncate x y) 0))
  :hints (("goal" :cases ((< x 0) (equal x 0)))))

(defthmd truncate-of-x-negative-step
  (implies (and (< 0 y) (<= x (- y)) (rationalp x) (rationalp y))
           (equal (truncate x y)
                  (+ -1 (truncate (+ x y) y))))
  :hints (("goal" :cases ((equal (+ x y) 0)
                          (< 0 (+ x y))))))

;; (defthmd rem-of-x-negative-base-case
;;   (implies (and (< (- y) x) (< 0 y) (<= x 0) (rationalp x) (rationalp y))
;;            (equal (rem x y) x))
;;   :hints(("Goal" :in-theory (enable truncate-of-x-negative-base-case))))

(defthmd rem-of-y-positive-base-case
  (implies (and (< (- y) x) (< x y) (< 0 y) (rationalp x) (rationalp y))
           (equal (rem x y) x))
  :hints(("Goal" :in-theory (enable truncate-of-y-positive-base-case))))

(defthmd rem-of-x-negative-step
  (implies (and (< 0 y) (<= x (- y)) (rationalp x) (rationalp y))
           (equal (rem x y)
                  (rem (+ x y) y)))
  :hints(("Goal" :in-theory (e/d (truncate-of-x-negative-step)
                                 (rem-of-x-negative-invert)))))

(defthmd truncate-of-y-negative-base-case
  (implies (and (< x (- y)) (< y x) (< y 0) (rationalp x) (rationalp y))
           (equal (truncate x y) 0))
  :hints (("goal" :cases ((equal x 0) (< x 0)))))

(defthmd truncate-of-y-negative-step
  (implies (and (<= (- y) x) (< y 0) (rationalp x) (rationalp y))
           (equal (truncate x y)
                  (+ -1 (truncate (+ x y) y))))
  :hints (("goal" :cases ((equal (- y) x)))))


(defthmd rem-of-y-negative-base-case
  (implies (and (< x (- y)) (< y x) (< y 0) (rationalp x) (rationalp y))
           (equal (rem x y) x))
  :hints(("Goal" :in-theory (e/d (truncate-of-y-negative-base-case)
                                 (rem-of-y-negative-invert)))))

(defthmd rem-of-y-negative-step
  (implies (and (<= (- y) x) (< y 0) (rationalp x) (rationalp y))
           (equal (rem x y)
                  (rem (+ x y) y)))
  :hints(("Goal" :in-theory (e/d (truncate-of-y-negative-step)
                                 (rem-of-y-negative-invert)))))


;; (defthmd truncate-of-negative-operands-base-case
;;   (implies (and (< y x) (< y 0) (< x 0) (rationalp x) (rationalp y))
;;            (equal (truncate x y) 0)))

(defthmd truncate-of-negative-operands-step
  (implies (and (<= x y) (< y 0) (rationalp x) (rationalp y))
           (equal (truncate x y)
                  (+ 1 (truncate (- x y) y)))))

;; (defthmd rem-of-negative-operands-base-case
;;   (implies (and (< y x) (< y 0) (< x 0) (rationalp x) (rationalp y))
;;            (equal (rem x y) x)))

(defthmd rem-of-negative-operands-step
  (implies (and (<= x y) (< y 0) (rationalp x) (rationalp y))
           (equal (rem x y)
                  (rem (- x y) y))))



(defthm truncate-when-y-is-0
  (equal (truncate x 0) 0)
  :hints(("Goal" :in-theory (enable truncate))))

(defthm rem-when-y-is-0
  (equal (rem x 0) (fix x)))

(defthmd truncate-redef
  (implies (and (rationalp x) (rationalp y))
           (equal (truncate x y)
                  (cond ((eql y 0) 0)
                        ((< 0 y)
                         (cond ((<= x (- y)) (+ -1 (truncate (+ x y) y)))
                               ((< x y) 0)
                               (t (+ 1 (truncate (- x y) y)))))
                        (t (cond ((>= x (- y)) (+ -1 (truncate (+ x y) y)))
                                 ((> x y) 0)
                                 (t (+ 1 (truncate (- x y) y))))))))
  :hints (("goal" :in-theory (e/d (truncate-of-y-positive-base-case
                                    truncate-of-x-negative-step
                                    truncate-of-y-negative-base-case
                                    truncate-of-y-negative-step
                                    truncate-of-negative-operands-step)
                                  (truncate-of-x-negative-invert
                                   truncate-of-y-negative-invert))))
  :rule-classes :definition)

(defthmd rem-redef
  (implies (and (rationalp x) (rationalp y))
           (equal (rem x y)
                  (cond ((eql y 0) x)
                        ((< 0 y)
                         (cond ((<= x (- y)) (rem (+ x y) y))
                               ((< x y) x)
                               (t (rem (- x y) y))))
                        (t (cond ((>= x (- y)) (rem (+ x y) y))
                                 ((> x y) x)
                                 (t (rem (- x y) y)))))))
  :hints (("goal" :in-theory (e/d (rem-of-y-positive-base-case
                                    rem-of-x-negative-step
                                    rem-of-y-negative-base-case
                                    rem-of-y-negative-step
                                    rem-of-negative-operands-step)
                                  (rem-of-x-negative-invert
                                   rem-of-y-negative-invert
                                   rem))))
  :rule-classes :definition)


(local (defthm nonneg-int-quotient-equal-0
         (equal (equal (nonnegative-integer-quotient i j) 0)
                (or (equal (nfix j) 0)
                    (< (ifix i) (nfix j))))
         :hints(("Goal" :in-theory (enable nonnegative-integer-quotient)))))

(local (defthm natp-nonneg-int-quotient
         (natp (nonnegative-integer-quotient i j))
         :rule-classes :type-prescription))

(local (defthm truncate-negative
         (implies (and (< 0 y) (<= x (- y))
                       (rationalp x) (rationalp y))
                  (< (truncate x y) 0))
         :hints(("Goal" :in-theory (e/d (truncate) (numerator-<-denominator
                                                    <-*-/-right))
                 :use ((:instance numerator-<-denominator
                        (x (* (- x) (/ y))))
                       (:instance <-*-/-right
                        (a -1)))))
         :rule-classes :linear))

(local (defthm truncate-nonnegative
         (implies (and (<= 0 x) (< 0 y)
                       (rationalp x) (rationalp y))
                  (<= 0 (truncate x y)))
         :hints(("Goal" :in-theory (enable truncate)))
         :rule-classes :linear))

(local (defthm truncate-negative-lemma
         (implies (and (< x 0) (< 0 y)
                       (rationalp x) (rationalp y))
                  (< (truncate (+ x y) y) 1))
         :hints (("goal" :use truncate-negative
                  :cases ((< (+ x y) 0)
                          (equal (+ x y) 0))))
         :rule-classes :linear))



(defun truncate/rem-nats-ind (x y)
  (declare (xargs :measure (nfix (truncate (nfix x) (nfix y)))))
  (b* ((x (nfix x))
       (y (nfix y))
       ((when (eql y 0)) 0)
       ((when (< x y)) 0))
    (truncate/rem-nats-ind (- x y) y)))

(defun truncate-rem-ind (x y)
  (declare (xargs :measure (abs (truncate (rfix x) (rfix y)))
                  :hints (("Goal" :in-theory (enable truncate-redef)
                           :cases ((equal (+ x y) 0))))))
  (b* ((x (rfix x))
       (y (rfix y))
       ((when (eql y 0)) 0)
       ((when (< 0 y))
        (cond ((<= x (- y)) (truncate-rem-ind (+ x y) y))
              ((< x y) x)
              (t (truncate-rem-ind (- x y) y)))))
    (cond ((>= x (- y)) (truncate-rem-ind (+ x y) y))
          ((> x y) x)
          (t (truncate-rem-ind (- x y) y)))))


