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
                                      acl2::*-r-denominator-r
                                      acl2::equal-*-/-1)))))

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
                      '(:use ((:instance acl2::<-*-/-LEFT (a 1))
                              (:instance acl2::<-*-/-LEFT (a 0)))
                        :in-theory (disable acl2::<-*-/-LEFT
                                            acl2::<-UNARY-/-POSITIVE-RIGHT
                                            acl2::<-*-0))))))

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
                                                    acl2::<-*-/-right))
                 :use ((:instance numerator-<-denominator
                        (x (* (- x) (/ y))))
                       (:instance acl2::<-*-/-right
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





(local (include-book "std/util/termhints" :dir :system))
(Defsection truncate-unique

  (local (defthm add-sides-of-ineqs
           (implies (and (< a b)
                         (<= c d))
                    (< (+ a c) (+ b d)))
           :rule-classes nil))

  (local (include-book "arithmetic/top-with-meta" :dir :System))

  (local (defthm lemma1
           (implies (and (integerp delta)
                         (< delta 0)
                         (rationalp div)
                         (< 0 div))
                    (<= div (- (* delta div))))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (defthm nonneg-truncate-unique-lemma
    (implies (and (rationalp num)
                  (rationalp div)
                  (< 0 div)
                  (<= 0 num)
                  (integerp quot)
                  (integerp delta))
             (let ((rem1 (- num (* quot div)))
                   (rem2 (- num (* (+ delta quot) div))))
               (implies (and (<= 0 rem1)
                             (< rem1 div)
                             (<= 0 rem2)
                             (< rem2 div))
                        (equal delta 0))))
    :hints ((acl2::use-termhint
             (cond ((< delta 0)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< delta 0)"))
                            (:instance add-sides-of-ineqs
                             (a (+ num (- (* delta div)) (- (* div quot))))
                             (b div)
                             (c (* div quot))
                             (d num)))))
                   ((< 0 delta)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< 0 delta)"))
                            (:instance add-sides-of-ineqs
                             (a (+ num (- (* div quot))))
                             (b div)
                             (c (+ (* delta div) (* div quot)))
                             (d num)))))
                   (t '(:use ((:instance acl2::mark-clause-is-true
                               (x "neither"))))))))
    :rule-classes nil)

  (local (defthm lemma2
           (implies (and (integerp delta)
                         (< delta 0)
                         (rationalp div)
                         (< div 0))
                    (<= (- div) (* delta div)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm lemma3
           (implies (and (integerp delta)
                         (< 0 delta)
                         (rationalp div)
                         (< div 0))
                    (<= (- div) (- (* delta div))))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (defthm nonneg/neg-truncate-unique-lemma
    (implies (and (rationalp num)
                  (rationalp div)
                  (< div 0)
                  (<= 0 num)
                  (integerp quot)
                  (integerp delta))
             (let ((rem1 (- num (* quot div)))
                   (rem2 (- num (* (+ delta quot) div))))
               (implies (and (<= 0 rem1)
                             (< rem1 (- div))
                             (<= 0 rem2)
                             (< rem2 (- div)))
                        (equal delta 0))))
    :hints ((acl2::use-termhint
             (cond ((< delta 0)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< delta 0)"))
                            (:instance add-sides-of-ineqs
                             (a (+ num (- (* div quot))))
                             (b (- div))
                             (c (+ (* delta div) (* div quot)))
                             (d num))
                            
                            )))
                   ((< 0 delta)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< 0 delta)"))
                            (:instance add-sides-of-ineqs
                             (a (+ num (- (* delta div)) (- (* div quot))))
                             (b (- div))
                             (d num)
                             (c (* div quot)))
                            )))
                   (t '(:use ((:instance acl2::mark-clause-is-true
                               (x "neither"))))))))
    :rule-classes nil)


  (local (defthm lemma4
           (implies (and (integerp delta)
                         (< delta 0)
                         (rationalp div)
                         (< 0 div))
                    (<= (* delta div) (- div)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm lemma5
           (implies (and (integerp delta)
                         (< 0 delta)
                         (rationalp div)
                         (< 0 div))
                    (<= (- (* delta div)) (- div)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (defthm neg/nonneg-truncate-unique-lemma
    (implies (and (rationalp num)
                  (rationalp div)
                  (< 0 div)
                  (<= num 0)
                  (integerp quot)
                  (integerp delta))
             (let ((rem1 (- num (* quot div)))
                   (rem2 (- num (* (+ delta quot) div))))
               (implies (and (<= rem1 0)
                             (< (- div) rem1)
                             (<= rem2 0)
                             (< (- div) rem2))
                        (equal delta 0))))
    :hints ((acl2::use-termhint
             (cond ((< delta 0)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< delta 0)"))
                            (:instance add-sides-of-ineqs
                             (d (+ (* delta div) (* div quot)))
                             (c num)
                             (a (- div))
                             (b (+ num (- (* div quot))))
                             ))))
                   ((< 0 delta)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< 0 delta)"))
                            (:instance add-sides-of-ineqs
                             (d (* div quot))
                             (c num)
                             (b (+ num (- (* delta div)) (- (* div quot))))
                             (a (- div)))
                            )))
                   (t '(:use ((:instance acl2::mark-clause-is-true
                               (x "neither"))))))))
    :rule-classes nil)


  (local (defthm lemma6
           (implies (and (integerp delta)
                         (< delta 0)
                         (rationalp div)
                         (< div 0))
                    (<= (- (* delta div)) div))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (defthm nonneg/neg-floor-unique-lemma
    (implies (and (rationalp num)
                  (rationalp div)
                  (< div 0)
                  (<= 0 num)
                  (integerp quot)
                  (integerp delta))
             (let ((rem1 (- num (* quot div)))
                   (rem2 (- num (* (+ delta quot) div))))
               (implies (and (<= rem1 0)
                             (< div rem1)
                             (<= rem2 0)
                             (< div rem2))
                        (equal delta 0))))
    :hints ((acl2::use-termhint
             (cond ((< delta 0)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< delta 0)"))
                            (:instance add-sides-of-ineqs
                             (a div)
                             (b (+ num (- (* delta div)) (- (* div quot))))
                             (c num)
                             (d (* div quot)))
                            
                            )))
                   ((< 0 delta)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< 0 delta)"))
                            (:instance add-sides-of-ineqs
                             (a div)
                             (b (+ num (- (* div quot))))
                             (c num)
                             (d (+ (* delta div) (* div quot))))
                            )))
                   (t '(:use ((:instance acl2::mark-clause-is-true
                               (x "neither"))))))))
    :rule-classes nil)

  (defthm neg/nonneg-floor-unique-lemma
    (implies (and (rationalp num)
                  (rationalp div)
                  (< 0 div)
                  (<= num 0)
                  (integerp quot)
                  (integerp delta))
             (let ((rem1 (- num (* quot div)))
                   (rem2 (- num (* (+ delta quot) div))))
               (implies (and (<= 0 rem1)
                             (< rem1 div)
                             (<= 0 rem2)
                             (< rem2 div))
                        (equal delta 0))))
    :hints ((acl2::use-termhint
             (cond ((< delta 0)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< delta 0)"))
                            (:instance add-sides-of-ineqs
                             (d num)
                             (c (* div quot))
                             (a (+ num (- (* delta div)) (- (* div quot))))
                             (b div)))))
                   ((< 0 delta)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< 0 delta)"))
                            (:instance add-sides-of-ineqs
                             (d num)
                             (c (+ (* delta div) (* div quot)))
                             (a (+ num (- (* div quot))))
                             (b div)))))
                   (t '(:use ((:instance acl2::mark-clause-is-true
                               (x "neither"))))))))
    :rule-classes nil)


  (defthm neg/neg-truncate-unique-lemma
    (implies (and (rationalp num)
                  (rationalp div)
                  (< div 0)
                  (<= num 0)
                  (integerp quot)
                  (integerp delta))
             (let ((rem1 (- num (* quot div)))
                   (rem2 (- num (* (+ delta quot) div))))
               (implies (and (<= rem1 0)
                             (< div rem1)
                             (<= rem2 0)
                             (< div rem2))
                        (equal delta 0))))
    :hints ((acl2::use-termhint
             (cond ((< 0 delta)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< 0 delta)"))
                            (:instance add-sides-of-ineqs
                             (d (+ (* delta div) (* div quot)))
                             (c num)
                             (a div)
                             (b (+ num (- (* div quot))))
                             )
                            )))
                   ((< delta 0)
                    '(:use ((:instance acl2::mark-clause-is-true
                             (x "(< delta 0)"))
                            (:instance add-sides-of-ineqs
                             (d (* div quot))
                             (c num)
                             (b (+ num (- (* delta div)) (- (* div quot))))
                             (a div)))))
                   (t '(:use ((:instance acl2::mark-clause-is-true
                               (x "neither"))))))))
    :rule-classes nil)


  (defthm truncate-unique-lemma
    (implies (and (rationalp num)
                  (rationalp div)
                  (not (equal div 0))
                  (integerp quot)
                  (integerp delta))
             (let ((rem1 (- num (* quot div)))
                   (rem2 (- num (* (+ delta quot) div))))
               (implies (and (implies (<= num 0) (<= rem1 0))
                             (implies (<= 0 num) (<= 0 rem1))
                             (< (abs rem1) (abs div))
                             (implies (<= num 0) (<= rem2 0))
                             (implies (<= 0 num) (<= 0 rem2))
                             (< (abs rem2) (abs div)))
                        (equal delta 0))))
    :hints ((acl2::use-termhint
             (if (< 0 div)
                 (if (<= 0 num)
                     `(:use ((:instance nonneg-truncate-unique-lemma
                              (quot ,(acl2::hq quot)))))
                   `(:use ((:instance neg/nonneg-truncate-unique-lemma
                            (quot ,(acl2::hq quot))))))
               (if (<= 0 num)
                   `(:use ((:instance nonneg/neg-truncate-unique-lemma
                            (quot ,(acl2::hq quot)))))
                 `(:use ((:instance neg/neg-truncate-unique-lemma
                          (quot ,(acl2::hq quot)))))))))
    :rule-classes nil)


  (defthm floor-unique-lemma
    (implies (and (rationalp num)
                  (rationalp div)
                  (not (equal div 0))
                  (integerp quot)
                  (integerp delta))
             (let ((rem1 (- num (* quot div)))
                   (rem2 (- num (* (+ delta quot) div))))
               (implies (and (implies (<= div 0) (<= rem1 0))
                             (implies (<= 0 div) (<= 0 rem1))
                             (< (abs rem1) (abs div))
                             (implies (<= div 0) (<= rem2 0))
                             (implies (<= 0 div) (<= 0 rem2))
                             (< (abs rem2) (abs div)))
                        (equal delta 0))))
    :hints ((acl2::use-termhint
             (if (< 0 div)
                 (if (<= 0 num)
                     `(:use ((:instance nonneg-truncate-unique-lemma
                              (quot ,(acl2::hq quot)))))
                   `(:use ((:instance neg/nonneg-floor-unique-lemma
                            (quot ,(acl2::hq quot))))))
               (if (<= 0 num)
                   `(:use ((:instance nonneg/neg-floor-unique-lemma
                            (quot ,(acl2::hq quot)))))
                 `(:use ((:instance neg/neg-truncate-unique-lemma
                          (quot ,(acl2::hq quot)))))))))
    :rule-classes nil)

  (local (defthm minus-x-plus-x
           (equal (+ (- x) x) 0)))

  (local (defthmd hide-<
           (equal (< x y) (hide (< x y)))
           :hints (("goal" :expand ((hide (< x y)))))))

  (defthm truncate-bound
    (implies (and (rationalp num)
                  (rationalp div)
                  (not (equal div 0)))
             (let* ((quot (truncate num div))
                    (rem (- num (* quot div))))
               (and (implies (<= num 0) (<= rem 0))
                    (implies (<= 0 num) (<= 0 rem))
                    (< (abs rem) (abs div)))))
    :hints (("goal" :induct (truncate-rem-ind num div)
             :expand ((:with truncate-redef (truncate num div))
                      (:with truncate-redef (truncate 0 div))
                      (:with truncate-redef (truncate div div))
                      (:with truncate-redef (truncate (- div) div)))
             :in-theory (e/d ()
                             (truncate-of-nonneg-operands-step
                              truncate-of-nonneg-operands-base-case
                              truncate-of-y-negative-invert
                              truncate-of-negative-operands-step
                              truncate-of-x-negative-invert)))))


  (defthm floor-bound
    (implies (and (rationalp num)
                  (rationalp div)
                  (not (equal div 0)))
             (let* ((quot (floor num div))
                    (rem (- num (* quot div))))
               (and (implies (< 0 div) (<= 0 rem))
                    (implies (< div 0) (<= rem 0))
                    (< (abs rem) (abs div)))))
    :hints (("goal" :induct (floor-mod-ind num div)
             :expand ((:with floor-redef (floor num div))
                      (:with floor-redef (floor 0 div))
                      (:with floor-redef (floor div div))
                      (:with floor-redef (floor (- div) div)))
             :in-theory (e/d ()
                             (floor-of-nonneg-operands-step
                              floor-of-nonneg-operands-base-case
                              floor-of-y-negative-invert
                              floor-of-negative-operands-step)))))
  

  (defthmd truncate-unique
    (implies (and (rationalp num)
                  (rationalp div)
                  (not (equal div 0))
                  (integerp quot))
             (let ((rem (- num (* quot div))))
               (iff (equal quot (truncate num div))
                    (and (implies (<= num 0) (<= rem 0))
                         (implies (<= 0 num) (<= 0 rem))
                         (< (abs rem) (abs div))))))
    :hints (("goal" :use ((:instance truncate-unique-lemma
                           (delta (- (truncate num div) quot)))
                          (:instance truncate-bound))
             :in-theory (e/d ()
                             (truncate-of-nonneg-operands-step
                              truncate-of-nonneg-operands-base-case
                              truncate-of-y-negative-invert
                              truncate-of-negative-operands-step
                              truncate-of-x-negative-invert)))))

  (defthmd floor-unique
    (implies (and (rationalp num)
                  (rationalp div)
                  (not (equal div 0))
                  (integerp quot))
             (let ((rem (- num (* quot div))))
               (iff (equal quot (floor num div))
                    (and (implies (<= div 0) (<= rem 0))
                         (implies (<= 0 div) (<= 0 rem))
                         (< (abs rem) (abs div))))))
    :hints (("goal" :use ((:instance floor-unique-lemma
                           (delta (- (floor num div) quot)))
                          (:instance floor-bound))
             :in-theory (e/d ()
                             (floor-of-nonneg-operands-step
                              floor-of-nonneg-operands-base-case
                              floor-of-y-negative-invert
                              floor-of-negative-operands-step))))))
