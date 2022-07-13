; Copyright (C) 2022 Intel Corp.
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
;
; Original author: Sol Swords <sol.swords@intel.com>


(in-package "BITOPS")

(include-book "ihs/logops-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(define int-sqrt/rem ((x natp))
  :measure (integer-length (nfix x))
  :returns (mv (sqrt natp :rule-classes :type-prescription)
               (rem))
  :hints(("Goal" :expand ((integer-length x)
                          (integer-length (nfix x)))))
  :verify-guards nil
  (b* (((when (zp x)) (mv 0 0))
       ((mv sqrt rem) (int-sqrt/rem (logtail 2 x)))
       ;; sqrt*sqrt + rem == (logtail 2 x) and rem <= 2sqrt
        ;; we need sqrt', rem', rem' <= 2sqrt'
        ;; sqrt'^2 + rem' == x == 4*sqrt^2 + 4*rem + (loghead 2 x)
        ;; try 2*sqrt, 2*sqrt+1.
        ;; 2*sqrt:  rem' = 4*rem + (loghead 2 x)
        ;; 2*sqrt+1: rem' = 4*rem + (loghead 2 x) - 4*sqrt - 1
        (rem0 (+ (* 4 rem) (loghead 2 x)))
        ((when (>= (* 4 sqrt) rem0))
         (mv (* 2 sqrt) rem0))
        (sqrt1 (+ 1 (* 2 sqrt))))
    (mv sqrt1 (- rem0 (+ 1 (* 4 sqrt)))))
  ///
  (local (defthmd loghead-plus-logtail
           (equal (+ (loghead n x) (ash (logtail n x) (nfix n)))
                  (ifix x))
           :hints (("goal" :induct (loghead n x)
                    :in-theory (e/d* (bitops::ihsext-inductions
                                      bitops::ihsext-recursive-redefs))))))
  
  (defretd int-sqrt/rem-invariant
    (and (equal rem (- (nfix x) (* sqrt sqrt)))
         (<= rem (* 2 sqrt))
         (integerp rem)
         (<= 0 rem))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (disable (:d <fn>)))
            (and stable-under-simplificationp
                 '(:use ((:instance loghead-plus-logtail
                          (n 2) (x x)))
                   :in-theory (enable bitops::ash-is-expt-*-x
                                      acl2::loghead-upper-bound)))))

  (defretd int-sqrt/rem-sqrt-bounds
    (and (<= (* sqrt sqrt) (nfix x))
         (< (nfix x) (* (+ 1 sqrt) (+ 1 sqrt))))
    :hints (("goal" :use int-sqrt/rem-invariant
             :in-theory (disable int-sqrt/rem-invariant
                                 int-sqrt/rem))))

  (defret int-sqrt/rem-rem-natp
    (natp rem)
    :rule-classes :type-prescription)


  (local (defthm integer-length-of-logcons
           (implies (and (not (zip x))
                         (not (eql x -1)))
                    (equal (integer-length (logcons b x))
                           (+ 1 (integer-length x))))
           :hints (("goal" :expand ((integer-length (logcons b x)))))))
  
  (local (defthm integer-length-of-*2
           (implies (and (case-split (not (zip x)))
                         (not (eql x -1)))
                    (and (equal (integer-length (* 2 x))
                                (+ 1 (integer-length x)))
                         (equal (integer-length (+ 1 (* 2 x)))
                                (+ 1 (integer-length x)))))
           :hints (("goal" :use ((:instance integer-length-of-logcons (b 1))
                                 (:instance integer-length-of-logcons (b 0)))
                    :in-theory (e/d (logcons) (integer-length-of-logcons))))))

  (local (defthm loghead-equal-0-when-logtail-equal-0
           (implies (equal (logtail n x) 0)
                    (equal (equal (loghead n x) 0)
                           (zip x)))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs)))))
  
  (defret int-sqrt/rem-posp
    (implies (posp x)
             (posp sqrt))
    :hints (("goal" :induct <call>)))

  (defret int-sqrt/rem-equal-0
    (equal (equal sqrt 0)
           (zp x)))

  ;; (local (defthm floor-2-of-plus-3
  ;;          (implies (natp x)
  ;;                   (equal (floor (+ 3 x) 2)
  ;;                          (+ 1 (floor (+ 1 x) 2))))
  ;;          :hints(("Goal" :in-theory (enable floor nonnegative-integer-quotient)))))
  
  (defret integer-length-of-int-sqrt/rem
    (equal (integer-length sqrt)
           (logcdr (+ 1 (integer-length (nfix x)))))
    :hints (("goal" :induct <call>
             :expand ((integer-length x)
                      (integer-length (logcdr x))
                      (logtail 2 x)
                      (logtail 1 (logcdr x))))))
  
  (verify-guards int-sqrt/rem))

(define int-sqrt ((x natp))
  :returns (sqrt natp :rule-classes :type-prescription)
  (b* (((mv isqrt &) (int-sqrt/rem x)))
    isqrt)
  ///
  (defretd int-sqrt-bounds
    (and (<= (* sqrt sqrt) (nfix x))
         (< (nfix x) (* (+ 1 sqrt) (+ 1 sqrt))))
    :hints (("goal" :use int-sqrt/rem-sqrt-bounds))
    :rule-classes :linear)

  (defret int-sqrt-posp
    (implies (posp x)
             (posp sqrt)))

  (defret int-sqrt-equal-0
    (equal (equal sqrt 0)
           (zp x)))
  
  (defret integer-length-of-int-sqrt
    (equal (integer-length sqrt)
           (logcdr (+ 1 (integer-length (nfix x))))))

  (defthm int-sqrt/rem-redef
    (and (equal (mv-nth 0 (int-sqrt/rem x))
                (int-sqrt x))
         (equal (mv-nth 1 (int-sqrt/rem x))
                (- (nfix x) (* (int-sqrt x) (int-sqrt x)))))
    :hints(("Goal" :in-theory (enable int-sqrt/rem-invariant)))))

(define int-sqrt-ceiling ((x natp))
  :returns (sqrt natp :rule-classes :type-prescription)
  (b* (((mv isqrt rem) (int-sqrt/rem x)))
    (+ isqrt (if (eql rem 0) 0 1)))
  ///
  (defretd int-sqrt-ceiling-bounds
    (and (<= (nfix x) (* sqrt sqrt))
         (implies (posp x)
                  (< (* (+ -1 sqrt) (+ -1 sqrt)) (nfix x))))
    :hints (("goal" :use (int-sqrt/rem-sqrt-bounds
                          int-sqrt/rem-invariant)
             :in-theory (disable int-sqrt/rem-invariant)))
    :rule-classes :linear))


(defthmd upper-bound-by-int-sqrt
  (implies (and (integerp x) (natp y)
                (<= (* x x) y))
           (<= x (int-sqrt y)))
  :hints (("goal" :use ((:instance int-sqrt-bounds (x y))))
          (and stable-under-simplificationp
               '(:nonlinearp t)))
  :rule-classes :linear)

(defthmd lower-bound-by-int-sqrt
  (implies (and (natp x) (natp y)
                (< y (* (+ 1 x) (+ 1 x))))
           (<= (int-sqrt y) x))
  :hints (("goal" :use ((:instance int-sqrt-bounds (x y))))
          (and stable-under-simplificationp
               '(:nonlinearp t)))
  :rule-classes :linear)

(defthmd lower-bound-by-negative-int-sqrt
  (implies (and (integerp x) (natp y)
                (<= (* x x) y))
           (<= (- (int-sqrt y)) x))
  :hints (("goal" :use ((:instance int-sqrt-bounds (x y))))
          (and stable-under-simplificationp
               '(:nonlinearp t)))
  :rule-classes :linear)



(defthm bounds-by-int-sqrt-ceiling
  (implies (and (integerp x) (natp y)
                (<= y (* x x)))
           (or (<= (int-sqrt-ceiling y) x)
               (<= x (- (int-sqrt-ceiling y)))))
  :hints (("goal" :use ((:instance int-sqrt-ceiling-bounds (x y))))
          (and stable-under-simplificationp
               '(:nonlinearp t)))
  :rule-classes nil)

(defthmd lower-bound-by-int-sqrt-ceiling
  (implies (and (natp x) (natp y)
                (<= y (* x x)))
           (<= (int-sqrt-ceiling y) x))
  :hints (("goal" :use bounds-by-int-sqrt-ceiling))
  :rule-classes :linear)

(defthmd lower-bound-by-int-sqrt-ceiling-general
  (implies (and (integerp x) (natp y)
                (<= y (* x x))
                (< (- (int-sqrt-ceiling y)) x))
           (<= (int-sqrt-ceiling y) x))
  :hints (("goal" :use bounds-by-int-sqrt-ceiling))
  :rule-classes :linear)

(defthmd upper-bound-by-negative-int-sqrt-ceiling
  (implies (and (integerp x)
                (<= x 0)
                (natp y)
                (<= y (* x x)))
           (<= x (- (int-sqrt-ceiling y))))
  :hints (("goal" :use bounds-by-int-sqrt-ceiling))
  :rule-classes :linear)

(defthmd upper-bound-by-negative-int-sqrt-ceiling-general
  (implies (and (integerp x)
                (natp y)
                (<= y (* x x))
                (< x (int-sqrt-ceiling y)))
           (<= x (- (int-sqrt-ceiling y))))
  :hints (("goal" :use bounds-by-int-sqrt-ceiling))
  :rule-classes :linear)



(defthm int-sqrt-unique
  (implies (and (natp x)
                (natp s)
                (<= (* s s) x)
                (< x (* (+ 1 s) (+ 1 s))))
           (equal s (int-sqrt x)))
  :hints (("goal" :use ((:instance upper-bound-by-int-sqrt (y x) (x s))
                        (:instance lower-bound-by-int-sqrt (y x) (x s)))))
  :rule-classes nil)

(defthm int-sqrt-unique-by-remainder
  (b* ((remainder (- x (* s s))))
    (implies (and (natp x)
                  (natp s)
                  (<= 0 remainder)
                  (< remainder (+ 1 (* 2 s))))
             (equal s (int-sqrt x))))
  :hints (("goal" :use int-sqrt-unique))
  :rule-classes nil)



(defthm int-sqrt-monotonic
  (implies (and (natp x) (integerp y)
                (<= x y))
           (<= (int-sqrt x) (int-sqrt y)))
  :hints (("goal" :use ((:instance int-sqrt-bounds)
                        (:instance int-sqrt-bounds (x y))))
          (and stable-under-simplificationp
               '(:nonlinearp t))))
