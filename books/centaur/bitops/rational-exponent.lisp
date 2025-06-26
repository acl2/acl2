; Copyright (C) 2024 Intel Corporation
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

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(local (include-book "centaur/misc/multiply-out" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (in-theory (disable unsigned-byte-p)))





(local (defthm equal-0-of-leftshift
         (implies (natp sh)
                  (equal (equal 0 (ash x sh))
                         (zip x)))
         :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                             bitops::ihsext-recursive-redefs)))))

(local (defthm posp-of-leftshift
         (implies (and (natp sh)
                       (posp x))
                  (posp (ash x sh)))
         :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                             bitops::ihsext-recursive-redefs)))
         :rule-classes :type-prescription))

(local
 (defthm integer-length-minus-1-is-exponent
   (implies (posp x)
            (let ((scand (/ x (* (if (< x 0) -1 1)
                                 (ash 1 (1- (integer-length (abs x))))))))
              (and (<= 1 scand)
                   (< scand 2))))
   :hints (("Goal"
            :in-theory (enable* bitops::ihsext-inductions)
            :induct (integer-length x)
            :expand ((integer-length x)
                     (ash 1 (integer-length (logcdr x)))))
           (and stable-under-simplificationp
                '(:in-theory (enable logcons))))))

(define rational-exponent ((x rationalp))
  :returns (exp integerp :rule-classes :type-prescription)
  ;; We want the integer e such that x = sign * scand * 2^e, 1 <= scand < 2, sign = 1 or -1.
  ;; If x is an integer, e is (1- (integer-length (abs x))) by integer-length-minus-1-is-exponent above.

  ;; In general, we have x = n / d, integers.  Let en / ed be their respective
  ;; exponents, scn / scd their significands, and signn the sign of n (d is
  ;; always positive).  n / d = signn * scn * 2^en / (scd * 2^ed) = signn *
  ;; (scn / scd) * 2^(en - ed).  scn / scd ranges from 1/2 < scn/scd < 2 so the
  ;; true exponent of x is en - ed if scn / scd >= 1 (that is, scn >= scd);
  ;; otherwise, en - ed - 1 if scn < scd (and the significand is 2*scn/scd).


  (b* (((when (eql (mbe :logic (rfix x) :exec x) 0))
        0)
       (n (abs (numerator x)))
       (d (denominator x))
       (en (1- (integer-length n)))
       (ed (1- (integer-length d)))
       ((mv nnorm dnorm)
        (if (< en ed)
            (mv (ash n (- ed en)) d)
          (mv n (ash d (- en ed))))))
    (if (< nnorm dnorm)
        (1- (- en ed))
      (- en ed)))
  ///
  (local (defthm integer-length-<-0
           (implies (posp x)
                    (posp (integer-length x)))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs)))
           :rule-classes :type-prescription))

  (defthm rational-exponent-correct-positive
    (implies (and (rationalp x)
                  (< 0 x))
             (let ((scand (/ x (expt 2 (rational-exponent x)))))
               (and (<= 1 scand)
                    (< scand 2))))
    :hints (("Goal" :in-theory (e/d (bitops::ash-is-expt-*-x
                                     acl2::exponents-add-unrestricted)
                                    (rational-implies2
                                     ACL2::*-R-DENOMINATOR-R))
             :use ((:instance integer-length-minus-1-is-exponent
                              (x (abs (numerator x))))
                   (:instance integer-length-minus-1-is-exponent
                              (x (denominator x)))
                   (:instance rational-implies2 (x x))))
            (and stable-under-simplificationp
                 '(:nonlinearp t))))

  (defthm denominator-of-neg
    (equal (denominator (- x))
           (denominator x))
    :hints (("Goal" :cases ((rationalp x)))))

  (defthm rational-exponent-of-negate
    (equal (rational-exponent (- x))
           (rational-exponent x)))

  (defthm rational-exponent-of-rfix
    (equal (rational-exponent (rfix x))
           (rational-exponent x)))

  (defthm rational-exponent-correct-negative
    (implies (and (rationalp x)
                  (< x 0))
             (let ((scand (- (/ x (expt 2 (rational-exponent x))))))
               (and (<= 1 scand)
                    (< scand 2))))
    :hints (("Goal" :use ((:instance rational-exponent-correct-positive
                                     (x (- x))))
             :in-theory (disable rational-exponent)))))

(defthmd rational-exponent-correct-abs
  (implies (and (rationalp x)
                (not (equal 0 x)))
           (and (<= (expt 2 (rational-exponent x)) (abs x))
                (< (abs x) (* 2 (expt 2 (rational-exponent x))))))
  :hints (("goal" :use ((:instance rational-exponent-correct-positive
                         (x (abs x))))
           :in-theory (disable rational-exponent-correct-positive)))
  :rule-classes :linear)

(define rational-significand ((x rationalp))
  ;; :guard (not (eql x 0))
  :returns (scand)
  (if (eql (mbe :logic (rfix x) :exec x) 0)
      0
    (/ (abs x)
       (expt 2 (rational-exponent x))))
  ///
  (defret rational-significand-bounds
    (implies (not (equal (rfix x) 0))
             (and (<= 1 scand)
                  (< scand 2)))
    :hints (("Goal" :cases ((< (rfix x) 0))))
    :rule-classes :linear)

  (defret rational-significand-type
    (and (rationalp scand)
         (<= 0 scand))
    :rule-classes :type-prescription)

  (defret rational-significand-of-negate
    (equal (rational-significand (- x))
           (rational-significand x)))

  (defret rational-significand-of-rfix
    (equal (rational-significand (rfix x))
           (rational-significand x)))

  (defret rational-significand-equal-0
    (equal (equal 0 scand)
           (equal 0 (rfix x)))))

(define rational-sign ((x rationalp))
  :returns (sign)
  (if (< (mbe :logic (rfix x) :exec x)
         0)
      -1
    1)
  ///
  (defret rational-sign-type
    (or (equal sign -1)
        (equal sign 1))
    :rule-classes
    (:type-prescription
     (:forward-chaining :trigger-terms (sign))))

  (defret rational-sign-of-rfix
    (equal (rational-sign (rfix x))
           (rational-sign x)))

  (defret rational-sign-of-negate
    (implies (not (equal (rfix x) 0))
             (equal (rational-sign (- x))
                    (- (rational-sign x))))))


(defthm rational-sign-significand-exponent-correct
  (equal (* (rational-sign x)
            (rational-significand x)
            (expt 2 (rational-exponent x)))
         (rfix x))
  :hints (("Goal" :in-theory (enable rational-significand
                                     rational-sign))))

(defthmd rational-exponent-in-terms-of-rational-significand
  (implies (and (rationalp x)
                (not (equal x 0)))
           (equal (expt 2 (rational-exponent x))
                  (* (rational-sign x) (/ x (rational-significand x)))))
  :hints (("Goal" :in-theory (enable rational-significand
                                     rational-sign))))

(defthmd rational-exponent-in-terms-of-rational-significand-abs
  (implies (and (rationalp x)
                (not (equal x 0)))
           (equal (expt 2 (rational-exponent x))
                  (/ (abs x) (rational-significand x))))
  :hints (("Goal"
           :in-theory (enable rational-exponent-in-terms-of-rational-significand
                              rational-sign))))

(defthmd rational-significand-in-terms-of-rational-exponent
  (implies (and (rationalp x)
                (not (equal x 0)))
           (equal (rational-significand x)
                  (* (rational-sign x) (/ x (expt 2 (rational-exponent x))))))
  :hints (("Goal" :in-theory (enable rational-significand
                                     rational-sign))))

(defthmd rational-significand-in-terms-of-rational-exponent-abs
  (implies (and (rationalp x)
                (not (equal x 0)))
           (equal (rational-significand x)
                  (/ (abs x) (expt 2 (rational-exponent x)))))
  :hints (("Goal"
           :in-theory (enable rational-significand-in-terms-of-rational-exponent
                              rational-sign))))


(encapsulate
  nil

  (local (defthm divide-out-exponent
           (implies (and (rationalp r)
                         (rationalp s)
                         (integerp x))
                    (iff (equal (* r (expt 2 x))
                                (* (expt 2 x) s))
                         (equal r s)))))

  (local (defun rational-exponent-diff (significand exponent)
           (- (rational-exponent (* significand (expt 2 exponent))) (ifix exponent))))

  (local (defthm rewrite-rational-exponent-in-terms-of-diff
           (implies (integerp exponent)
                    (equal (rational-exponent (* significand (expt 2 exponent)))
                           (+ exponent (rational-exponent-diff significand exponent))))))

  (local (in-theory (disable rational-exponent-diff)))

  (local (defthm expt-2-when-less-than-0
           (implies (and (integerp x)
                         (< x 0))
                    (<= (expt 2 x) 1/2))
           :hints (("Goal" :in-theory (enable expt)))
           :rule-classes :linear))

  (defthm rational-sign-significand-exponent-unique
    (implies (and (or (equal sign 1) (equal sign -1))
                  (rationalp significand)
                  (<= 1 significand)
                  (< significand 2)
                  (integerp exponent))
             (let ((x  (* sign significand (expt 2 exponent))))
               (and (equal (rational-sign x) sign)
                    (equal (rational-significand x) significand)
                    (equal (rational-exponent x) exponent))))
    :hints (("Goal"
             :in-theory (e/d (rational-sign)
                             (rational-sign-significand-exponent-correct))
             :use ((:instance rational-sign-significand-exponent-correct
                              (x (* sign significand (expt 2 exponent)))))
             :cases ((equal (rational-exponent (* sign significand (expt 2 exponent)))
                            exponent)))
            (and stable-under-simplificationp
                 '(:cases ((< (rational-exponent-diff significand exponent) 0)
                           (> (rational-exponent-diff significand exponent) 0))))
            (and stable-under-simplificationp
                 '(:nonlinearp t)))
    :otf-flg t)


  (local (in-theory (disable rewrite-rational-exponent-in-terms-of-diff)))

  (defthm rational-sign-significand-exponent-of-double
    (and (equal (rational-sign (* 2 x))
                (rational-sign x))
         (equal (rational-significand (* 2 x))
                (rational-significand x))
         (implies (not (equal (rfix x) 0))
                  (equal (rational-exponent (* 2 x))
                         (+ 1 (rational-exponent x)))))
    :hints (("Goal"
             :use ((:instance rational-sign-significand-exponent-unique
                              (exponent (+ 1 (rational-exponent x)))
                              (significand (rational-significand x))
                              (sign (rational-sign x)))
                   (:instance rational-sign-significand-exponent-correct
                              (x x)))
             :in-theory (e/d (rational-sign
                              acl2::exponents-add-unrestricted)
                             (rational-sign-significand-exponent-unique
                              rational-exponent-of-negate
                              rational-significand-of-negate)))
            (and stable-under-simplificationp
                 '(:in-theory (enable rational-significand)))))

  (defthm rational-sign-significand-exponent-of-half
    (and (equal (rational-sign (* 1/2 x))
                (rational-sign x))
         (equal (rational-significand (* 1/2 x))
                (rational-significand x))
         (implies (not (equal (rfix x) 0))
                  (equal (rational-exponent (* 1/2 x))
                         (+ -1 (rational-exponent x)))))
    :hints (("Goal"
             :use ((:instance rational-sign-significand-exponent-unique
                              (exponent (+ -1 (rational-exponent x)))
                              (significand (rational-significand x))
                              (sign (rational-sign x)))
                   (:instance rational-sign-significand-exponent-correct
                              (x x)))
             :in-theory (e/d (rational-sign
                              acl2::exponents-add-unrestricted)
                             (rational-sign-significand-exponent-unique
                              rational-exponent-of-negate
                              rational-significand-of-negate)))
            (and stable-under-simplificationp
                 '(:in-theory (enable rational-significand)))))

  ;; rational-exponent-base-case
  (defthm rational-exponent-zero-range
    (implies (and (rationalp x)
                  (<= 1 (abs x))
                  (< (abs x) 2))
             (equal (rational-exponent x) 0))
    :hints (("Goal" :use ((:instance rational-sign-significand-exponent-unique
                                     (sign (if (< x 0) -1 1))
                                     (significand (abs x))
                                     (exponent 0))))))

  (defthm rational-significand-base-case
    (implies (and (rationalp x)
                  (<= 1 (abs x))
                  (< (abs x) 2))
             (equal (rational-significand x) (abs x)))
    :hints (("Goal" :use ((:instance rational-sign-significand-exponent-unique
                                     (sign (if (< x 0) -1 1))
                                     (significand (abs x))
                                     (exponent 0))))))

  (local (defund rational-exponent-x-y-diff (x y)
           (acl2::pos-fix (- (rational-exponent x) (rational-exponent y)))))

  (local (defthmd rewrite-rational-exponent-in-terms-of-x-y-diff
           (implies (and (bind-free (and (equal x 'x)
                                         '((y . y)))
                                    (y))
                         (< (rational-exponent y) (rational-exponent x)))
                    (equal (rational-exponent x)
                           (+ (rational-exponent y) (rational-exponent-x-y-diff x y))))
           :hints (("Goal" :in-theory (enable rational-exponent-x-y-diff)))))

  (defthm rational-exponent-monotonic
    (implies (and (<= (abs x) (abs y))
                  (rationalp x)
                  (rationalp y)
                  (not (equal x 0)))
             (<= (rational-exponent x) (rational-exponent y)))
    :hints (("Goal"
             :use ((:instance rational-sign-significand-exponent-correct
                              (x x))
                   (:instance rational-sign-significand-exponent-correct
                              (x y)))
             :in-theory (e/d (rewrite-rational-exponent-in-terms-of-x-y-diff
                              rational-sign)
                             (rational-sign-significand-exponent-correct)))
            (and stable-under-simplificationp
                 '(:nonlinearp t)))
    :rule-classes :linear)

  (local (defund rational-exponent-x-n-diff (x n)
           (nfix (- (rational-exponent x) n))))

  (local (defthmd rewrite-rational-exponent-in-terms-of-x-n-diff
           (implies (and (bind-free (and (equal x 'x)
                                         '((n . n)))
                                    (n))
                         (integerp n)
                         (<= n (rational-exponent x)))
                    (equal (rational-exponent x)
                           (+ n (rational-exponent-x-n-diff x n))))
           :hints (("Goal" :in-theory (enable rational-exponent-x-n-diff)))))

  (defthm rational-exponent-less-than-power-of-2
    (implies (and (< (abs x) (expt 2 n))
                  (integerp n)
                  (rationalp x)
                  (not (equal x 0)))
             (< (rational-exponent x) n))
    :hints (("Goal"
             :use ((:instance rational-sign-significand-exponent-correct
                              (x x)))
             :in-theory (e/d (rational-sign
                              rewrite-rational-exponent-in-terms-of-x-n-diff)
                             (rational-sign-significand-exponent-correct)))
            (and stable-under-simplificationp
                 '(:nonlinearp t)))
    :rule-classes :linear)

  (defthm rational-exponent-of-expt-2
    (equal (rational-exponent (expt 2 n))
           (ifix n))
    :hints (("Goal"
             :use ((:instance rational-sign-significand-exponent-unique
                              (sign 1) (significand 1) (exponent (ifix n))))
             :in-theory (disable rational-sign-significand-exponent-unique))))

  (defthm rational-exponent-gte-power-of-2
    (implies (and (<= (expt 2 n) (abs x))
                  (integerp n)
                  (rationalp x))
             (<= n (rational-exponent x)))
    :hints (("Goal" :use ((:instance rational-exponent-monotonic
                                     (y x) (x (expt 2 n))))
             :in-theory (e/d (rational-sign)
                             (rational-exponent-monotonic)))
            (and stable-under-simplificationp
                 '(:nonlinearp t)))
    :rule-classes :linear)

  (defthm rational-exponent-positive
    (implies (and (<= 2 (abs x))
                  (rationalp x))
             (< 0 (rational-exponent x)))
    :hints (("Goal" :use ((:instance rational-exponent-gte-power-of-2
                                     (n 1)))))
    :rule-classes :linear)

  (defthm rational-exponent-negative
    (implies (and (< (abs x) 1)
                  (rationalp x)
                  (not (equal x 0)))
             (< (rational-exponent x) 0))
    :hints (("Goal" :use ((:instance rational-exponent-less-than-power-of-2
                                     (n 0)))))
    :rule-classes :linear)

  (defthmd rational-exponent-unique
    (implies (And (< x (* 2 (expt 2 n)))
                  (<= (expt 2 n) x)
                  (integerp n)
                  (rationalp x))
             (equal (rational-exponent x) n))
    :hints (("goal" :use ((:instance rational-exponent-gte-power-of-2)
                          (:instance rational-exponent-less-than-power-of-2
                           (n (+ 1 n))))
             :expand ((expt 2 (+ 1 n))))))

  (defthmd rational-exponent-unique-abs
    (implies (And (< (abs x) (* 2 (expt 2 n)))
                  (<= (expt 2 n) (abs x))
                  (integerp n)
                  (rationalp x))
             (equal (rational-exponent x) n))
    :hints (("goal" :use ((:instance rational-exponent-unique
                           (x (abs x))))))))


(define rational-exponent-rec ((x rationalp))
  (declare (xargs :measure (abs (rational-exponent x))))
  (b* (((when (eql (mbe :logic (rfix x) :exec x) 0)) 0)
       (xa (abs x)))
    (cond ((< xa 1) (1- (rational-exponent-rec (* x 2))))
          ((< xa 2) 0)
          (t (1+ (rational-exponent-rec (/ x 2))))))
  ///
  (defthmd rational-exponent-in-terms-of-rec
    (equal (rational-exponent x)
           (rational-exponent-rec x))
    :hints (("Goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable rational-exponent)))))

  (defthmd rational-exponent-recursive
    (equal (rational-exponent x)
           (b* (((when (eql (rfix x) 0)) 0)
                (xa (abs x)))
             (cond ((< xa 1) (1- (rational-exponent (* x 2))))
                   ((< xa 2) 0)
                   (t (1+ (rational-exponent (/ x 2)))))))
    :hints (("Goal" :in-theory (enable rational-exponent-rec
                                       rational-exponent-in-terms-of-rec)))
    :rule-classes ((:definition :controller-alist ((rational-exponent t)))))

  (defthmd rational-exponent-induct
    t
    :rule-classes ((:induction :pattern (rational-exponent x)
                               :scheme (rational-exponent-rec x)))))

(define rational-significand-rec ((x rationalp))
  :guard (not (eql x 0))
  (declare (xargs :measure (abs (rational-exponent x))))
  (b* (((when (eql (mbe :logic (rfix x) :exec x) 0)) 0)
       (xa (abs x)))
    (cond ((< xa 1) (rational-significand-rec (* x 2)))
          ((< xa 2) xa)
          (t (rational-significand-rec (/ x 2)))))
  ///
  (defthmd rational-significand-in-terms-of-rec
    (equal (rational-significand x)
           (rational-significand-rec x))
    :hints (("Goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable rational-significand)))))

  (defthmd rational-significand-recursive
    (equal (rational-significand x)
           (b* (((when (eql (rfix x) 0)) 0)
                (xa (abs x)))
             (cond ((< xa 1) (rational-significand (* x 2)))
                   ((< xa 2) xa)
                   (t (rational-significand (/ x 2))))))
    :hints (("Goal" :in-theory (enable rational-significand-rec
                                       rational-significand-in-terms-of-rec)))
    :rule-classes ((:definition :controller-alist ((rational-significand t)))))

  (defthmd rational-significand-induct
    t
    :rule-classes ((:induction :pattern (rational-significand x)
                               :scheme (rational-significand-rec x)))))



(defsection rational-sign-significand-exponent-compare-nonneg

  (defthm rational-significand-compare-nonneg
    (implies (and (rationalp x)
                  (rationalp y)
                  (< 0 x)
                  (< x y)
                  (equal (rational-exponent x) (rational-exponent y)))
             (< (rational-significand x) (rational-significand y)))
    :hints (("Goal" :use ((:instance rational-sign-significand-exponent-correct (x x))
                          (:instance rational-sign-significand-exponent-correct (x y)))
             :in-theory (e/d (rational-sign)
                             (rational-sign-significand-exponent-correct)))
            (and stable-under-simplificationp
                 '(:nonlinearp t))))

  (defthm rational-significand-compare-neg
    (implies (and (rationalp x)
                  (rationalp y)
                  (< y 0)
                  (< x y)
                  (equal (rational-exponent x) (rational-exponent y)))
             (< (rational-significand y) (rational-significand x)))
    :hints (("Goal"
             :use ((:instance rational-sign-significand-exponent-correct (x x))
                   (:instance rational-sign-significand-exponent-correct (x y)))
             :in-theory (e/d (rational-sign)
                             (rational-sign-significand-exponent-correct)))
            (and stable-under-simplificationp
                 '(:nonlinearp t)))))

(defthm rational-exponent-of-expt-2-prod
  (implies (and (rationalp x)
                (not (equal x 0)))
           (equal (rational-exponent (* (expt 2 n) x))
                  (+ (ifix n) (rational-exponent x))))
  :hints (("Goal" :in-theory (enable expt))))



(defthm rational-significand-of-expt-2-prod
  (implies (and (rationalp x)
                (not (equal x 0)))
           (equal (rational-significand (* (expt 2 n) x))
                  (rational-significand x)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm rational-significand-of-expt-2
  (implies (and (rationalp x)
                (not (equal x 0)))
           (equal (rational-significand (expt 2 n))
                  1))
  :hints (("Goal"
           :use ((:instance rational-significand-of-expt-2-prod (x 1)))
           :in-theory (disable rational-significand-of-expt-2-prod))))


(encapsulate
  nil

  (local (defthm rational-exponent-of-expt-2-prod-third
           (implies (and (rationalp x)
                         (rationalp y)
                         (rationalp z)
                         (not (equal x 0))
                         (not (equal y 0))
                         (not (equal z 0)))
                    (equal (rational-exponent (* x y (expt 2 n) z))
                           (+ (ifix n) (rational-exponent (* x y z)))))
           :hints (("Goal"
                    :use ((:instance rational-exponent-of-expt-2-prod
                                     (x (* x y z))))
                    :in-theory (disable rational-exponent-of-expt-2-prod)))))

  (local (defthm rational-exponent-of-expt-2-prod-third2
           (implies (and (rationalp x)
                         (rationalp y)
                         (not (equal x 0))
                         (not (equal y 0)))
                    (equal (rational-exponent (* x y (expt 2 n)))
                           (+ (ifix n) (rational-exponent (* x y)))))
           :hints (("Goal"
                    :use ((:instance rational-exponent-of-expt-2-prod
                                     (x (* x y))))
                    :in-theory (disable rational-exponent-of-expt-2-prod)))))

  (local (defthm rational-significand-of-expt-2-prod-third
           (implies (and (rationalp x)
                         (rationalp y)
                         (rationalp z)
                         (not (equal x 0))
                         (not (equal y 0))
                         (not (equal z 0)))
                    (equal (rational-significand (* x y (expt 2 n) z))
                           (rational-significand (* x y z))))
           :hints (("Goal"
                    :use ((:instance rational-significand-of-expt-2-prod
                                     (x (* x y z))))
                    :in-theory (disable rational-significand-of-expt-2-prod)))))

  (local (defthm rational-significand-of-expt-2-prod-third2
           (implies (and (rationalp x)
                         (rationalp y)
                         (not (equal x 0))
                         (not (equal y 0)))
                    (equal (rational-significand (* x y (expt 2 n)))
                           (rational-significand (* x y))))
           :hints (("Goal"
                    :use ((:instance rational-significand-of-expt-2-prod
                                     (x (* x y))))
                    :in-theory (disable rational-significand-of-expt-2-prod)))))

  (local
   (defthmd x*y-equals-exponent-prod
     (implies (and (syntaxp (and (equal x 'x)
                                 (equal y 'y)))
                   (rationalp x)
                   (rationalp y)
                   (not (equal x 0))
                   (not (equal y 0)))
              (equal (* x y)
                     (* (expt 2 (rational-exponent x))
                        (expt 2 (rational-exponent y))
                        (rational-significand x)
                        (rational-significand y)
                        (rational-sign x)
                        (rational-sign y))))
     :hints (("Goal"
              :in-theory (enable rational-significand-in-terms-of-rational-exponent
                                 rational-sign)))))

  (local (defthm rational-significand-prod-bounds
           (implies (and (not (equal (rfix x) 0))
                         (not (equal (rfix y) 0)))
                    (and (<= 1 (* (rational-significand x)
                                  (rational-significand y)))
                         (< (* (rational-significand x)
                               (rational-significand y))
                            4)))
           :hints (("Goal" :nonlinearp t))
           :rule-classes :linear))

  (defthmd rational-exponent/significand-of-multiply
    (implies (and (rationalp x)
                  (rationalp y)
                  (not (equal x 0))
                  (not (equal y 0)))
             (and (equal (rational-exponent (* x y))
                         (b* ((xsig (rational-significand x))
                              (ysig (rational-significand y))
                              (over (<= 2 (* xsig ysig))))
                           (+ (if over 1 0)
                              (rational-exponent x)
                              (rational-exponent y))))
                  (equal (rational-significand (* x y))
                         (b* ((xsig (rational-significand x))
                              (ysig (rational-significand y))
                              (over (<= 2 (* xsig ysig))))
                           (* (if over 1/2 1)
                              (rational-significand x)
                              (rational-significand y))))))
    :hints (("Goal"
             :use ((:instance rational-sign-significand-exponent-correct (x x))
                   (:instance rational-sign-significand-exponent-correct (x y)))
             :in-theory (e/d (rational-sign
                              x*y-equals-exponent-prod)
                             (rational-sign-significand-exponent-correct)))
            (and stable-under-simplificationp
                 '(:expand ((:with rational-exponent-recursive
                                   (rational-exponent (* (rational-significand x)
                                                         (rational-significand y))))
                            (:with rational-significand-recursive
                                   (rational-significand (* (rational-significand x)
                                                            (rational-significand y))))))))))

(defthmd rational-exponent/significand-of-recip
  (implies (and (rationalp x)
                (not (equal 0 x)))
           (and (equal (rational-exponent (/ x))
                       (if (equal (rational-significand x) 1)
                           (- (rational-exponent x))
                         (1- (- (rational-exponent x)))))
                (equal (rational-significand (/ x))
                       (if (equal (rational-significand x) 1)
                           1
                         (* 2 (/ (rational-significand x)))))))
  :hints (("Goal"
           :in-theory (enable rational-exponent-induct)
           :induct (rational-exponent x)
           :expand ((:with rational-exponent-recursive (rational-exponent (/ x)))
                    (:with rational-exponent-recursive (rational-exponent x))
                    (:with rational-significand-recursive (rational-significand (/ x)))
                    (:with rational-significand-recursive (rational-significand x))))))


(defthmd rational-exponent/significand-of-divide
  (implies (and (rationalp x)
                (rationalp y)
                (not (equal x 0))
                (not (equal y 0)))
           (and (b* ((exp (if (< (rational-significand x) (rational-significand y))
                              (1- (- (rational-exponent x) (rational-exponent y)))
                            (- (rational-exponent x) (rational-exponent y)))))
                  (and (equal (rational-exponent (* (/ y) x)) exp)
                       (equal (rational-exponent (* x (/ y))) exp)))
                (b* ((signif (if (< (rational-significand x) (rational-significand y))
                                 (* 2 (/ (rational-significand x) (rational-significand y)))
                               (/ (rational-significand x) (rational-significand y)))))
                  (and (equal (rational-significand (* (/ y) x)) signif)
                       (equal (rational-significand (* x (/ y))) signif)))))
  :hints (("Goal" :in-theory (enable rational-exponent/significand-of-multiply
                                     rational-exponent/significand-of-recip)))
  :otf-flg t)
