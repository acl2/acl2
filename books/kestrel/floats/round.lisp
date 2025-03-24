; Partial spec of IEEE 754 floating point rounding
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Handle rounding attributes other than roundTiesToEven

;; TODO: Prove more validation theorems, such as that these is no closer
;; representable value than the rounded value.

(include-book "ieee-floats")
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
(local (include-book "meta/meta-plus-equal" :dir :system))
(local (include-book "meta/meta-plus-lessp" :dir :system))
(local (include-book "ieee-floats-helpers"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund int-part (x)
  (declare (xargs :guard (rationalp x)))
  (floor x 1))

(defthm rationalp-of-int-part-type
  (implies (rationalp x)
           (rationalp (int-part x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable int-part))))

(defthm <=-of-0-and-int-part
  (implies (and (<= 0 rat)
                (rationalp rat))
           (<= 0 (int-part rat)))
  :hints (("Goal" :in-theory (enable int-part))))

(defthm <=-of-0-and-int-part-type
  (implies (and (<= 0 rat)
                (rationalp rat))
           (<= 0 (int-part rat)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable int-part))))

(defund frac-part (x)
  (declare (xargs :guard (rationalp x)))
  (- x (int-part x)))

(defthm rationalp-of-frac-part-type
  (implies (rationalp x)
           (rationalp (frac-part x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable frac-part))))

(defund round-to-nearest-integer-ties-to-even (x)
  (declare (xargs :guard (rationalp x)))
  (let* ((int-part (int-part x))
         (frac-part (frac-part x)) ; optimize to not redo the int-part
         (low int-part)
         (high (+ 1 int-part)))
    (if (< 1/2 frac-part)
        high
      (if (equal 1/2 frac-part)
          (if (evenp high) high low)
        ;; frac-part < 1/2:
        low))))

(defthm integerp-of-round-to-nearest-integer-ties-to-even
  (implies (rationalp x)
           (integerp (round-to-nearest-integer-ties-to-even x)))
  :hints (("Goal" :in-theory (enable round-to-nearest-integer-ties-to-even int-part frac-part))))

(defthm round-to-nearest-integer-ties-to-even-bound
  (implies (rationalp x)
           (<= (abs (- x (round-to-nearest-integer-ties-to-even x)))
                    1/2))
  :hints (("Goal" :in-theory (enable round-to-nearest-integer-ties-to-even int-part frac-part))))

(defthm round-to-nearest-integer-ties-to-even-when-integerp
  (implies (integerp x)
           (equal (round-to-nearest-integer-ties-to-even x)
                  x))
  :hints (("Goal" :in-theory (enable round-to-nearest-integer-ties-to-even int-part frac-part))))

(defthm <=-of-0-and-round-to-nearest-integer-ties-to-even
  (implies (and (<= 0 x)
                (rationalp x))
           (<= 0 (round-to-nearest-integer-ties-to-even x)))
  :hints (("Goal" :in-theory (enable round-to-nearest-integer-ties-to-even int-part frac-part))))

(defthm <-of-0-and-round-to-nearest-integer-ties-to-even
  (implies (and (<= 0 x)
                (rationalp x))
           (equal (< 0 (round-to-nearest-integer-ties-to-even x))
                  (< 1/2 x)))
  :hints (("Goal" :in-theory (enable round-to-nearest-integer-ties-to-even int-part frac-part))))

(defthm <=-of-0-and-round-to-nearest-integer-ties-to-even-type
  (implies (and (<= 0 x)
                (rationalp x))
           (<= 0 (round-to-nearest-integer-ties-to-even x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable round-to-nearest-integer-ties-to-even int-part frac-part))))

(defthm equal-of-0-and-round-to-nearest-integer-ties-to-even-type
  (implies (and (<= 0 x)
                (rationalp x))
           (equal (equal 0 (round-to-nearest-integer-ties-to-even x))
                  (<= x 1/2)))
  :hints (("Goal" :in-theory (enable round-to-nearest-integer-ties-to-even int-part frac-part))))

(local
  (defthm helper
    (implies (and (not (integerp x))
                  (rationalp x)
                  (integerp i)
                  (< x i) ; this case
                  )
             (<= (+ 1 (floor x 1)) i))))

;; there is no closer integer
(defthm no-closer-integer
  (implies (and (rationalp x)
                (integerp i))
           (<= (abs (- x (round-to-nearest-integer-ties-to-even x)))
               (abs (- x i))))
  :hints (("Goal" :cases ((integerp x))
           :use helper
           :in-theory (enable round-to-nearest-integer-ties-to-even int-part frac-part))))

(defthmd no-closer-integer-2
  (implies (and (rationalp x)
                (integerp i)
                (<= x i))
           (<= (round-to-nearest-integer-ties-to-even x) i))
  :hints (("Goal" :cases ((integerp x))
           :use helper
           :in-theory (enable round-to-nearest-integer-ties-to-even int-part frac-part))))

;; Tests:
(thm
  (and (equal (round-to-nearest-integer-ties-to-even 7) 7)
       (equal (round-to-nearest-integer-ties-to-even 8) 8)
       (equal (round-to-nearest-integer-ties-to-even (/ 74 10)) 7) ; 7.4
       (equal (round-to-nearest-integer-ties-to-even (/ 76 10)) 8) ; 7.6
       (equal (round-to-nearest-integer-ties-to-even (/ 75 10)) 8) ; since 8 is even
       (equal (round-to-nearest-integer-ties-to-even (/ 65 10)) 6) ; since 8 is even
       ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; From Section 4.3.1.
(defund infinity-threshold (k p)
  (declare (xargs :guard (formatp k p)))
  (* (expt 2 (emax k p))
     (- 2 (* 1/2 (expt 2 (- 1 p))))))

;; Sanity check: infinity-threshold is the average of the largest normal and
;; the smallest normal that would be expressible using the next larger exponent
;; (were such a number representable)
(defthmd infinity-threshold-redef
  (implies (formatp k p)
           (equal (infinity-threshold k p)
                  (/ (+ (expt 2 (+ 1 (emax k p)))
                        (largest-normal k p))
                     2)))
  :hints (("Goal" :in-theory (enable infinity-threshold
                                     largest-normal-redef
                                     decode-normal-number
                                     bias
                                     wfn
                                     emax
                                     ;expt-of-+
                                     ))))

(defthm <-of-1-and-infinity-threshold
  (implies (formatp k p)
           (< 1 (infinity-threshold k p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (infinity-threshold emax)
                                  (distributivity
                                   distributivity-alt)))))

;; The infinity-threshold exceeds the largest representable rational:
(defthm <-of-largest-normal-and-infinity-threshold
  (implies (formatp k p)
           (< (largest-normal k p)
              (infinity-threshold k p)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable largest-normal
                                     largest-normal-redef
                                     infinity-threshold))))

(defthm <-of-expt2-and-1
  (implies (integerp i)
           (equal (< (expt 2 i) 1)
                  (< i 0)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm <=-of-1-and-emax-linear
  (implies (formatp k p)
           (<= 1 (emax k p)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable formatp emax))))

(defthm log2-of-smallest-positive-normal
  (implies (formatp k p)
           (equal (log2 (smallest-positive-normal k p))
                  (emin k p)))
  :hints (("Goal" :in-theory (enable smallest-positive-normal-redef))))

(defthm log2-of-decode-normal-number-positive
  (implies (and (formatp k p)
                ;(bitp sign) ; todo bitp vs unsigned-byte-p
                (unsigned-byte-p (wfn k p) biased-exponent)
                (< 0 biased-exponent) ; not all zeros
                (< biased-exponent (+ -1 (expt 2 (wfn k p)))) ; not all ones
                (unsigned-byte-p (- p 1) trailing-significand))
           (equal (log2 (decode-normal-number k p
                                              0 ;sign
                                              biased-exponent trailing-significand))
                  (- biased-exponent (bias k p))))
  :hints (("Goal" :in-theory (enable decode-normal-number wfn unsigned-byte-p))))

(defthm log2-of-largest-normal
  (implies (formatp k p)
           (equal (log2 (largest-normal k p))
                  (emax k p)))
  :hints (("Goal" :in-theory (enable largest-normal wfn emax bias))))

(defthm <-of-emin-and-emax
  (implies (formatp k p)
           (< (emin k p) (emax k p)))
  :hints (("Goal" :in-theory (enable emin emax))))

(defthm <=-of-emin-and-emax
  (implies (formatp k p)
           (<= (emin k p) (emax k p)))
  :hints (("Goal" :in-theory (enable emin emax))))

(defthmd <-when-<-of-log2-and-log2
  (implies (and (< (log2 x) (log2 y))
                (rationalp x)
                (rationalp y)
                (< 0 x)
                (< 0 y))
           (< x y)))

(defthm <-of-0-and-log2
  (implies (rationalp x)
           (equal (< 0 (log2 x))
                  (<= 2 x)))
  :hints (("Goal" ;:cases ((< 0 x))
           :in-theory (enable log2))))

(defthm <-of-0-and-largest-normal
  (implies (formatp k p)
           (< 0 (largest-normal k p)))
  :hints (("Goal" :in-theory (enable largest-normal))))

(defthm <-of-smallest-positive-normal-and-largest-normal
  (implies (formatp k p)
           (< (smallest-positive-normal k p)
              (largest-normal k p)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :cases ((< p 2))
           :in-theory (enable <-when-<-of-log2-and-log2))))

(defthm <-of-largest-subnormal-smallest-positive-normal
  (implies (formatp k p)
           (< (largest-subnormal k p)
              (smallest-positive-normal k p)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" ;:cases ((< p 2))
           :in-theory (enable <-when-<-of-log2-and-log2))))

(defthm <-of-largest-subnormal-and-infinity-threshold
  (implies (formatp k p)
           (< (largest-subnormal k p)
              (infinity-threshold k p)))
  :hints (("Goal" :use <-of-largest-normal-and-infinity-threshold
           :in-theory (disable <-of-largest-normal-and-infinity-threshold))))

(defthm infinity-threshold-linear
  (implies (formatp k p)
           (< (infinity-threshold k p)
              (expt 2 (+ 1 (emax k p)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable infinity-threshold expt-of-+))))



;move
(defthm log2-of-*-of-/-of-expt2
  (implies (and (integerp i)
                (< 0 x)
                (rationalp x))
           (equal (log2 (* (/ (expt 2 i)) x))
                  (+ (- i) (log2 x))))
  :hints (("Goal" :use (:instance log2-of-*-of-expt (i (- i)))
           :in-theory (disable log2-of-*-of-expt))))

(defthm integerp-of-*-of-expt-and-/-of-expt-and-n
  (implies (and (integerp n)
                (<= j i)
                (integerp i)
                (integerp j))
           (integerp (* (expt 2 i) (/ (expt 2 j)) n)))
  :hints (("Goal" :use (:instance integerp-of-*
                                  (x (* (expt 2 i) (/ (expt 2 j))))
                                  (y n))
           :in-theory (disable integerp-of-*))))

(defthmd round-to-nearest-integer-ties-to-even-helper
  (implies (and (< small 1)
                (rationalp small)
                (<= 0 small)
                (integerp int)
                (<= 0 int))
           (not (< int (round-to-nearest-integer-ties-to-even (* small int)))))
  :hints (("Goal"
           :use (:instance no-closer-integer-2 (x (* small int))
                           (i int))
           :in-theory (e/d (round-to-nearest-integer-ties-to-even frac-part) (no-closer-integer-2)))))

(defthmd round-to-nearest-integer-ties-to-even-helper-2
  (implies (and (formatp k p)
                (rationalp rat)
                (< 0 rat)
                (< rat (expt 2 (emin k p))) ; subnormal case
                )
           (not (< (expt 2 (+ -1 p))
                   (round-to-nearest-integer-ties-to-even (* rat (expt 2 (+ -1 p)) (/ (expt 2 (emin k p))))))))
  :hints (("Goal" :use (:instance round-to-nearest-integer-ties-to-even-helper
                                  (small (* rat (/ (expt 2 (emin k p)))))
                                  (int (expt 2 (+ -1 p))))
           :in-theory (disable round-to-nearest-integer-ties-to-even-helper))))

(defthm <=-of-int-part-when-integer
  (implies (and (<= i x)
                (rationalp x)
                (integerp i))
           (<= i (int-part x)))
  :hints (("Goal" :in-theory (enable int-part))))

(defthm log2-of-int-part
  (implies (and (<= 1 x) ; avoids log2 of 0
                (rationalp x))
           (equal (log2 (int-part x))
                  (log2 x)))
  :hints (("Goal" :in-theory (enable int-part))))

(defthm frac-part-linear
  (equal (frac-part x) (- x (int-part x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable frac-part))))

(defthm int-part-must-be
  (implies (and (rationalp x)
                (<= i x)
                (integerp i)
                (< x (+ 1 i)))
           (equal (int-part x)
                  i))
  :hints (("Goal" :in-theory (enable int-part))))

(defthm log2-of-round-to-nearest-integer-ties-to-even
  (implies (and (rationalp x)
                (posp i)
                (<= (expt 2 i) x)
                (< x (expt 2 (+ 1 i))))
           (equal (log2 (round-to-nearest-integer-ties-to-even x))
                  (if (<= (- (expt 2 (+ 1 i))
                             1/2)
                          x)
                      (+ 1 (log2 x))
                    (log2 x))))
  :hints (("Goal"
           :cases ((evenp (+ 1 (int-part x))))
           :use (:instance int-part-must-be
                           (x x)
                           (i (+ -1 (* 2 (expt 2 i)))))
           :in-theory (e/d (round-to-nearest-integer-ties-to-even expt-of-+
                                                                  even-not-equal-odd-hack)
                           (int-part-must-be)))))

(defthm log2-of-*-of-/-of-expt2-alt
  (implies (and (integerp i) (< 0 x) (rationalp x))
           (equal (log2 (* x (/ (expt 2 i))))
                  (+ (- i) (log2 x))))
  :hints (("Goal" :use (:instance log2-of-*-of-expt (i (- i)))
           :in-theory (disable log2-of-*-of-expt))))



(defthm <-expt-cancel-helper
  (implies (and (rationalp x)
                (rationalp y)
                (integerp p))
           (equal (< (* x y (expt 2 (+ -1 p))) (expt 2 p))
                  (< (* x y 1/2) 1)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm *-of-expt-helper
  (implies (and (integerp i)
                (integerp j)
                (rationalp x)
                )
           (equal (* (expt 2 i) (/ (expt 2 (+ j i))) x)
                  (* (/ (expt 2 j)) x)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

;; (thm
;;   (implies (and (<= (expt 2 p) (+ 1/2 (* rat (/ (expt 2 (log2 rat))) (expt 2 (+ -1 p)))))
;;                 (integerp p)
;;                 (< 1 p)
;;                 (rationalp rat)
;;                 (< 0 rat))
;;            (equal (round-to-nearest-integer-ties-to-even (* rat (/ (expt 2 (log2 rat))) (expt 2 (+ -1 p))))
;;                   p))
;;   :hints (("Goal" :in-theory (enable round-to-nearest-integer-ties-to-even))))

(defthm round-to-nearest-integer-ties-to-even-when-big
  (implies (and (rationalp x)
                (posp i)
                (<= (expt 2 i) x)
                (< x (expt 2 (+ 1 i)))
                (<= (- (expt 2 (+ 1 i)) 1/2) x) ; this case
                )
           (equal (round-to-nearest-integer-ties-to-even x)
                  (expt 2 (+ 1 i))))
  :hints (("Goal"
           :cases ((evenp (+ 1 (int-part x))))
           :use (:instance int-part-must-be
                           (x x)
                           (i (+ -1 (* 2 (expt 2 i)))))
           :in-theory (e/d (round-to-nearest-integer-ties-to-even expt-of-+
                                                                  even-not-equal-odd-hack)
                           (int-part-must-be)))))

(defthm final-helper
  (implies (and (formatp k p)
                (rationalp rat)
                (< 0 rat)
                (< rat (infinity-threshold k p)))
           (< (+ 1/2
                 (* rat (expt 2 (+ -1 p))
                    (/ (expt 2 (emax k p)))))
              (expt 2 p)))
  :hints (("Goal" :in-theory (enable infinity-threshold))))

;; todo: clean up the stuff above here

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The guard excludes the case where we round to *float-positive-infinity*.
;; Returns a rational.
(defund round-positive-normal-ties-to-even (k p rat)
  (declare (xargs :guard (and (formatp k p)
                              (rationalp rat)
                              ;; (< 0 rat)
                              (<= (smallest-positive-normal k p) rat)
                              (< rat (infinity-threshold k p))
                              ))
           (ignore k)) ; only used in the guard
  (let* ((exponent (log2 rat))
         (significand (/ rat (expt 2 exponent))) ; in the range [1,2)
         (shifted-significand (* significand (expt 2 (- p 1)))) ; integer-part of this is in the range [2^(p-1), 2^p) and is a BV of size p
         (rounded-shifted-significand (round-to-nearest-integer-ties-to-even shifted-significand)) ; an integer in the range [2^(p-1), 2^p] so either a BV of size p, or 2^p if we rounded up
         (rounded-significand (/ rounded-shifted-significand (expt 2 (- p 1)))) ; in the range [1,2]
         )
    (* (expt 2 exponent) rounded-significand)))

(defthm <=-of-1-and-*-of-/-of-expt-of-log-same
  (implies (and (rationalp rat)
                (< 0 rat))
           (<= 1 (* rat (/ (expt 2 (log2 rat))))))
  :rule-classes (:rewrite :type-prescription))

(local
  (defthm bound-helper
    (implies (and (rationalp rat)
                  (< 0 rat)
                  (natp i))
             (< 1/2 (* rat (/ (expt 2 (log2 rat))) (expt 2 i))))
    :hints (("Goal" :use (<=-of-1-and-*-of-/-of-expt-of-log-same)
             :in-theory (disable <=-of-1-and-*-of-/-of-expt-of-log-same)))))

;slow
(defthm representable-positive-normalp-of-round-positive-normal-ties-to-even
  (implies (and (formatp k p)
                (rationalp rat)
                (<= (smallest-positive-normal k p) rat)
                (< rat (infinity-threshold k p)))
           (representable-positive-normalp k p (round-positive-normal-ties-to-even k p rat)))
  :hints (("Goal" :use ((:instance round-to-nearest-integer-ties-to-even-when-big
                                   (x (* rat (/ (expt 2 (log2 rat)))
                                         (expt 2 (+ -1 p))))
                                   (i (- p 1)))
                        (:instance log2-of-round-to-nearest-integer-ties-to-even
                                   (x (* rat (/ (expt 2 (log2 rat)))
                                         (expt 2 (+ -1 p))))
                                   (i (+ -1 p))))
           :in-theory (e/d (round-positive-normal-ties-to-even representable-positive-normalp
                                         infinity-threshold
                                         smallest-positive-normal-redef
                                         ;expt-of-+ ;bad
                                         )
                           (log2-of-round-to-nearest-integer-ties-to-even
                            log2-of-round-to-nearest-integer-ties-to-even
                            /-of-expt-of-diff)))))

(defthm round-positive-normal-ties-to-even-when-representable-positive-normalp
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-positive-normalp k p rat))
           (equal (round-positive-normal-ties-to-even k p rat)
                  rat))
  :hints (("Goal" :in-theory (enable round-positive-normal-ties-to-even representable-positive-normalp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a rational or *float-positive-zero*.  (Instead, we could allow this to return 0 instead of *float-positive-zero*.)
(defund round-positive-subnormal-ties-to-even (k p rat)
  (declare (xargs :guard (and (formatp k p)
                              (rationalp rat)
                              (< 0 rat)
                              (< rat (smallest-positive-normal k p)))))
  (let* ((emin (emin k p))
         (significand (/ rat (expt 2 emin))) ; in the range (0,1)
         (shifted-significand (* significand (expt 2 (- p 1)))) ; in the range (0, 2^(p-1)), so the integer-part of this is a BV of size p-1
         (rounded-shifted-significand (round-to-nearest-integer-ties-to-even shifted-significand)) ; in the range [0, 2^(p-1)]
         (rounded-significand (/ rounded-shifted-significand (expt 2 (- p 1)))) ; in the range [0, 1]
         )
    (if (equal 0 rounded-significand)
        *float-positive-zero*
      ;; might create smallest-positive-normal:
      (* (expt 2 emin) rounded-significand))))

;todo: rename to indicate the mode
(defthm type-of-round-positive-subnormal-ties-to-even
  (implies (and (formatp k p)
                (rationalp rat)
                (< 0 rat)
                (< rat (smallest-positive-normal k p)))
           (let ((result (round-positive-subnormal-ties-to-even k p rat)))
             (or (representable-positive-subnormalp k p result)
                 (equal *float-positive-zero* result)
                 ;; might round up to this:
                 (equal (smallest-positive-normal k p) result))))
  :hints (("Goal" :use (round-to-nearest-integer-ties-to-even-helper-2)
           :in-theory (e/d (round-positive-subnormal-ties-to-even
                            representable-positive-subnormalp
                            smallest-positive-normal-redef)
                           (round-to-nearest-integer-ties-to-even-helper-2)))))

(defthm round-positive-subnormal-ties-to-even-when-representable-positive-subnormalp
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-positive-subnormalp k p rat))
           (equal (round-positive-subnormal-ties-to-even k p rat)
                  rat))
  :hints (("Goal" :in-theory (enable round-positive-subnormal-ties-to-even representable-positive-subnormalp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund round-positive-rational-ties-to-even (k p rat)
  (declare (xargs :guard (and (formatp k p)
                              (rationalp rat)
                              (< 0 rat))))
  (if (<= (infinity-threshold k p) rat)
      *float-positive-infinity*
    (if (<= (smallest-positive-normal k p) rat) ; todo: or compare exponent to emin
        (round-positive-normal-ties-to-even k p rat)
      (round-positive-subnormal-ties-to-even k p rat))))

(defthm type-of-round-positive-rational-ties-to-even
  (implies (and (formatp k p)
                (rationalp rat)
                (< 0 rat))
           (let ((result (round-positive-rational-ties-to-even k p rat)))
             (or (representable-positive-normalp k p result)
                 (representable-positive-subnormalp k p result)
                 (equal *float-positive-zero* result)
                 (equal *float-positive-infinity* result))))
  :hints (("Goal" :in-theory (e/d (round-positive-rational-ties-to-even) (type-of-round-positive-subnormal-ties-to-even))
           :use type-of-round-positive-subnormal-ties-to-even)))

(defthm round-positive-subnormal-ties-to-even-when-representable-positive-subnormalp
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-positive-subnormalp k p rat))
           (equal (round-positive-subnormal-ties-to-even k p rat)
                  rat))
  :hints (("Goal" :in-theory (enable round-positive-subnormal-ties-to-even representable-positive-subnormalp))))

;; Rounding always returns a floating-point-datum (perhaps infinity or 0).
(defthm floating-point-datump-of-round-positive-rational-ties-to-even
  (implies (and (formatp k p)
                (rationalp rat)
                (< 0 rat))
           (floating-point-datump k p (round-positive-rational-ties-to-even k p rat)))
  :hints (("Goal" :in-theory (e/d (floating-point-datump
                                   representable-nonzero-rationalp
                                   representable-normalp
                                   representable-subnormalp)
                                  (type-of-round-positive-rational-ties-to-even))
           :use type-of-round-positive-rational-ties-to-even)))

(defthm not-equal-of-nan-and-round-positive-rational-ties-to-even
  (not (equal *float-nan* (round-positive-rational-ties-to-even k p rat)))
  :hints (("Goal" :in-theory (enable round-positive-rational-ties-to-even
                                     round-positive-subnormal-ties-to-even ; todo
                                     ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper function
(defund negate-floating-point-datum (datum)
  (declare (xargs :guard (weak-floating-point-datump datum)
                  :guard-hints (("Goal" :in-theory (enable weak-floating-point-datump)))))
  (cond ((equal datum *float-nan*) *float-nan*)
        ((equal datum *float-positive-zero*) *float-negative-zero*)
        ((equal datum *float-negative-zero*) *float-positive-zero*)
        ((equal datum *float-positive-infinity*) *float-negative-infinity*)
        ((equal datum *float-negative-infinity*) *float-positive-infinity*)
        (t (- datum))))

;; If the rounded result is a zero, then the sign-if-0 bit determines the sign.
(defund round-rational-ties-to-even (k p rat sign-if-0)
  (declare (xargs :guard (and (formatp k p)
                              (rationalp rat)
                              (bitp sign-if-0))
                  :guard-hints (("Goal" :use (floating-point-datump-of-round-positive-rational-ties-to-even
                                               (:instance floating-point-datump-of-round-positive-rational-ties-to-even (rat (- rat))))
                                 :in-theory (e/d (round-rational-ties-to-even)
                                                 (floating-point-datump-of-round-positive-rational-ties-to-even))))))
  (if (equal 0 rat)
      (if (equal 1 sign-if-0)
          *float-negative-zero*
        *float-positive-zero*)
    (let ((result
            (if (< 0 rat)
                (round-positive-rational-ties-to-even k p rat)
              (negate-floating-point-datum (round-positive-rational-ties-to-even k p (- rat))))))
      (if (or (equal result *float-positive-zero*)
              (equal result *float-negative-zero*))
          (if (equal 1 sign-if-0)
              *float-negative-zero*
            *float-positive-zero*)
        result))))

(defthm floating-point-datump-of-round-rational-ties-to-even
  (implies (and (formatp k p)
                (rationalp rat))
           (floating-point-datump k p (round-rational-ties-to-even k p rat sign-if-0)))
  :hints (("Goal" :use (floating-point-datump-of-round-positive-rational-ties-to-even
                         (:instance floating-point-datump-of-round-positive-rational-ties-to-even (rat (- rat))))
           :in-theory (e/d (round-rational-ties-to-even floating-point-datump negate-floating-point-datum)
                           (floating-point-datump-of-round-positive-rational-ties-to-even)))))

(defthm not-equal-of-nan-and-round-rational-ties-to-even
  (not (equal *float-nan* (round-rational-ties-to-even k p rat sign-if-0)))
  :hints (("Goal" :in-theory (enable round-rational-ties-to-even negate-floating-point-datum))))

;; (local
;;   (defthm expt1
;;     (implies (integerp i)
;;              (equal (* 1/2 (expt 2 (+ 1 i)) x)
;;                     (* (expt 2 i) x)))
;;     :hints (("Goal" :in-theory (enable expt-of-+)))))

;; (local
;;   (defthm expt2
;;     (implies (integerp i)
;;              (equal (* 1/2 (expt 2 (+ 1 i)))
;;                     (* (expt 2 i))))
;;     :hints (("Goal" :in-theory (enable expt-of-+)))))

(defthm h1
  (implies (and (integerp i)
                (integerp x)
                (< x i))
           (<= x (+ -1 i))))

(defthm *-cancel
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (rationalp w)
                (< 0 W))
           (equal (equal (* z w) (* x y w))
                  (equal z (* x y)))))

(defthm expt-cancel
  (implies (and (integerp i)
                (rationalp x)
                (rationalp y))
           (equal (equal (* x y (expt 2 (+ -1 i))) (expt 2 i))
                  (equal (* x y) 2)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm mantissa-bound-linear
  (implies (and (< 0 rat)
                (rationalp rat))
           (< (* rat (/ (expt 2 (log2 rat))))
              2))
  :rule-classes :linear)

(defthm step1
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-positive-normalp k p rat))
           (<= (* rat (/ (expt 2 (log2 rat))) (expt 2 (+ -1 p)))
               (+ -1 (expt 2 p))))
  :hints (("Goal"
           :use (:instance h1
                           (i (expt 2 p))
                           (x (* rat (/ (expt 2 (log2 rat))) (expt 2 (+ -1 p)))))
           :in-theory (enable representable-positive-normalp))))

;;switches from (log2 rat) to (emax k p)
(defthm step2
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-positive-normalp k p rat))
           (<= (* rat (/ (expt 2 (emax k p))) (expt 2 (+ -1 p)))
               (+ -1 (expt 2 p))))
  :hints (("Goal"
           :use (step1
                  (:instance <-of-expt-and-expt-same-base
                             (r 2)
                             (i (+ -1 p (- (emax k p))))
                             (j (+ -1 p (- (log2 rat))))))
           :in-theory (e/d (representable-positive-normalp
                            *-of-/-of-expt-and-expt)
                           (<-of-log2-arg1
                            <-of-log2-arg2
                            <-of-expt-and-expt-same-base)))))

(defthm <-of-infinity-threshold-when-representable-positive-normalp
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-positive-normalp k p rat))
           (< rat (infinity-threshold k p)))
  :hints (("Goal"
           :use step2
;           :cases ((<= (* rat (/ (expt 2 (log2 rat))) (expt 2 (+ -1 p))) (- (expt 2 p) 1)))
           ;; :use (:instance log2-monotonic-weak
           ;;                 (x rat)
           ;;                 (y (expt 2 (emax k p))))
           :in-theory (e/d (;representable-positive-normalp
                            infinity-threshold)
                           (;distributivity
                            ;distributivity-alt
                            log2-monotonic-weak
                            )))))

;;easy
(defthm <-of-infinity-threshold-when-representable-positive-subnormalp
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-positive-subnormalp k p rat))
           (< rat (infinity-threshold k p)))
  :hints (("Goal"
           :use <-of-1-and-infinity-threshold
           :cases ((< rat 1))
           :in-theory (e/d (representable-positive-subnormalp emin)
                           (<-of-1-and-infinity-threshold)))))

;; Rounding does not change a representable number.
(defthm round-positive-rational-ties-to-even-when-representable-positive-rationalp
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-positive-rationalp k p rat))
           (equal (round-positive-rational-ties-to-even k p rat)
                  rat))
  :hints (("Goal" :in-theory (enable round-positive-rational-ties-to-even representable-positive-rationalp))))

(defthm not-representable-positive-subnormalp-when-negative
  (implies (< x 0)
           (not (representable-positive-subnormalp k p x))))

;todo: move up, but first move up supporting rules
(defthm not-representable-nonzero-rationalp-of-infinity-threshold
  (implies (formatp k p)
           (not (representable-nonzero-rationalp k p (infinity-threshold k p))))
  :hints (("Goal" :use (<-of-largest-normal-and-infinity-threshold
                         (:instance <-of-infinity-threshold-when-representable-positive-subnormalp (rat (infinity-threshold k p)))
                         (:instance largest-normal-correct (rat (infinity-threshold k p))))
           :in-theory (e/d (representable-nonzero-rationalp
                            representable-subnormalp)
                           (largest-normal-correct
                            <-of-infinity-threshold-when-representable-positive-subnormalp
                            <-of-largest-normal-and-infinity-threshold
                            formatp)))))
