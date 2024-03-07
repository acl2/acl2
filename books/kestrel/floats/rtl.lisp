; Connecting our spec to similar notions from the RTL library
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ieee-floats")
(include-book "ieee-floats-as-bvs")
(include-book "rtl/rel11/lib/reps" :dir :system)
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/bv/rtl" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(defthm expo-becomes-log2
  (implies (and (< 0 rat)
                (rationalp rat))
           (equal (rtl::expo rat)
                  (log2 rat)))
  :hints (("Goal" :in-theory (enable rtl::expo log2))))

(defthm expo-becomes-log2-when-negative
  (implies (and (< rat 0)
                (rationalp rat))
           (equal (rtl::expo rat)
                  (log2 (- rat))))
  :hints (("Goal" :in-theory (enable rtl::expo log2))))

;; todo: turn around
(defthmd representable-normalp-becomes-nrepp
  (implies (and (rationalp rat)
                (formatp k p))
           (equal (representable-normalp k p rat)
                  (rtl::nrepp rat (list nil ; format doesn't store the leading bit of significand
                                        p   ; precision
                                        (wfn k p) ; exponent width
                                        ))))
  :hints (("Goal" :in-theory (enable formatp representable-normalp emin emax wfn
                                     rtl::nrepp
                                     rtl::formatp rtl::bias rtl::expw rtl::prec rtl::sig rtl::exactp
                                     representable-positive-normalp))))

(local (include-book "ieee-floats-helpers")) ;todo: move up, but that may break a proof

(local
  (defthmd *-of-expt-and-/-of-expt
    (implies (and (integerp i)
                  (integerp j))
             (equal (* (expt 2 i) (/ (expt 2 j)))
                    (expt 2 (- i j))))
    :hints (("Goal" :in-theory (enable expt-of-+)))))

(local
  (defthm <=-of-log2-when-<=-of-expt2-linear
    (implies (and (<= (expt 2 i) rat)
                  (integerp i)
                  (rationalp rat))
             (<= i (log2 rat)))
    :rule-classes :linear))

(local
  (defthm <-of-log2-when-<-of-expt2-linear
    (implies (and (< rat (expt 2 i))
                  (integerp i)
                  (rationalp rat)
                  (< 0 rat))
             (< (log2 rat) i))
    :rule-classes :linear))

;; (defthmd *-of-/-of-expt-and-expt
;;   (implies (and (integerp i)
;;                 (integerp j))
;;            (equal (* (/ (expt 2 i)) (expt 2 j))
;;                   (expt 2 (- j i))))
;;   :hints (("Goal" :in-theory (enable expt-of-+))))

(local
  (defthm not-integer-of-*-of-expt2-when-<-of-expt2-of--
    (implies (and (< rat (expt 2 (- i)))
                  (rationalp rat)
                  (< 0 rat))
             (not (integerp (* rat (expt 2 i)))))))

(local
  (defthm <-of-+-of-log2
    (implies (and (integerp i1)
                  (integerp i2)
                  (< 0 rat)
                  (rationalp rat))
             (equal (< i1 (+ (log2 rat) i2))
                    (<= (expt 2 (+ 1 (- i1 i2))) rat)))))

(local
  (defthm <-of-+-of-log2-arg1
    (implies (and (integerp i1)
                  (integerp i2)
                  (< 0 rat)
                  (rationalp rat))
             (equal (< (+ (log2 rat) i1) i2)
                    (< rat (expt 2 (- i2 i1)))))
    :hints (("Goal" :use (:instance <-of-log2-arg1 (i (- i2 i1)))
             :in-theory (disable <-of-log2-arg1)))))

;; todo: turn around
(defthmd representable-subnormalp-becomes-drepp
  (implies (and (rationalp rat)
                (formatp k p))
           (equal (representable-subnormalp k p rat)
                  (rtl::drepp rat (list nil ; formal doesn't store the leading bit of significand
                                        p   ; precision
                                        (wfn k p) ; exponent width
                                        ))))
  :hints (("Goal"
           :use ((:instance not-integer-of-*-of-expt2-when-<-of-expt2-of-- (i (+ -3 p (expt 2 (+ -1 k (- p))))))
                 (:instance not-integer-of-*-of-expt2-when-<-of-expt2-of-- (rat (- rat)) (i (+ -3 p (expt 2 (+ -1 k (- p)))))))
           :in-theory (e/d (formatp representable-subnormalp representable-positive-subnormalp emin emax wfn
                                     rtl::drepp
                                     rtl::formatp
                                     rtl::bias
                                     rtl::expw rtl::prec rtl::sig rtl::exactp
                                     *-of-expt-and-/-of-expt
                                     *-of-/-of-expt-and-expt)
                           (not-integer-of-*-of-expt2-when-<-of-expt2-of--)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Our notion of smallest positive normal agrees with RTL.
(defthm spn-becomes-smallest-positive-normal
  (implies (rtl::formatp f)
           (equal (rtl::spn f)
                  (smallest-positive-normal (+ (rtl::prec f)
                                               (rtl::expw f))
                                            (rtl::prec f))))
  :hints (("Goal" :in-theory (enable rtl::spn rtl::bias rtl::expw rtl::prec
                                     smallest-positive-normal
                                     decode-normal-number
                                     bias
                                     emax))))

;; Our notion of largest (positive) normal agrees with RTL.
(defthm lpn-becomes-largest-normal
  (implies (rtl::formatp f)
           (equal (rtl::lpn f)
                  (largest-normal (+ (rtl::prec f)
                                     (rtl::expw f))
                                  (rtl::prec f))))
  :hints (("Goal" :in-theory (enable rtl::lpn rtl::bias rtl::expw rtl::prec rtl::formatp
                                     largest-normal
                                     decode-normal-number
                                     bias
                                     emax
                                     wfn
                                     expt-of-+))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Decoding a non-zero number (not an infinity or a NAN):
(defthm decode-becomes-decode-bv-float-usual-case
  (implies (and (rtl::formatp f)
                (rtl::encodingp x f)
                (not (rtl::explicitp f))
                (equal k (+ (rtl::prec f) (rtl::expw f)))
                (equal p (rtl::prec f))
                ;; Decoding does not give one of the 5 special kinds of floating-point-datump:
                (not (rtl::infp x f)) ; see below for this case
                (not (rtl::nanp x f)) ; see below for this case
                (not (rtl::zerp x f)) ; see below for this case
                )
           (equal (rtl::decode x f)
                  (decode-bv-float k p x)))
  :hints (("Goal" :in-theory (enable decode-bv-float decode wfn decode-subnormal-number decode-normal-number
                                     emin emax bias
                                     rtl::decode rtl::ndecode rtl::ddecode
                                     rtl::expf rtl::expf rtl::sgnf
                                     rtl::encodingp
                                     rtl::formatp
                                     rtl::expw rtl::sigw
                                     rtl::prec
                                     rtl::manf
                                     rtl::bias
                                     rtl::explicitp
                                     rtl::sigf
                                     expt-of-+
                                     representable-nonzero-rationalp
                                     representable-subnormalp
                                     representable-positive-subnormalp
                                     rtl::infp
                                     rtl::nanp
                                     rtl::unsupp
                                     rtl::zerp))))

;; Decoding an infinity
(defthm decode-bv-float-infinity-case
  (implies (and (rtl::formatp f)
                (rtl::encodingp x f)
                (not (rtl::explicitp f))
                (equal k (+ (rtl::prec f) (rtl::expw f)))
                (equal p (rtl::prec f))
                (rtl::infp x f) ; this case
                )
           (equal (decode-bv-float k p x)
                  (if (equal (rtl::sgnf x f) 1)
                      *float-negative-infinity*
                    *float-positive-infinity*)))
  :hints (("Goal" :in-theory (enable decode-bv-float decode wfn decode-subnormal-number decode-normal-number
                                     emin emax bias
                                     rtl::decode rtl::ndecode rtl::ddecode
                                     rtl::expf rtl::expf rtl::sgnf
                                     rtl::encodingp
                                     rtl::formatp
                                     rtl::expw rtl::sigw
                                     rtl::prec
                                     rtl::manf
                                     rtl::bias
                                     rtl::explicitp
                                     rtl::sigf
                                     expt-of-+
                                     representable-nonzero-rationalp
                                     representable-subnormalp
                                     representable-positive-subnormalp
                                     rtl::infp
                                     rtl::nanp
                                     rtl::unsupp
                                     rtl::zerp))))

;; Decoding a NAN
(defthm decode-bv-float-nan-case
  (implies (and (rtl::formatp f)
                (rtl::encodingp x f)
                (not (rtl::explicitp f))
                (equal k (+ (rtl::prec f) (rtl::expw f)))
                (equal p (rtl::prec f))
                (rtl::nanp x f) ; this case
                )
           (equal (decode-bv-float k p x)
                  *float-nan*))
  :hints (("Goal" :in-theory (enable decode-bv-float decode wfn decode-subnormal-number decode-normal-number
                                     emin emax bias
                                     rtl::decode rtl::ndecode rtl::ddecode
                                     rtl::expf rtl::expf rtl::sgnf
                                     rtl::encodingp
                                     rtl::formatp
                                     rtl::expw rtl::sigw
                                     rtl::prec
                                     rtl::manf
                                     rtl::bias
                                     rtl::explicitp
                                     rtl::sigf
                                     expt-of-+
                                     representable-nonzero-rationalp
                                     representable-subnormalp
                                     representable-positive-subnormalp
                                     rtl::infp
                                     rtl::nanp
                                     rtl::unsupp
                                     rtl::zerp))))

;; Decoding a zero
(defthm decode-bv-float-zero-case
  (implies (and (rtl::formatp f)
                (rtl::encodingp x f)
                (not (rtl::explicitp f))
                (equal k (+ (rtl::prec f) (rtl::expw f)))
                (equal p (rtl::prec f))
                (rtl::zerp x f) ; this case
                )
           (equal (decode-bv-float k p x)
                  (if (equal (rtl::sgnf x f) 1)
                      *float-negative-zero*
                    *float-positive-zero*)))
  :hints (("Goal" :in-theory (enable decode-bv-float decode wfn decode-subnormal-number decode-normal-number
                                     emin emax bias
                                     rtl::decode rtl::ndecode rtl::ddecode
                                     rtl::expf rtl::expf rtl::sgnf
                                     rtl::encodingp
                                     rtl::formatp
                                     rtl::expw rtl::sigw
                                     rtl::prec
                                     rtl::manf
                                     rtl::bias
                                     rtl::explicitp
                                     rtl::sigf
                                     expt-of-+
                                     representable-nonzero-rationalp
                                     representable-subnormalp
                                     representable-positive-subnormalp
                                     rtl::infp
                                     rtl::nanp
                                     rtl::unsupp
                                     rtl::zerp))))
