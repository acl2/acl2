; Connecting our spec to similar notions from the RTL library
;
; Copyright (C) 2022-2024 Kestrel Institute
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
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/bv/rtl" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(defthm formatp-forward-to-posp-of-prec
  (implies (rtl::formatp f)
           (posp (rtl::prec f)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rtl::formatp rtl::prec))))

(defthm formatp-forward-to-<-of-1-and-prec
  (implies (rtl::formatp f)
           (< 1 (rtl::prec f)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rtl::formatp rtl::prec))))

(defthm formatp-forward-to-<=-of-2-and-prec-linear
  (implies (rtl::formatp f)
           (<= 2 (rtl::prec f)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable rtl::formatp rtl::prec))))

(defthm formatp-forward-to-posp-of-expw
  (implies (rtl::formatp f)
           (posp (rtl::expw f)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rtl::formatp rtl::expw))))

(defthm formatp-forward-to-<-of-1-and-expw
  (implies (rtl::formatp f)
           (< 1 (rtl::expw f)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rtl::formatp rtl::expw))))

(defthm formatp-forward-to-posp-of-sigw
  (implies (rtl::formatp f)
           (posp (rtl::sigw f)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rtl::formatp rtl::sigw rtl::prec))))

;; todo: use these more
;; Extract the K value from a format
(defun format-k (f)
  (declare (xargs :guard (rtl::formatp f)))
  (+ (rtl::prec f) (rtl::expw f)))

;; Extract the K value from a format
(defun format-p (f)
  (declare (xargs :guard (rtl::formatp f)))
  (rtl::prec f))

(defthm expo-becomes-log2
  (equal (rtl::expo rat)
         (if (rationalp rat)
             (if (< 0 rat)
                 (log2 rat)
               (log2 (- rat)))
           0))
  :hints (("Goal" :in-theory (enable rtl::expo log2))))

;; (defthm expo-becomes-log2-when-negative
;;   (implies (and (< rat 0)
;;                 (rationalp rat))
;;            (equal (rtl::expo rat)
;;                   (log2 (- rat))))
;;   :hints (("Goal" :in-theory (enable rtl::expo log2))))

(defthm encodingp-becomes-unsigned-byte-p
  (implies (and (rtl::formatp f)
                (not (rtl::explicitp f)))
           (equal (rtl::encodingp x f)
                  (unsigned-byte-p (format-k f) x)))
  :hints (("Goal" :in-theory (enable rtl::encodingp rtl::sigw))))

;drop?
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

;dup in ieee-floats-helpers !
(local
 (defthmd *-of-/-of-expt-and-expt
   (implies (and (integerp i)
                 (integerp j)
                 (acl2-numberp r)
                 (not (equal 0 r)))
            (equal (* (/ (expt r i)) (expt r j))
                   (expt r (+ (- i) j))))
   :hints (("Goal" :in-theory (enable expt-of-+)))))

(defthm nrepp-becomes-representable-normalp
  (implies (rtl::formatp f)
           (equal (rtl::nrepp x f)
                  (representable-normalp (format-k f) (format-p f) x)))
  :hints (("Goal" :in-theory (enable formatp representable-normalp emin emax wfn
                                     rtl::nrepp
                                     rtl::formatp rtl::bias rtl::expw rtl::prec rtl::sig rtl::exactp
                                     representable-positive-normalp
                                     *-of-/-of-expt-and-expt))))

(local (include-book "ieee-floats-helpers")) ;todo: move up, but that may break a proof -- why?


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

;drop?
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

(defthm drepp-becomes-representable-subnormalp
  (implies (rtl::formatp f)
           (equal (rtl::drepp x f)
                  (and (rationalp x)
                       (representable-subnormalp (format-k f) (format-p f) x))))
  :hints (("Goal"
           :use ((:instance not-integer-of-*-of-expt2-when-<-of-expt2-of-- (rat x) (i (+ -3 (format-p f) (expt 2 (+ -1 (format-k f) (- (format-p f)))))))
                 (:instance not-integer-of-*-of-expt2-when-<-of-expt2-of-- (rat (- x)) (i (+ -3 (format-p f) (expt 2 (+ -1 (format-k f) (- (format-p f))))))))
           :in-theory (e/d (formatp representable-subnormalp representable-positive-subnormalp emin emax wfn
                                    rtl::drepp
                                    rtl::formatp
                                    rtl::bias
                                    rtl::explicitp
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
                ;; Decoding does not give one of the 5 special kinds of floating-point-datump:
                (not (rtl::infp x f)) ; see below for this case
                (not (rtl::nanp x f)) ; see below for this case
                (not (rtl::zerp x f)) ; see below for this case
                )
           (equal (rtl::decode x f)
                  (decode-bv-float (format-k f) (format-p f) x)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Encoding a zero
(defthm zencode-becomes-encode-bv-float
  (implies (and (rtl::formatp f)
                (not (rtl::explicitp f)) ; we only handle implicit formats
                (bitp sgn))
           (equal (rtl::zencode sgn f)
                  (encode-bv-float (format-k f) (format-p f)
                                   (if (equal 0 sgn) *float-positive-zero* *float-negative-zero*)
                                   oracle)))
  :hints (("Goal" :in-theory (enable rtl::zencode encode-bv-float encode wfn encode-nonzero-rational rtl::sigw))))

;; Encoding an infinity
(defthm iencode-becomes-encode-bv-float
  (implies (and (rtl::formatp f)
                (not (rtl::explicitp f)) ; we only handle implicit formats
                (bitp sgn))
           (equal (rtl::iencode sgn f)
                  (encode-bv-float (format-k f) (format-p f)
                                   (if (equal 0 sgn) *float-positive-infinity* *float-negative-infinity*)
                                   oracle)))
  :hints (("Goal" :in-theory (enable rtl::iencode encode-bv-float encode wfn encode-nonzero-rational rtl::sigw))))

(defthm drepp-forward-to-rationalp
  (implies (rtl::drepp x f)
           (rationalp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rtl::drepp))))

(defthm nrepp-forward-to-rationalp
  (implies (rtl::nrepp x f)
           (rationalp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rtl::nrepp))))

(defthm binary-cat-of-0-arg1
  (implies (and (natp n) (natp m))
           (equal (rtl::binary-cat 0 m y n)
                  (rtl::bits y (1- n) 0)))
  :hints (("Goal" :in-theory (enable rtl::binary-cat rtl::bits))))

;; (thm
;;  (implies (and (rationalp rat)
;;                (formatp k p)
;;                (representable-positive-subnormalp k p rat))

(defthm <-of-largest-subnormal-and-smallest-positive-normal
  (implies (formatp k p)
           (< (largest-subnormal k p) (smallest-positive-normal k p)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable largest-subnormal smallest-positive-normal
                                     decode-normal-number
                                     decode-subnormal-number
                                     emin bias))))

(defthm representable-positive-subnormalp-forward-to-positive
  (implies (representable-positive-subnormalp k p rat)
           (< 0 rat))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable representable-positive-subnormalp))))

(defthm representable-positive-subnormalp-forward-to-representable-subnormalp
  (implies (representable-positive-subnormalp k p rat)
           (representable-subnormalp k p rat))
  :hints (("Goal" :in-theory (enable representable-subnormalp)))
  :rule-classes :forward-chaining)

(local
 (defthm representable-positive-subnormalp-helper
   (implies (and (rtl::formatp f)
                 (representable-positive-subnormalp (+ (rtl::expw f) (rtl::prec f))
                                                    (rtl::prec f)
                                                    x))
            (integerp (* x
                         (expt 2
                               (+ -3 (rtl::prec f)
                                  (expt 2 (+ -1 (rtl::expw f))))))))
   :hints (("Goal" :in-theory (enable representable-positive-subnormalp emin emax
                                      *-of-expt-and-/-of-expt)))))

(local
 (defthm representable-positive-subnormalp-helper-2
   (implies (and (rtl::formatp f)
                 (representable-positive-subnormalp (+ (rtl::expw f) (rtl::prec f))
                                                    (rtl::prec f)
                                                    (- x) ; note this
                                                    ))
            (integerp (* x
                         (expt 2
                               (+ -3 (rtl::prec f)
                                  (expt 2 (+ -1 (rtl::expw f))))))))
   :hints (("Goal" :in-theory (enable representable-positive-subnormalp emin emax
                                      *-of-expt-and-/-of-expt)))))

;; Encoding a denormal
(defthm dencode-becomes-encode-bv-float
  (implies (and (rtl::formatp f)
                (not (rtl::explicitp f)) ; we only handle implicit formats
                (rtl::drepp x f))
           (equal (rtl::dencode x f)
                  ;; the oracle is unused, since x is not a nan:
                  (encode-bv-float (format-k f) (format-p f) x oracle)))
  :hints (("Goal" :in-theory (e/d (rtl::dencode encode-bv-float encode wfn encode-nonzero-rational rtl::sigw
                                                rtl::sgn
                                                encode-subnormal-number
                                                rtl::bias
                                                representable-subnormalp
                                                emin emax
                                                rtl::sig
                                                *-of-expt-and-/-of-expt
                                                *-of-/-of-expt-and-expt)
                                  (bvcat-equal-rewrite-alt
                                   bvcat-equal-rewrite)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm representable-positive-normalp-forward-to-rationalp
  (implies (representable-positive-normalp k p rat)
           (rationalp rat))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable representable-positive-normalp))))

(defthm representable-normalp-forward-to-rationalp
  (implies (representable-normalp k p rat)
           (rationalp rat))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable representable-normalp))))

(local
 (defthm representable-positive-normalp-helper
   (implies (and (representable-positive-normalp (+ (rtl::expw f) (rtl::prec f))
                                                 (rtl::prec f)
                                                 x)
                 (integerp (rtl::prec f)))
            (integerp (binary-* x
                                (expt '2
                                      (binary-+ '-1
                                                (binary-+ (unary-- (log2 x))
                                                          (rtl::prec f)))))))
   :hints (("Goal" :in-theory (enable representable-positive-normalp
                                      emax emin
                                      *-of-/-of-expt-and-expt)))))

(local
 (defthm representable-positive-normalp-helper-2
   (implies (and (representable-positive-normalp (+ (rtl::expw f) (rtl::prec f))
                                                 (rtl::prec f)
                                                 (- x) ; note this
                                                 )
                 (integerp (rtl::prec f)))
            (integerp (binary-* x
                                (expt '2
                                      (binary-+ '-1
                                                (binary-+ (rtl::prec f)
                                                          (unary-- (log2 (- x)))))))))
   :hints (("Goal" :in-theory (enable representable-positive-normalp
                                      emax emin
                                      *-of-/-of-expt-and-expt)))))

(local
 (defthm bvchop-of-sum-minus-expt-alt2
   (implies (and (natp size)
                 (integerp x))
            (equal (bvchop size (+ (- (expt 2 size)) x))
                   (bvchop size x)))))

;; Encoding a normal
(defthm nencode-becomes-encode-bv-float
  (implies (and (rtl::formatp f)
                (not (rtl::explicitp f)) ; we only handle implicit formats
                (rtl::nrepp x f))
           (equal (rtl::nencode x f)
                  ;; the oracle is unused, since x is not a nan:
                  (encode-bv-float (format-k f) (format-p f) x oracle)))
  :hints (("Goal" :in-theory (e/d (rtl::nencode encode-bv-float encode wfn encode-nonzero-rational rtl::sigw
                                                rtl::sgn
                                                encode-normal-number
                                                rtl::bias
                                                representable-normalp
                                                emin emax bias
                                                rtl::sig
                                                *-of-expt-and-/-of-expt
                                                *-of-/-of-expt-and-expt)
                                  (bvcat-equal-rewrite-alt
                                   bvcat-equal-rewrite)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm infp-in-terms-of-decode-bv-float
  (implies (and (rtl::formatp f)
                (not (rtl::explicitp f)) ; we only handle implicit formats
                (rtl::encodingp x f))
           (equal (rtl::infp x f)
                  (infinityp (decode-bv-float (format-k f) (format-p f) x))))
  :hints (("Goal" :in-theory (enable infinityp
                                     rtl::infp
                                     decode-bv-float
                                     decode
                                     rtl::unsupp
                                     wfn
                                     rtl::expf
                                     rtl::manf
                                     rtl::sigw))))

(defthm nanp-in-terms-of-decode-bv-float
  (implies (and (rtl::formatp f)
                (not (rtl::explicitp f)) ; we only handle implicit formats
                (rtl::encodingp x f))
           (equal (rtl::nanp x f)
                  (equal (decode-bv-float (format-k f) (format-p f) x)
                         *float-nan*)))
  :hints (("Goal" :in-theory (enable rtl::nanp
                                     decode-bv-float
                                     decode
                                     rtl::unsupp
                                     wfn
                                     rtl::expf
                                     rtl::manf
                                     rtl::sigw))))
