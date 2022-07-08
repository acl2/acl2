; Representation of floats as bit-vectors (BVs)
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: use an IEEE or FLOAT package?

;; STATUS: DRAFT

(include-book "ieee-floats")
(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/bv/bvcat-def" :dir :system)
(local (include-book "kestrel/bv/bvcat" :dir :system))

(local (in-theory (disable formatp)))

;; Recognizes an (encoded) IEEE float, represented as a BV, in a format with K total bits.
(defun bv-floatp (k bv)
  (declare (xargs :guard (posp k))) ; todo: what's the smallest allowable format?
  (unsigned-byte-p k bv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Decode a BV float, giving a floating-point datum.
(defund decode-bv-float (k p bv)
  (declare (xargs :guard (and (formatp k p)
                              (bv-floatp k bv))
                  :guard-hints (("Goal" :in-theory (enable wfn formatp)))))
  (let ((sign (getbit (+ -1 k) bv))                    ; sign bit, called "S"
        (biased-exponent (slice (+ -2 k) (+ p -1) bv)) ; biased exponent (w bits), called "E"
        (trailing-significand (bvchop (+ p -1) bv)) ; trailing significand (p-1 bits), called "T"
        )
    (decode k p sign biased-exponent trailing-significand)))

(defthm floating-point-datump-of-decode-bv-float
  (implies (formatp k p)
           (floating-point-datump k p (decode-bv-float k p bv)))
  :hints (("Goal" :in-theory (enable decode-bv-float wfn formatp))))

(defthm rationalp-of-decode-bv-float
  (implies (and (not (equal *float-nan* (decode-bv-float k p bv)))
                (not (equal *float-positive-infinity* (decode-bv-float k p bv)))
                (not (equal *float-negative-infinity* (decode-bv-float k p bv)))
                (not (equal *float-positive-zero* (decode-bv-float k p bv)))
                (not (equal *float-negative-zero* (decode-bv-float k p bv)))
                (formatp k p))
           (rationalp (decode-bv-float k p bv)))
  :hints (("Goal" :use (:instance floating-point-datump-of-decode-bv-float)
           :in-theory (e/d (floating-point-datump representable-nonzero-rationalp)
                           (floating-point-datump-of-decode-bv-float)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Encode a floating point datum in the format (K,P) as a BV.
;; The oracle determines how NaNs are encoded.
(defund encode-bv-float (k p datum oracle)
  (declare (xargs :guard (and (formatp k p)
                              (floating-point-datump k p datum))
                  :guard-hints (("Goal" :in-theory (enable formatp)))))
  (mv-let (sign biased-exponent trailing-significand)
    (encode k p datum oracle)
    (bvcat 1
           sign
           (+ (wfn k p) (+ -1 p))
           (bvcat (wfn k p)
                  biased-exponent
                  (+ -1 p) ; leading digit is implicit
                  trailing-significand))))

(defthm bv-floatp-of-encode-bv-float
  (implies (formatp k p)
           (bv-floatp k (encode-bv-float k p datum oracle)))
  :hints (("Goal" :in-theory (enable encode-bv-float wfn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inversion
;; TODO: What to prove about the NaN case?
(defthm encode-bv-float-of-decode-bv-float-when-not-nan
  (implies (and (not (equal *float-nan* (decode-bv-float k p bv))) ; this case
                (bv-floatp k bv)
                (formatp k p))
           (equal (encode-bv-float k p (decode-bv-float k p bv) oracle)
                  bv))
  :hints (("Goal" :in-theory (enable encode-bv-float decode-bv-float wfn formatp))))

;; Inversion
(defthm decode-bv-float-of-encode-bv-float
  (implies (and (floating-point-datump k p datum)
                (formatp k p))
           (equal (decode-bv-float k p (encode-bv-float k p datum oracle))
                  datum))
  :hints (("Goal" :in-theory (enable encode-bv-float decode-bv-float formatp wfn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Perform a "less than" comparison on two BV floats, in the format (K,P).
(defund bv-float-< (k p x y)
  (declare (xargs :guard (and (formatp k p)
                              (bv-floatp k x)
                              (bv-floatp k y))))
  (floating-point-datum-< k p (decode-bv-float k p x) (decode-bv-float k p y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Perform a "greater than" comparison on two BV floats, in the format (K,P).
(defund bv-float-> (k p x y)
  (declare (xargs :guard (and (formatp k p)
                              (bv-floatp k x)
                              (bv-floatp k y))))
  (bv-float-< k p y x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a 32-bit IEEE float, represented as a BV
(defun bv-float32p (f)
  (declare (xargs :guard t))
  (bv-floatp 32 f))

(defund decode-bv-float32 (f)
  (declare (xargs :guard (bv-float32p f)))
  (decode-bv-float *binary32-k* *binary32-p* f))

;todo: make specialized versions of floating-point-datump
(defthm floating-point-datump-of-decode-bv-float32
  (floating-point-datump 32 24 (decode-bv-float32 x))
  :hints (("Goal" :in-theory (enable decode-bv-float32))))

(defthm rationalp-of-decode-bv-float32
  (implies (and (not (equal *float-nan* (decode-bv-float32 x)))
                (not (equal *float-positive-infinity* (decode-bv-float32 x)))
                (not (equal *float-negative-infinity* (decode-bv-float32 x)))
                (not (equal *float-positive-zero* (decode-bv-float32 x)))
                (not (equal *float-negative-zero* (decode-bv-float32 x))))
           (rationalp (decode-bv-float32 x)))
  :hints (("Goal" :in-theory (enable decode-bv-float32))))

;; TODO: Encode and inversion theorems

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a 64-bit IEEE float, represented as a BV
(defun bv-float64p (d)
  (declare (xargs :guard t))
  (bv-floatp 64 d))

(defund decode-bv-float64 (f)
  (declare (xargs :guard (bv-float64p f)))
  (decode-bv-float *binary64-k* *binary64-p* f))

(defthm floating-point-datump-of-decode-bv-float64
  (floating-point-datump 64 53 (decode-bv-float64 x))
  :hints (("Goal" :in-theory (enable decode-bv-float64))))

(defthm rationalp-of-decode-bv-float64
  (implies (and (not (equal *float-nan* (decode-bv-float64 x)))
                (not (equal *float-positive-infinity* (decode-bv-float64 x)))
                (not (equal *float-negative-infinity* (decode-bv-float64 x)))
                (not (equal *float-positive-zero* (decode-bv-float64 x)))
                (not (equal *float-negative-zero* (decode-bv-float64 x))))
           (rationalp (decode-bv-float64 x)))
  :hints (("Goal" :in-theory (enable decode-bv-float64))))

;; TODO: Encode and inversion theorems

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
