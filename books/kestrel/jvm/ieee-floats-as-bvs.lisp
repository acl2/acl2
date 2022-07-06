; Representation of floats as bit-vectors (BVs)
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: use an IEEE package?

;; STATUS: DRAFT

(include-book "ieee-floats")
(include-book "kestrel/bv/getbit" :dir :system)

;; Recognizes an (encoded) IEEE float, represented as a BV, in a format with K total bits.
(defun bv-floatp (k f)
  (declare (xargs :guard (posp k))) ; todo: what's the smallest allowable format?
  (unsigned-byte-p k f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Decode an IEEE float, giving a floating-point datum.
(defund decode-bv-float (k p f)
  (declare (xargs :guard (and (formatp k p)
                              (bv-floatp k f))
                  :guard-hints (("Goal" :in-theory (enable wfn)))))
  (let ((sign (getbit (+ -1 k) f))                    ; sign bit, called "S"
        (biased-exponent (slice (+ -2 k) (+ p -1) f)) ; biased exponent (w bits), called "E"
        (trailing-significand (bvchop (+ p -1) f)) ; trailing significand (p-1 bits), called "T"
        )
    (decode k p sign biased-exponent trailing-significand)))

(defthm floating-point-datump-of-decode-bv-float
  (implies (formatp k p)
           (floating-point-datump k p (decode-bv-float k p x)))
  :hints (("Goal" :in-theory (enable decode-bv-float wfn))))

(defthm rationalp-of-decode-bv-float
  (implies (and (not (equal *float-nan* (decode-bv-float k p x)))
                (not (equal *float-positive-infinity* (decode-bv-float k p x)))
                (not (equal *float-negative-infinity* (decode-bv-float k p x)))
                (not (equal *float-positive-zero* (decode-bv-float k p x)))
                (not (equal *float-negative-zero* (decode-bv-float k p x)))
                (formatp k p))
           (rationalp (decode-bv-float k p x)))
  :hints (("Goal" :use (:instance floating-point-datump-of-decode-bv-float)
           :in-theory (e/d (floating-point-datump representable-nonzero-rationalp)
                           (floating-point-datump-of-decode-bv-float)))))

;; TODO: Encode, but how to represent NaNs?

;; TODO: Inversion theorems for decode and encode

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
