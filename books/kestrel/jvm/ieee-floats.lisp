; Partial spec of IEEE 754 floating point values and operations
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: use an IEEE package?

;; STATUS: In-PROGRESS

;; TODO: Add comparisons, rounding, etc.

;; Reference: IEEE Std 754-2019: IEEE Standard for Floating-Point Arithmetic

(include-book "kestrel/arithmetic-light/log2" :dir :system)
(Local (include-book "ieee-floats-helpers"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/divides" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(in-theory (disable mv-nth))

;; These are constants so that we don't mistype the keyword by accident.
;; These are the same for all formats.
(defconst *float-positive-zero* :float-positive-zero)
(defconst *float-negative-zero* :float-negative-zero)
(defconst *float-positive-infinity* :float-positive-infinity)
(defconst *float-negative-infinity* :float-negative-infinity)
(defconst *float-nan* :float-NaN) ; "not a number"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; K is the total number of bits, and P is the number of bits of precision.  K
;; and P together define a floating-point format, denoted (K,P).
;; TODO: What is the mininum size of a format?
(defun formatp (k p)
  (declare (xargs :guard t))
  (and (integerp k)
       (posp p) ; if p were 0, there would be -1 bits in the trailing significand
       (< p k) ; if p were equal to k, there would be no room for a sign bit
       ))

;; See Table 3.5:

(defconst *binary16-k* 16) ; storage width
(defconst *binary16-p* 11) ; precision

(defconst *binary32-k* 32) ; storage width
(defconst *binary32-p* 24) ; precision

(defconst *binary64-k* 64) ; storage width
(defconst *binary64-p* 53) ; precision

(defconst *binary128-k* 128) ; storage width
(defconst *binary128-p* 113) ; precision

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Maximum exponent
(defund emax (k p)
  (declare (xargs :guard (formatp k p)))
  (- (expt 2 (+ k (- p) -1))
     1))

(defthm integerp-of-emax
  (implies (formatp k p)
           (integerp (emax k p)))
  :hints (("Goal" :in-theory (enable emax))))

;; Check the values in Table 3.5:
(thm (equal (emax *binary16-k* *binary16-p*) 15))
(thm (equal (emax *binary32-k* *binary32-p*) 127))
(thm (equal (emax *binary64-k* *binary64-p*) 1023))
(thm (equal (emax *binary128-k* *binary128-p*) 16383))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Minimum exponent
;; See 3.3
(defund emin (k p)
  (declare (xargs :guard (formatp k p)))
  (- 1 (emax k p)))

(defthm integerp-of-emin
  (implies (formatp k p)
           (integerp (emin k p)))
  :hints (("Goal" :in-theory (enable emin))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Exponent bias
(defund bias (k p)
  (declare (xargs :guard (formatp k p)))
  (emax k p))

(defthm integerp-of-bias
  (implies (formatp k p)
           (integerp (bias k p)))
  :hints (("Goal" :in-theory (enable bias))))

;; Check the values in Table 3.5:
(thm (equal (bias *binary16-k* *binary16-p*) 15))
(thm (equal (bias *binary32-k* *binary32-p*) 127))
(thm (equal (bias *binary64-k* *binary64-p*) 1023))
(thm (equal (bias *binary128-k* *binary128-p*) 16383))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Width of exponent field ("w function")
;; todo: rename to w once we have a FLOAT package
(defund wfn (k p)
  (declare (xargs :guard (formatp k p)))
  (- k p))

(defthm integerp-of-wfn
  (implies (and (integerp k)
                (integerp p))
           (integerp (wfn k p)))
  :hints (("Goal" :in-theory (enable wfn))))

;; Check the values in Table 3.5:
(thm (equal (wfn *binary16-k* *binary16-p*) 5))
(thm (equal (wfn *binary32-k* *binary32-p*) 8))
(thm (equal (wfn *binary64-k* *binary64-p*) 11))
(thm (equal (wfn *binary128-k* *binary128-p*) 15))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks whether the rational RAT is representable as a positive normal (i.e.,
;; not subnormal) number in the floating-point format (K,P).
(defund representable-positive-normalp (k p rat)
  (declare (xargs :guard (and (rationalp rat)
                              (formatp k p))))
  (and (< 0 rat)
       (let* ((exponent (log2 rat)))
         (and (<= (emin k p) exponent)
              (<= exponent (emax k p))
              (let ((possible-significand (/ rat (expt 2 exponent)))) ; will be in the range [1,2]
                ;; Shift left by p-1 places, and ensure there are no 1 bits
                ;; beyond the p-1 bits immediately to the right of the radix
                ;; point:
                (integerp (* possible-significand (expt 2 (- p 1)))))))))

;; Checks whether the rational RAT is representable as a normal (i.e., not
;; subnormal) number in the floating-point format (K,P).  Note that 0 is not a
;; "normal" number (see Definitions in the standard).
(defund representable-normalp (k p rat)
  (declare (xargs :guard (and (rationalp rat)
                              (formatp k p))))
  (representable-positive-normalp k p (abs rat)))

(defthm not-representable-normalp-of-0
  (not (representable-normalp k p 0))
  :hints (("Goal" :in-theory (enable representable-positive-normalp representable-normalp))))

(defthm representable-normalp-of--
  (implies (rationalp rat)
           (equal (representable-normalp k p (- rat))
                  (representable-normalp k p rat)))
  :hints (("Goal" :in-theory (enable representable-normalp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks whether the rational RAT is representable as a positive subnormal
;; number in the floating-point format (K,P).
(defund representable-positive-subnormalp (k p rat)
  (declare (xargs :guard (and (rationalp rat)
                              (formatp k p))))
  (and (< 0 rat)
       (let* ((exponent (log2 rat))
              (emin (emin k p)))
         (and (< exponent emin)
              (let ((possible-significand (/ rat (expt 2 emin)))) ; will be in the range (0,1)
                ;; Shift left by p-1 places, and ensure there are no 1 bits
                ;; beyond the p-1 bits immediately to the right of the radix
                ;; point:
                (integerp (* possible-significand (expt 2 (- p 1)))))))))

;; Checks whether the rational RAT is representable as a subnormal number in
;; the floating-point format (K,P).
(defund representable-subnormalp (k p rat)
  (declare (xargs :guard (and (rationalp rat)
                              (formatp k p))))
  (representable-positive-subnormalp k p (abs rat)))

(defthm not-representable-subnormalp-of-0
  (not (representable-subnormalp k p 0))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable representable-positive-subnormalp representable-subnormalp))))

(defthm representable-subnormalp-of--
  (implies (rationalp rat)
           (equal (representable-subnormalp k p (- rat))
                  (representable-subnormalp k p rat)))
  :hints (("Goal" :in-theory (enable representable-subnormalp))))

;; The normals and subnormals are disjoint.
(defthm not-and-representable-normalp-and-representable-subnormalp
  (not (and (representable-normalp k p rat)
            (representable-subnormalp k p rat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable representable-normalp
                                     representable-subnormalp
                                     representable-positive-normalp
                                     representable-positive-subnormalp))))

;; Checks whether RAT is a nonzero rational number representable in the
;; floating-point format (K,P).  Note that 0 is represented differently.
(defund representable-nonzero-rationalp (k p rat)
  (declare (xargs :guard (formatp k p)))
  (and (rationalp rat)
       (or (representable-normalp k p rat)
           (representable-subnormalp k p rat))))

(defthm representable-nonzero-rationalp-of--
  (implies (rationalp rat)
           (equal (representable-nonzero-rationalp k p (- rat))
                  (representable-nonzero-rationalp k p rat)))
  :hints (("Goal" :in-theory (enable representable-nonzero-rationalp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A floating-point datum is a representable nonzero rational, or one of the 5
;; special values.
(defund floating-point-datump (k p datum)
  (declare (xargs :guard (formatp k p)))
  (or (representable-nonzero-rationalp k p datum)
      (member-eq datum (list *float-positive-zero*
                             *float-negative-zero*
                             *float-positive-infinity*
                             *float-negative-infinity*
                             *float-nan*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Decode the 3 fields (sign, biased exponent, and trailing-significant) of a
;; normal number, giving a rational.  The 3 fields must encode a normal number;
;; that is, the exponent field must not contain all zeros or all ones.
(defund decode-normal-number (k p sign biased-exponent trailing-significand)
  (declare (xargs :guard (and (formatp k p)
                              (bitp sign) ; todo bitp vs unsigned-byte-p
                              (unsigned-byte-p (wfn k p) biased-exponent)
                              (< 0 biased-exponent) ; not all zeros
                              (< biased-exponent (+ -1 (expt 2 (wfn k p)))) ; not all ones
                              (unsigned-byte-p (- p 1) trailing-significand))))
  (* (expt -1 sign)
     (expt 2 (- biased-exponent (bias k p)))
     (+ 1 ; implicit leading 1 bit
        (* (expt 2 (- 1 p))
           trailing-significand))))

(defthm rationalp-of-decode-normal-number
  (implies (rationalp trailing-significand)
           (rationalp (decode-normal-number k p sign biased-exponent trailing-significand)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable decode-normal-number))))

(defthm <-of-decode-normal-number-and-0
  (implies (and (bitp sign)
                (unsigned-byte-p (- p 1) trailing-significand))
           (equal (< (decode-normal-number k p sign biased-exponent trailing-significand) 0)
                  (equal sign 1)))
  :hints (("Goal" :in-theory (enable decode-normal-number))))

(defthm <-of-decode-normal-number-and-0-linear
  (implies (unsigned-byte-p (- p 1) trailing-significand)
           (< 0 (decode-normal-number k p 0 biased-exponent trailing-significand)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable decode-normal-number))))

(defthm <-of-decode-normal-number-of-1
  (implies (and (bitp sign)
                (unsigned-byte-p (- p 1) trailing-significand))
           (equal (decode-normal-number k p 1 biased-exponent trailing-significand)
                  (- (decode-normal-number k p 0 biased-exponent trailing-significand))))
  :hints (("Goal" :in-theory (enable decode-normal-number))))

;; might be able to prove the next one from this
(defthm representable-positive-normalp-of-decode-normal-number-of-0
  (implies (and (unsigned-byte-p (wfn k p) biased-exponent)
                (< 0 biased-exponent)                         ; not the min
                (< biased-exponent (+ -1 (expt 2 (wfn k p)))) ; not the max
                (unsigned-byte-p (- p 1) trailing-significand)
                (formatp k p))
           (representable-positive-normalp k p (decode-normal-number k p 0 biased-exponent trailing-significand)))
  :hints (("Goal" :cases ((integerp (expt 2 (+ k (- p)))))
           :in-theory (enable decode-normal-number representable-positive-normalp emin emax bias wfn unsigned-byte-p representable-normalp))))

;; Decoding gives a representable normal
(defthm representable-normalp-of-decode-normal-number
  (implies (and (bitp sign)
                (unsigned-byte-p (wfn k p) biased-exponent)
                (< 0 biased-exponent)                         ; not the min
                (< biased-exponent (+ -1 (expt 2 (wfn k p)))) ; not the max
                (unsigned-byte-p (- p 1) trailing-significand)
                (formatp k p))
           (representable-normalp k p (decode-normal-number k p sign biased-exponent trailing-significand)))
  :hints (("Goal" :cases ((integerp (expt 2 (+ k (- p)))))
           :in-theory (enable decode-normal-number representable-positive-normalp emin emax bias wfn unsigned-byte-p representable-normalp))))

;; Trivial consequence of the above
(defthm representable-nonzero-rationalp-of-decode-normal-number
  (implies (and (bitp sign)
                (unsigned-byte-p (wfn k p) biased-exponent)
                (< 0 biased-exponent)                         ; not the min
                (< biased-exponent (+ -1 (expt 2 (wfn k p)))) ; not the max
                (unsigned-byte-p (- p 1) trailing-significand)
                (formatp k p))
           (representable-nonzero-rationalp k p (decode-normal-number k p sign biased-exponent trailing-significand)))
  :hints (("Goal" :in-theory (enable representable-nonzero-rationalp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Decode the 2 relevant fields (sign and trailing-significant) of a subnormal
;; number, giving a rational. Note that the exponent field is not needed (it
;; will always be zero when this is called).
(defund decode-subnormal-number (k p sign trailing-significand)
  (declare (xargs :guard (and (formatp k p)
                              (bitp sign)
                              (unsigned-byte-p (- p 1) trailing-significand)
                              (< 0 trailing-significand) ; all zeros would represent a signed zero
                              )))
  (* (expt -1 sign)
     (expt 2 (emin k p))
     (+ 0 ; implicit leading 0 bit
        (* (expt 2 (- 1 p))
           trailing-significand))))

(defthm rationalp-of-decode-subnormal-number
  (implies (rationalp trailing-significand)
           (rationalp (decode-subnormal-number k p sign trailing-significand)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable decode-subnormal-number))))

;; might be able to prove the next one from this
(defthm representable-positive-normalp-of-decode-subnormal-number-of-0
  (implies (and (unsigned-byte-p (- p 1) trailing-significand)
                (< 0 trailing-significand) ; all zeros would represent a signed zero
                (formatp k p))
           (representable-positive-subnormalp k p (decode-subnormal-number k p 0 trailing-significand)))
  :hints (("Goal" :cases ((integerp (expt 2 (+ k (- p)))))
           :in-theory (enable decode-subnormal-number representable-positive-subnormalp emin emax bias wfn unsigned-byte-p representable-subnormalp))))

;; Decoding gives a representable subnormal
(defthm representable-subnormalp-of-decode-subnormal-number
  (implies (and (bitp sign)
                (unsigned-byte-p (- p 1) trailing-significand)
                (< 0 trailing-significand)
                (formatp k p))
           (representable-subnormalp k p (decode-subnormal-number k p sign trailing-significand)))
  :hints (("Goal" :in-theory (enable decode-subnormal-number representable-positive-subnormalp emin emax bias wfn unsigned-byte-p representable-subnormalp))))

;; Trivial consequence of the above
(defthm representable-nonzero-rationalp-of-decode-subnormal-number
  (implies (and (bitp sign)
                (unsigned-byte-p (- p 1) trailing-significand)
                (< 0 trailing-significand)
                (formatp k p))
           (representable-nonzero-rationalp k p (decode-subnormal-number k p sign trailing-significand)))
  :hints (("Goal" :in-theory (enable representable-nonzero-rationalp))))

(defthm <-of-decode-subnormal-number-and-0
  (implies (and (bitp sign)
                (unsigned-byte-p (- p 1) trailing-significand)
                (< 0 trailing-significand) ; all zeros would represent a signed zero
                )
           (equal (< (decode-subnormal-number k p sign trailing-significand) 0)
                  (equal sign 1)))
  :hints (("Goal" :in-theory (enable decode-subnormal-number))))

(defthm <-of-decode-subnormal-number-and-0-linear
  (implies (and (unsigned-byte-p (- p 1) trailing-significand)
                (< 0 trailing-significand) ; all zeros would represent a signed zero
                )
           (< 0 (decode-subnormal-number k p 0 trailing-significand)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable decode-subnormal-number))))

(defthm <-of-decode-subnormal-number-of-1
  (implies (and (bitp sign)
                (unsigned-byte-p (- p 1) trailing-significand))
           (equal (decode-subnormal-number k p 1 trailing-significand)
                  (- (decode-subnormal-number k p 0 trailing-significand))))
  :hints (("Goal" :in-theory (enable decode-subnormal-number))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Given the 3 components, decode them, returning a floating-point datum.
;; TODO: Compare to parse-float in class-file-parser.lisp
(defund decode (k
                p
                sign                 ; sign bit, called "S"
                biased-exponent      ; biased exponent (w bits), called "E"
                trailing-significand ; trailing significand (p-1 bits), called "T"
                )
  (declare (xargs :guard (and (formatp k p)
                              (bitp sign)
                              (unsigned-byte-p (wfn k p) biased-exponent)
                              (unsigned-byte-p (- p 1) trailing-significand))
                  :guard-hints (("Goal" :in-theory (enable wfn unsigned-byte-p)))))
  (let ((w (wfn k p)))
    (if (= biased-exponent (+ (expt 2 w) -1)) ;all ones for exponent
        (if (= 0 trailing-significand)
            ;; an infinity:
            (if (= 1 sign)
                *float-negative-infinity*
              *float-positive-infinity*)
          ;; a NaN:
          *float-nan*)
      (if (= biased-exponent 0)
          (if (= trailing-significand 0)
              ;; a signed zero:
              (if (= 1 sign)
                  *float-negative-zero*
                *float-positive-zero*)
            ;; a subnormal number:
            (decode-subnormal-number k p sign trailing-significand))
        ;; a normal number:
        (decode-normal-number k p sign biased-exponent trailing-significand)))))

(defthm floating-point-datump-of-decode
  (implies (and (bitp sign)
                (unsigned-byte-p (wfn k p) biased-exponent)
                (unsigned-byte-p (- p 1) trailing-significand)
                (formatp k p))
           (floating-point-datump k p (decode k p sign biased-exponent trailing-significand)))
  :hints (("Goal" :in-theory (enable decode floating-point-datump unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Encodes a representable normal rational, giving the 3 fields.
;; Returns (mv sign biased-exponent trailing-significand).
(defund encode-normal-number (k p rat)
  (declare (xargs :guard (and (formatp k p)
                              (rationalp rat)
                              (representable-normalp k p rat))))
  (let* ((sign (if (< rat 0) 1 0))
         (rat (abs rat))
         (exponent (log2 rat))
         (significand (/ rat (expt 2 exponent))) ; will be in the range [1,2)
         (trailing-significand (* (- significand 1)
                                  (expt 2 (- p 1)))))
    (mv sign (+ exponent (bias k p)) trailing-significand)))

(defthm encode-normal-number-type
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-normalp k p rat))
           (mv-let (sign biased-exponent trailing-significand)
             (encode-normal-number k p rat)
             (and (bitp sign)
                  (unsigned-byte-p (wfn k p) biased-exponent)
                  (< 0 biased-exponent) ; not all zeros
                  (< biased-exponent (+ -1 (expt 2 (wfn k p)))) ; not all ones
                  (unsigned-byte-p (- p 1) trailing-significand))))
  :hints (("Goal" :in-theory (enable encode-normal-number representable-normalp representable-positive-normalp
                                     wfn bias emax emin
                                     unsigned-byte-p
                                     expt-of-+))))

(defthm encode-normal-number-of-decode-normal-number
  (implies (and (bitp sign)
                (unsigned-byte-p (wfn k p) biased-exponent)
                (< 0 biased-exponent)                         ; not the min
                (< biased-exponent (+ -1 (expt 2 (wfn k p)))) ; not the max
                (unsigned-byte-p (- p 1) trailing-significand)
                (formatp k p))
           (equal (encode-normal-number k p (decode-normal-number k p sign biased-exponent trailing-significand))
                  (mv sign biased-exponent trailing-significand)))
  :hints (("Goal" :in-theory (enable decode-normal-number encode-normal-number bias wfn emax unsigned-byte-p))))

(defthm decode-normal-number-of-encode-normal-number
  (implies (and (rationalp rat)
                (representable-normalp k p rat)
                (formatp k p))
           (mv-let (sign biased-exponent trailing-significand)
             (encode-normal-number k p rat)
             (equal (decode-normal-number k p sign biased-exponent trailing-significand)
                    rat)))
  :hints (("Goal" :in-theory (enable decode-normal-number encode-normal-number bias wfn emax unsigned-byte-p))))

(defthm encode-normal-number-of--
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-normalp k p rat))
           (equal (encode-normal-number k p (- rat))
                  (mv-let (sign biased-exponent trailing-significand)
                    (encode-normal-number k p rat)
                    (mv (if (equal 0 sign) 1 0) ;flip the sign
                        biased-exponent
                        trailing-significand))))
  :hints (("Goal" :in-theory (enable encode-normal-number representable-normalp representable-positive-normalp))))

(defthm equal-of-mv-nth-0-of-encode-normal-number-and-0
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-normalp k p rat))
           (equal (equal 0 (mv-nth 0 (encode-normal-number k p rat)))
                  (< 0 rat)))
  :hints (("Goal" :in-theory (enable encode-normal-number representable-normalp representable-positive-normalp))))

(defthm not-equal-of-mv-nth-1-of-encode-normal-number-and-0
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-normalp k p rat))
           (not (equal 0 (mv-nth 1 (encode-normal-number k p rat)))))
  :hints (("Goal" :in-theory (e/d (encode-normal-number representable-normalp representable-positive-normalp bias emin)
                                  (<-of-log2-arg1)))))

(defthm <-of-mv-nth-1-of-encode-normal-number-linear
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-normalp k p rat))
           (<= (mv-nth 1 (encode-normal-number k p rat))
               (+ -2 (expt 2 (+ k (- p))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (encode-normal-number representable-normalp representable-positive-normalp bias emin emax)
                                  (<-of-log2-arg1
                                   <=-of-+-of-1-and-log2-arg1)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Encodes a representable subnormal rational, giving the 2 relevant fields.
;; Returns (mv sign trailing-significand).  There is no need to return the
;; biased exponent, as it is always 0.
(defund encode-subnormal-number (k p rat)
  (declare (xargs :guard (and (formatp k p)
                              (rationalp rat)
                              (representable-subnormalp k p rat))))
  (let* ((sign (if (< rat 0) 1 0))
         (rat (abs rat))
         (significand (/ rat (expt 2 (emin k p)))) ; will be in the range (0,1)
         (trailing-significand (* significand
                                  (expt 2 (- p 1)))))
    (mv sign trailing-significand)))

(defthm encode-subnormal-number-type
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-subnormalp k p rat))
           (mv-let (sign trailing-significand)
             (encode-subnormal-number k p rat)
             (and (bitp sign)
                  (unsigned-byte-p (- p 1) trailing-significand)
                  (< 0 trailing-significand))))
  :hints (("Goal" :in-theory (enable encode-subnormal-number representable-subnormalp representable-positive-subnormalp unsigned-byte-p))))

(defthm <-of-0-and-mv-nth-1-of-encode-subnormal-number-linear
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-subnormalp k p rat))
           (< 0 (mv-nth 1 (encode-subnormal-number k p rat))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable encode-subnormal-number representable-subnormalp representable-positive-subnormalp unsigned-byte-p))))

(defthm encode-subnormal-number-of-decode-subnormal-number
  (implies (and (bitp sign)
                (unsigned-byte-p (- p 1) trailing-significand)
                (< 0 trailing-significand)
                (formatp k p))
           (equal (encode-subnormal-number k p (decode-subnormal-number k p sign trailing-significand))
                  (mv sign trailing-significand)))
  :hints (("Goal" :in-theory (enable decode-subnormal-number encode-subnormal-number bias wfn emax unsigned-byte-p))))

(defthm decode-subnormal-number-of-encode-subnormal-number
  (implies (and (rationalp rat)
                (representable-subnormalp k p rat)
                (formatp k p))
           (mv-let (sign trailing-significand)
             (encode-subnormal-number k p rat)
             (equal (decode-subnormal-number k p sign trailing-significand)
                    rat)))
  :hints (("Goal" :in-theory (enable decode-subnormal-number encode-subnormal-number bias wfn emax unsigned-byte-p))))

(defthm encode-subnormal-number-of--
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-subnormalp k p rat))
           (equal (encode-subnormal-number k p (- rat))
                  (mv-let (sign trailing-significand)
                    (encode-subnormal-number k p rat)
                    (mv (if (equal 0 sign) 1 0) ;flip the sign
                        trailing-significand))))
  :hints (("Goal" :in-theory (enable encode-subnormal-number representable-subnormalp representable-positive-subnormalp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund smallest-positive-normal (k p)
  (declare (xargs :guard (and (formatp k p)
                              (< 1 (- k p)) ; must be exponent values available other than all zeros and all ones (TODO: Add to formatp?)
                              )
                  :guard-hints (("Goal" :in-theory (enable wfn unsigned-byte-p)))
                  ))
  (decode-normal-number k p
                        0                         ;positive
                        1 ; min exponent except for all zeros
                        0   ; min trailing-significand
                        ))

(defthm representable-positive-normalp-of-smallest-positive-normal
  (implies (and (formatp k p)
                (< 1 (- k p)))
           (representable-positive-normalp k p (smallest-positive-normal k p)))
  :hints (("Goal" :in-theory (enable smallest-positive-normal representable-positive-normalp decode-normal-number bias emin emax))))

(defthm smallest-positive-normal-correct
  (implies (and (representable-positive-normalp k p rat)
                (rationalp rat)
                (formatp k p))
           (<= (smallest-positive-normal k p) rat))
  :hints (("Goal" :in-theory (enable representable-positive-normalp smallest-positive-normal decode-normal-number bias emax emin
                                     <=-of-expt-of-2-when-<=-of-log2))))

(defthm <-of-smallest-positive-normal-when-representable-positive-subnormalp
  (implies (and (representable-positive-subnormalp k p rat)
                (rationalp rat)
                (formatp k p))
           (< rat (smallest-positive-normal k p)))
  :hints (("Goal" :in-theory (enable representable-positive-subnormalp smallest-positive-normal decode-normal-number bias emax emin
                                     <=-of-expt-of-2-when-<=-of-log2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate (((choose-bits-for-nan * * *) => (mv * *)))
  ;; Returns (mv sign trailing-significand).
  (local (defun choose-bits-for-nan (k p oracle)
           (declare (ignore k p oracle))
           (mv 0 ; choose 0 for the sign bit
               1 ; choose a single 1 for the trailing significand (can't choose 0)
               )))
  ;; The sign bit is a single bit:
  (defthm unsigned-byte-p-1-of-mv-nth-0-of-choose-bits-for-nan
    (implies (formatp k p)
             (bitp (mv-nth 0 (choose-bits-for-nan k p oracle)))))
  ;; The trailing significand has p-1 bits:
  (defthm unsigned-byte-p-of-mv-nth-1-of-choose-bits-for-nan
    (implies (and (formatp k p)
                  (< 1 p) ; todo: build in to formatp?
                  )
             (unsigned-byte-p (- p 1) (mv-nth 1 (choose-bits-for-nan k p oracle)))))
  ;; The trailing significand is not all zeros (all zeros would represent an infinity):
  (defthm not-equal-0-of-mv-nth-1-of-choose-bits-for-nan
    (implies (formatp k p)
             (not (equal 0 (mv-nth 1 (choose-bits-for-nan k p oracle)))))))

;; Returns (mv sign biased-exponent trailing-significand).
(defund encode-nonzero-rational (k p rat)
  (declare (xargs :guard (and (formatp k p)
                              (< 1 (- k p)) ;todo
                              (representable-nonzero-rationalp k p rat))
                  :guard-hints (("Goal" :in-theory (enable representable-nonzero-rationalp
                                                           representable-normalp
                                                           representable-subnormalp)))))
  (if (<= (smallest-positive-normal k p) (abs rat))
      (encode-normal-number k p rat)
    ;; must be a subnormal number:
    (mv-let (sign trailing-significand)
      (encode-subnormal-number k p rat)
      (mv sign 0 trailing-significand))))

;; Encodes a representable normal rational, giving the 3 fields.
;; Returns (mv sign biased-exponent trailing-significand).
;; The oracle helps select which NaN to return.
(defund encode (k p datum oracle)
  (declare (xargs :guard (and (formatp k p)
                              (< 1 (- k p)) ; todo
                              (floating-point-datump k p datum))
                  :guard-hints (("Goal" :in-theory (enable floating-point-datump
                                                           representable-nonzero-rationalp)))))
  (if (equal datum *float-positive-zero*)
      (mv 0 0 0)
    (if (equal datum *float-negative-zero*)
        (mv 1 0 0)
      (if (equal datum *float-positive-infinity*)
          (mv 0 (- (expt 2 (wfn k p)) 1) 0)
        (if (equal datum *float-negative-infinity*)
            (mv 1 (- (expt 2 (wfn k p)) 1) 0)
          (if (equal datum *float-nan*)
              (mv-let (sign trailing-significand)
                ;; There are many different ways to encode a Nan, so we use an
                ;; oracle value to choose one:
                (choose-bits-for-nan k p oracle)
                (mv sign (- (expt 2 (wfn k p)) 1) trailing-significand))
            ;; must be a (nonzero) representable rational:
            (encode-nonzero-rational k p datum)))))))

;; Inversion
;; TODO: What to prove about the NaN case?
(defthm encode-of-decode-when-not-nan
  (implies (and (not (equal *float-nan* (decode k p sign biased-exponent trailing-significand))) ; this case
                (bitp sign)
                (unsigned-byte-p (wfn k p) biased-exponent)
                (unsigned-byte-p (- p 1) trailing-significand)
                (formatp k p))
           (equal (encode k p (decode k p sign biased-exponent trailing-significand) oracle)
                  (mv sign biased-exponent trailing-significand)))
  :hints (("Goal" :in-theory (enable decode encode encode-nonzero-rational))))

;; Inversion
(defthm decode-of-encode
  (implies (and (< 1 (- k p)) ; todo
                (floating-point-datump k p datum)
                (formatp k p))
           (mv-let (sign biased-exponent trailing-significand)
             (encode k p datum oracle)
             (equal (decode k p sign biased-exponent trailing-significand)
                    datum)))
  :hints (("Goal" :in-theory (enable decode encode floating-point-datump representable-nonzero-rationalp wfn
                                     encode-nonzero-rational
                                     representable-normalp
                                     representable-subnormalp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund largest-positive-normal (k p)
  (declare (xargs :guard (and (formatp k p)
                              (< 1 (- k p)) ; must be exponent values available other than all zeros and all ones (TODO: Add to formatp?)
                              )
                  :guard-hints (("Goal" :in-theory (enable wfn unsigned-byte-p)))
                  ))
  (decode-normal-number k p
                        0                         ;positive
                        (+ -2 (expt 2 (wfn k p))) ; max exponent except for all ones
                        (+ -1 (expt 2 (- p 1)))   ; max trailing-significand
                        ))

(defthm representable-positive-normalp-of-largest-positive-normal
  (implies (and (formatp k p)
                (< 1 (- k p)))
           (representable-positive-normalp k p (largest-positive-normal k p)))
  :hints (("Goal" :in-theory (enable largest-positive-normal representable-positive-normalp decode-normal-number
                                                           bias emin emax wfn
                                                           *-of-expt-and-expt
                                                           *-of-/-of-expt-and-expt))))

;; todo: clean this up:

(local
 (defthm <-transitive
   (implies (and (< x y)
                 (< y z))
            (< x z))))

(local
 (defthm <-transitive-with-<=
   (implies (and (< x y)
                 (<= y z))
            (< x z))))

(defthmd *-of-2-and-expt
  (implies (integerp i)
           (equal (* 2 (expt 2 i))
                  (expt 2 (+ 1 i))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm <-of-expt-2-and-*-of-2-and-expt-2
  (implies (and (integerp i)
                (integerp j))
           (equal (< (expt '2 i) (binary-* '2 (expt '2 j)))
                  (< i (+ 1 j))))
  :hints (("Goal" :in-theory (enable *-of-2-and-expt))))

(local
 (defthm helper
   (implies (and (<= 1 s1)
                 (< s1 2)
                 (<= 1 s2)
                 (< s2 2)
                 (<= (* 2 e1) e2)
                 (rationalp s1)
                 (rationalp s2)
                 (rationalp e1)
                 (< 0 e1)
                 (rationalp e2)
                 (< 0 e2)
                 )
            (< (* s1 e1)
               (* s2 e2)))
   :hints (("Goal" :use (:instance <-transitive-with-<=
                                   (x (* s1 (/ s2)))
                                   (y 2)
                                   (z (* e2 (/ e1))))
            :in-theory (disable <-transitive-with-<= <-transitive)))))

(local
 (defthm helper2
   (implies (and (<= 1 s1)
                 (< s1 2)
                 (<= 1 s2)
                 (< s2 2)
                 (<= (* 2 e1) e2)
                 (rationalp s1)
                 (rationalp s2)
                 (rationalp e1)
                 (< 0 e1)
                 (rationalp e2)
                 (< 0 e2)
                 )
            (<= (* s1 e1)
                (* s2 e2)))
   :hints (("Goal" :use (:instance <-transitive-with-<=
                                   (x (* s1 (/ s2)))
                                   (y 2)
                                   (z (* e2 (/ e1))))
            :in-theory (disable <-transitive-with-<= <-transitive)))))

(defthm <-of-decode-normal-number-and-decode-normal-number
  (implies (and (formatp k p)
                (bitp sign1)
                (unsigned-byte-p (wfn k p) biased-exponent1)
                (< 0 biased-exponent1)                         ; not all zeros
                (< biased-exponent1 (+ -1 (expt 2 (wfn k p)))) ; not all ones
                (unsigned-byte-p (- p 1) trailing-significand1)
                (bitp sign2)
                (unsigned-byte-p (wfn k p) biased-exponent2)
                (< 0 biased-exponent2)                         ; not all zeros
                (< biased-exponent2 (+ -1 (expt 2 (wfn k p)))) ; not all ones
                (unsigned-byte-p (- p 1) trailing-significand2))
           (equal (< (decode-normal-number k p sign1 biased-exponent1 trailing-significand1)
                     (decode-normal-number k p sign2 biased-exponent2 trailing-significand2))
                  (if (and (equal 1 sign1) (equal 0 sign2))
                      t
                    (if (and (equal 0 sign1) (equal 1 sign2))
                        nil
                      (if (and (equal 0 sign1) (equal 0 sign2))
                          ;; both positive:
                          (if (< biased-exponent1 biased-exponent2)
                              t
                            (if (< biased-exponent2 biased-exponent1)
                                nil
                              ;; exponents are the same:
                              (< trailing-significand1 trailing-significand2)))
                        ;; both negative:
                        (if (< biased-exponent1 biased-exponent2)
                            nil
                          (if (< biased-exponent2 biased-exponent1)
                              t
                            ;; exponents are the same:
                            (< trailing-significand2 trailing-significand1))))))))
  :hints (("Goal" :in-theory (e/d (decode-normal-number
                                   <=-of-+-and-+-when-<=-and-<=
                                   <=-of-*-and-*-when-<=-and-<=)
                                  (distributivity)))))

(defthm <=-of-decode-normal-number-and-largest-positive-normal
  (implies (and (formatp k p)
                (bitp sign) ; todo bitp vs unsigned-byte-p
                (unsigned-byte-p (wfn k p) biased-exponent)
                (< 0 biased-exponent)                         ; not all zeros
                (< biased-exponent (+ -1 (expt 2 (wfn k p)))) ; not all ones
                (unsigned-byte-p (- p 1) trailing-significand))
           (<= (decode-normal-number k p
                                     sign
                                     biased-exponent
                                     trailing-significand)
               (largest-positive-normal k p)))
  :hints (("Goal" :in-theory (enable largest-positive-normal ;decode-normal-number
                                     ;;bias emin emax wfn
                                     *-of-expt-and-expt
                                     *-of-/-of-expt-and-expt))))

(defthm largest-positive-normal-correct
  (implies (and (representable-normalp k p rat)
                (rationalp rat)
                (formatp k p))
           (<= rat (largest-positive-normal k p)))
  :hints (("Goal" :use (decode-normal-number-of-encode-normal-number
                        (:instance <=-of-decode-normal-number-and-largest-positive-normal
                                   (sign (mv-nth 0 (encode-normal-number k p rat)))
                                   (biased-exponent (mv-nth 1 (encode-normal-number k p rat)))
                                   (trailing-significand (mv-nth 2 (encode-normal-number k p rat))))
                        encode-normal-number-type)
           :in-theory (e/d (representable-normalp
                            representable-positive-normalp)
                           (decode-normal-number-of-encode-normal-number
                            bitp
                            encode-normal-number-type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; TODO: Define largest subnormal, and prove properties

(defund largest-positive-subnormal (k p)
  (declare (xargs :guard (and (formatp k p)
                              (< 1 p) ; ensure there is a nonzero trailing-significand
                              )
                  :guard-hints (("Goal" :in-theory (enable wfn unsigned-byte-p)))
                  ))
  (decode-subnormal-number k p
                           0                    ;positive
                           (+ -1 (expt 2 (- p 1))) ; max trailing-significand
                           ))

(defthm <-of-decode-subnormal-number-and-decode-subnormal-number
  (implies (and (formatp k p)
                (bitp sign1)
                (unsigned-byte-p (- p 1) trailing-significand1)
                (< 0 trailing-significand1)
                (bitp sign2)
                (unsigned-byte-p (- p 1) trailing-significand2)
                (< 0 trailing-significand2))
           (equal (< (decode-subnormal-number k p sign1 trailing-significand1)
                     (decode-subnormal-number k p sign2 trailing-significand2))
                  (if (and (equal 1 sign1) (equal 0 sign2))
                      t
                    (if (and (equal 0 sign1) (equal 1 sign2))
                        nil
                      (if (and (equal 0 sign1) (equal 0 sign2))
                          ;; both positive:
                          (< trailing-significand1 trailing-significand2)
                        ;; both negative:
                        (< trailing-significand2 trailing-significand1))))))
  :hints (("Goal" :in-theory (e/d (decode-subnormal-number
                                   <=-of-+-and-+-when-<=-and-<=
                                   <=-of-*-and-*-when-<=-and-<=)
                                  (distributivity)))))

(defthm <=-of-decode-subnormal-number-and-largest-positive-subnormal
  (implies (and (formatp k p)
                (bitp sign) ; todo bitp vs unsigned-byte-p
                (unsigned-byte-p (- p 1) trailing-significand)
                (< 0 trailing-significand))
           (<= (decode-subnormal-number k p sign trailing-significand)
               (largest-positive-subnormal k p)))
  :hints (("Goal" :in-theory (enable largest-positive-subnormal ;decode-subnormal-number
                                     ;;bias emin emax wfn
                                     *-of-expt-and-expt
                                     *-of-/-of-expt-and-expt))))

(defthm largest-positive-subnormal-correct
  (implies (and (representable-subnormalp k p rat)
                (rationalp rat)
                (formatp k p))
           (<= rat (largest-positive-subnormal k p)))
  :hints (("Goal" :use (decode-subnormal-number-of-encode-subnormal-number
                        (:instance <=-of-decode-subnormal-number-and-largest-positive-subnormal
                                   (sign (mv-nth 0 (encode-subnormal-number k p rat)))
                                   (trailing-significand (mv-nth 1 (encode-subnormal-number k p rat))))
                        encode-subnormal-number-type)
           :in-theory (e/d (representable-subnormalp
                            representable-positive-subnormalp)
                           (decode-subnormal-number-of-encode-subnormal-number
                            bitp
                            encode-subnormal-number-type
                            unsigned-byte-p)))))
