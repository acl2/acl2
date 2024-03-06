; Some validation theorems for the floating-point model
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ieee-floats-as-bvs")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-times" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system))

;; Library stuff:

(local (in-theory (disable expt)))

;; divides through by 2^low.
;; (local
;;  (defthmd <-of-+-of-expt-helper
;;    (implies (and (<= low high)
;;                  (natp low)
;;                  (natp high)
;;                  (rationalp x))
;;             (equal (< (+ (expt 2 high) (- (expt 2 low))) (* (expt 2 low) x))
;;                    (< (+ (expt 2 (- high low)) (- 1)) x)))
;;    :hints (("Goal" :in-theory (enable expt-of-+)))))

;move
(defthm equal-of-bvchop-and-constant-forward
  (implies (and (equal k (bvchop size2 x))
                (syntaxp (and (quotep k)
                              (quotep size2)))
                (unsigned-byte-p size x)
                (syntaxp (quotep size))
                (< size2 size)
                (natp size2)
                (natp size))
           (<= x (+ (- (expt 2 size) (expt 2 size2)) k)))
  :rule-classes :forward-chaining
  :hints (("Goal" :use (:instance split-bv
                                  (x x)
                                  (n size)
                                  (m size2))
           :in-theory (enable bvcat logapp bvchop-of-sum-cases unsigned-byte-p))))

(defthm <-of-bvchop-and-constant-forward
  (implies (and (< (bvchop size2 x) k)
                (syntaxp (and (quotep k)
                              (quotep size2)))
                (integerp k)
                (unsigned-byte-p size x)
                (syntaxp (quotep size))
                (< size2 size)
                (natp size2)
                (natp size))
           (< x (+ (- (expt 2 size) (expt 2 size2)) k)))
  :rule-classes :forward-chaining
  :hints (("Goal" :use (:instance split-bv
                                  (x x)
                                  (n size)
                                  (m size2))
           :in-theory (enable bvcat logapp bvchop-of-sum-cases unsigned-byte-p))))

(local
 (defthm <-of-k-when-top-bit-1
   (implies (and (syntaxp (and (variablep x)
                               (quotep k)))
                 (equal 1 (getbit 31 x))
                 (unsigned-byte-p 32 x))
            (equal (< x k)
                   (< (+ (expt 2 31) (bvchop 31 x)) k)))
   :hints (("Goal" :use (:instance split-bv
                                   (x x)
                                   (n 32)
                                   (m 31))
            :in-theory (enable bvcat logapp bvchop-of-sum-cases unsigned-byte-p)))))

;gen
(local
 (defthm bvchop-upper-bound-when-lowbits-0-linear
   (implies (and (equal k (bvchop lowsize x))
                 (equal k 0)
                 (rationalp x) ; todo
                 (< lowsize size)
                 (natp size)
                 (natp lowsize)
                 )
            (<= (bvchop size x) (+ (expt 2 size) (- (expt 2 lowsize)) k)))
   :rule-classes ((:linear :trigger-terms ((bvchop size x))))
   :hints (("Goal" :use (:instance split-bv
                                   (x (bvchop size x))
                                   (n size)
                                   (m lowsize))
            :in-theory (enable bvcat logapp bvchop-of-sum-cases unsigned-byte-p)))))

;; End of library stuff

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; From the JVM spec 4.4.4
(thm
 (implies (bv-float32p bv)
          (iff (equal *float-positive-infinity* (decode-bv-float32 bv))
               (equal bv #x7f800000)))
 :hints (("Goal" :in-theory (enable decode-bv-float32 decode-bv-float decode))))

;; From the JVM spec 4.4.4
(thm
 (implies (bv-float32p bv)
          (iff (equal *float-negative-infinity* (decode-bv-float32 bv))
               (equal bv #xff800000)))
 :hints (("Goal" :in-theory (enable decode-bv-float32 decode-bv-float decode
                                    equal-of-bvchop-when-equal-of-getbit-widen))))

;; From the JVM spec 4.4.4
(thm
 (implies (bv-float32p bv)
          (iff (equal *float-nan* (decode-bv-float32 bv))
               (or (and (<= #x7f800001 bv)
                        (<= bv #x7fffffff))
                   (and (<= #xff800001 bv)
                        (<= bv #xffffffff)))))
 :hints (("Goal" :cases ((equal 1 (getbit 31 bv))
                         (equal 0 (getbit 31 bv)))
          :in-theory (enable decode-bv-float32 decode-bv-float decode
                             equal-of-bvchop-when-equal-of-getbit-widen
                             equal-of-slice
                             ))))


;; From the Java doc for Float.MAX_VALUE:
(thm (equal (largest-normal 32 24) (* (- 2 (expt 2 -23)) (expt 2 127))))
;todo: prove things about the encoding

;; From the Java doc for Float.MIN_NORMAL:
(thm (equal (smallest-positive-normal 32 24) (expt 2 -126)))

;; From the Java doc for Float.MIN_VALUE:
(thm (equal (smallest-positive-subnormal 32 24) (expt 2 -149)))

;; From https://en.wikipedia.org/wiki/Single-precision_floating-point_format:
(thm (equal (largest-subnormal 32 24) (* (expt 2 -126) (- 1 (expt 2 -23)))))

;; The granularity of the subnormals is the smallest-positive-subnormal.
;; That is, the difference between any 2 subnormals is a multiple of this value.
(thm
  (implies (and (formatp k p)
                (rationalp rat1)
                (rationalp rat2)
                (representable-subnormalp k p rat1)
                (representable-subnormalp k p rat2))
           (equal (mod (- rat1 rat2) (smallest-positive-subnormal k p))
                  0))
  :hints (("Goal" :in-theory (enable representable-subnormalp
                                     smallest-positive-subnormal-redef
                                     representable-positive-subnormalp
                                     equal-of-0-and-mod
                                     expt-of-+))))

;; And every subnormal is a multiple of that value.
(thm
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-subnormalp k p rat))
           (equal (mod rat (smallest-positive-subnormal k p))
                  0))
  :hints (("Goal" :in-theory (enable representable-subnormalp
                                     smallest-positive-subnormal-redef
                                     representable-positive-subnormalp
                                     equal-of-0-and-mod
                                     expt-of-+))))

;; And so is every normal
(thm
  (implies (and (formatp k p)
                (rationalp rat)
                (representable-normalp k p rat))
           (equal (mod rat (smallest-positive-subnormal k p))
                  0))
  :hints (("Goal"
           :use ((:instance integerp-of-*
                            (x (* 1/2 rat (expt 2 p)
                                  (/ (expt 2 (log2 (if (< rat 0) (- rat) rat))))))
                            (y (/ (expt 2 (log2 (if (< rat 0) (- rat) rat)))
                                  (expt 2 (emin k p))))))
           :in-theory (e/d (representable-normalp
                            smallest-positive-subnormal-redef
                            representable-positive-subnormalp
                            equal-of-0-and-mod
                            expt-of-+
                            representable-positive-normalp)
                           (integerp-of-*)))))

;; And the gap between the subnormals and the normals is exactly the
;; smallest-positive-subnormal.
(thm
  (implies (formatp k p)
           (equal (- (smallest-positive-normal k p)
                     (largest-subnormal k p))
                  (smallest-positive-subnormal k p)))
  :hints (("Goal" :in-theory (enable smallest-positive-subnormal-redef
                                     smallest-positive-normal-redef
                                     largest-subnormal
                                     decode-subnormal-number))))
