; BV Library: getbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book defines getbit, a function to extract a single bit from a bit
;; vector.  Bits are numbered starting at 0 for the least significant bit.
;; Getbit is perhaps similar to the function bitn from books/rtl.

(include-book "slice")
(include-book "getbit-def")
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/floor")) ;for FLOOR-DIVIDE-BY-same
(local (include-book "unsigned-byte-p"))

(defthm getbit-type
  (or (equal 0 (getbit n x))
      (equal 1 (getbit n x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (getbit slice)
                                  (bvchop-of-logtail-becomes-slice)))))

(in-theory (disable (:type-prescription getbit))) ;getbit-type is better

(defthm integerp-of-getbit
  (integerp (getbit index x)))

(defthm natp-of-getbit
  (natp (getbit n x)))

(defthm getbit-of-0
  (equal (getbit n 0)
         0)
  :hints (("Goal" :in-theory (enable getbit))))

(defthm getbit-0-of-getbit
  (equal (getbit 0 (getbit n x))
         (getbit n x))
  :hints (("Goal" :in-theory (e/d (getbit slice) (bvchop-of-logtail-becomes-slice)))))

;gen the 1?
(defthm bvchop-1-of-getbit
  (equal (bvchop 1 (getbit n x))
         (getbit n x))
  :hints (("Goal" :in-theory (e/d (getbit slice) (bvchop-of-logtail-becomes-slice)))))

(defthm getbit-when-val-is-not-an-integer
  (implies (not (integerp val))
           (equal (getbit n val)
                  0))
  :hints (("Goal" :in-theory (enable getbit))))

(defthm bvchop-1-becomes-getbit
  (equal (bvchop 1 x)
         (getbit 0 x))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (getbit slice)
                           (bvchop-of-logtail-becomes-slice)))))

(theory-invariant (incompatible (:rewrite bvchop-1-becomes-getbit) (:definition getbit)))

(defthm slice-becomes-getbit
  (equal (slice n n x)
         (getbit n x))
  :hints (("Goal" :in-theory (e/d (getbit) (bvchop-1-becomes-getbit)))))

(theory-invariant (incompatible (:rewrite slice-becomes-getbit) (:definition getbit)))

;justifies the correctness of some operations performed by Axe
(defthmd unsigned-byte-p-1-of-getbit
  (unsigned-byte-p 1 (getbit n x))
  :hints (("Goal" :in-theory (e/d (getbit slice)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit
                                   bvchop-of-logtail-becomes-slice)))))

(defthm unsigned-byte-p-of-getbit
  (implies (posp size)
           (unsigned-byte-p size (getbit n x)))
  :hints (("Goal" :use (:instance unsigned-byte-p-1-of-getbit)
           :in-theory (disable unsigned-byte-p-from-bounds))))

;gen the 1
;only needed by axe?
(defthm getbit-bound
  (not (< 1 (getbit n x)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-getbit (size 1) (n n))
           :in-theory (disable unsigned-byte-p-of-getbit))))

;drop?
(defthm getbit-bound-linear
  (<= (getbit n y) 1)
  :rule-classes :linear)

(in-theory (disable logtail)) ;move up

(defthm getbit-of-bvchop
  (implies (and (< m n)
                (natp m) ;drop?
                (integerp n))
           (equal (getbit m (bvchop n x))
                  (getbit m x)))
  :hints (("Goal" :cases ((natp m))
           :in-theory (e/d (getbit slice) (slice-becomes-getbit
                                           bvchop-of-logtail-becomes-slice
                                           bvchop-1-becomes-getbit
                                           logtail-of-bvchop)))))

(defthmd getbit-too-high
  (implies (unsigned-byte-p n x)
           (equal (getbit n x)
                  0))
  :hints (("Goal" :in-theory (e/d (getbit slice)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit
                                   bvchop-of-logtail-becomes-slice)))))

(defthm getbit-too-high-cheap-2
  (implies (unsigned-byte-p n x)
           (equal (getbit n x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable getbit-too-high))))

(defthm getbit-of-bvchop-too-high
  (implies (and (<= size n)
                (natp n)
                (natp size))
           (equal (getbit n (bvchop size x))
                  0))
  :hints (("Goal" :in-theory (enable getbit-too-high))))

(defthm getbit-identity
  (implies (unsigned-byte-p 1 x)
           (equal (getbit 0 x)
                  x))
  :hints (("Goal" :use (:instance bvchop-identity (i x)
                                  (size 1))
           :in-theory (disable bvchop-identity))))

(defthm getbit-identity-free
  (implies (and (unsigned-byte-p free x)
                (equal 1 free))
           (equal (getbit 0 x)
                  x))
  :hints (("Goal" :use (:instance getbit-identity)
           :in-theory (disable getbit-identity))))

(defthm high-getbit-of-getbit-is-0
  (implies (and (<= 1 m)
                (integerp m))
           (equal (getbit m (getbit n x))
                  0))
  :hints (("Goal" :in-theory (e/d (getbit slice)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit
                                   bvchop-of-logtail-becomes-slice)))))

(defthm slice-of-getbit-too-high
  (implies (and (<= 1 low)
                (integerp low))
           (equal (slice high low (getbit n x))
                  0))
  :hints (("Goal" :in-theory (e/d (getbit slice)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit
                                   bvchop-of-logtail-becomes-slice)))))

;todo gen
(defthm getbit-of-slice
  (implies (and (<= n (+ high (- low)))
                (natp n)
                (natp low)
                (integerp high)
                )
           (equal (getbit n (slice high low x))
;                  (if (<= n (+ high (- low)))
                  (getbit (+ low n) x)
;                   0)
                  ))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (getbit slice)
                           (logtail-of-bvchop-becomes-slice
                            logtail-of-bvchop
                            bvchop-of-logtail-becomes-slice
                            slice-becomes-getbit bvchop-1-becomes-getbit)))))

(defthm getbit-when-not-integerp-arg1
  (implies (not (integerp n))
           (equal (getbit n x)
                  (getbit 0 x)))
  :hints (("Goal" :in-theory (e/d (getbit slice)
                                  (bvchop-1-becomes-getbit
                                   slice-becomes-getbit
                                   bvchop-of-logtail-becomes-slice)))))

(defthm bvchop-of-getbit
  (equal (bvchop size (getbit n x))
         (if (posp size)
             (getbit n x)
           0)))

(defthm logbitp-iff-getbit
  (iff (logbitp n x)
       (equal 1 (getbit n x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logtail bvchop logbitp getbit slice oddp evenp
                                     equal-of-0-and-mod)
                           (;mod-cancel
                            bvchop-1-becomes-getbit
                            slice-becomes-bvchop
                            slice-becomes-getbit
                            ;;bvchop-of-logtail-becomes-slice
                            bvchop-of-logtail-becomes-slice
                            logtail-of-bvchop-becomes-slice)))))

(defthmd getbit-when-equal-of-constant-and-bvchop
  (implies (and (equal free (bvchop size x))
                (< n size)
                (integerp size)
                (natp n))
           (equal (getbit n x)
                  (getbit n free)
                  )))

(defthm getbit-when-equal-of-constant-and-bvchop-constant-version
  (implies (and (equal free (bvchop size x))
                (syntaxp (and (quotep free)
                              (not (quotep x)) ;prevents loops
                              (quotep n)
                              (quotep size)))
                (< n size)
                (integerp size)
                (natp n))
           (equal (getbit n x)
                  (getbit n free) ;gets computed
                  )))

(defthm getbit-of-expt
  (implies (and (< size2 size) ;other case?
                (integerp size)
                (natp size2))
           (equal (getbit size2 (expt 2 size))
                  0))
  :hints (("Goal" :in-theory (e/d (getbit slice)
                                  (bvchop-1-becomes-getbit
                                   slice-becomes-getbit
                                   bvchop-of-logtail-becomes-slice)))))

;can be useful when getbit-too-high is disabled..
(defthm getbit-of-slice-too-high
  (implies (and (> n (- high low))
                (<= low high) ;todo
                (natp n)
                (integerp x)
                (natp low)
                (natp high))
           (equal (getbit n (slice high low x))
                  0))
  :hints (("Goal" :in-theory (e/d (getbit-too-high)
                                  (slice-becomes-getbit)))))

(defthm getbit-when-n-is-negative
  (implies (< n 0)
           (equal (getbit n x)
                  (getbit 0 x)))
  :hints (("Goal" :in-theory (e/d (getbit)
                                  (bvchop-of-logtail-becomes-slice
                                   bvchop-1-becomes-getbit
                                   slice-becomes-getbit)))))

;todo: open less to prove this?
(defthm getbit-of-expt-2-n
  (implies (natp n)
           (equal (getbit n (expt 2 n)) 1))
  :hints (("Goal" :in-theory (e/d (getbit slice logtail)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit
                                   slice-becomes-bvchop
                                   bvchop-of-logtail-becomes-slice)))))

(defthm getbit-of-logtail
  (implies (and (natp n)
                (natp m))
           (equal (getbit n (logtail m x))
                  (getbit (+ m n) x)))
  :hints (("Goal" :in-theory (e/d (getbit)
                                  (bvchop-1-becomes-getbit
                                   slice-becomes-getbit)))))

(defthm getbit-of-mod-of-expt
  (implies (and (< n j) ;todo: other case
                (natp n)
                (integerp j))
           (equal (getbit n (mod i (expt 2 j)))
                  (getbit n i)))
  :hints (("Goal" :in-theory (e/d (getbit)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit
                                   slice-becomes-bvchop
                                   bvchop-of-logtail-becomes-slice)))))


;todo: rename?
;todo: gen
(defthm getbit-of-slice-gen
  (implies (and (natp n)
                (natp low)
                (natp high) ;(integerp high)
                (integerp x) ;todo
                (<= low high) ;todo
                )
           (equal (getbit n (slice high low x))
                  (if (<= n (+ high (- low)))
                      (getbit (+ low n) x)
                    0)))
    :hints (("Goal" :in-theory (enable getbit-of-slice-too-high))))

(defthm getbit-of-1
  (equal (getbit n 1)
         (if (zp n)
             1
           0))
  :hints (("Goal" :in-theory (e/d (getbit slice)
                                  (slice-becomes-getbit
                                   bvchop-of-logtail-becomes-slice
                                   bvchop-1-becomes-getbit)))))
