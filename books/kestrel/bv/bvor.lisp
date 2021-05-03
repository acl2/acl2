; Bitwise or
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "logior-b") ; make local?
(include-book "bvchop")
(include-book "getbit")
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

(defund bvor (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (logior (bvchop size x)
          (bvchop size y)))

(defthm bvor-type
  (and (integerp (bvor size x y))
       (<= 0 (bvor size x y)))
  :rule-classes :type-prescription)

(in-theory (disable (:type-prescription bvor))) ; bvor-type is at least as good

(defthm bvor-commutative
  (equal (bvor size x y)
         (bvor size y x))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-associative
  (equal (bvor size (bvor size x y) z)
         (bvor size x (bvor size y z)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthmd bvor-commutative-2
  (equal (bvor size y (bvor size x z))
         (bvor size x (bvor size y z)))
  :hints (("Goal" :in-theory (e/d (bvor-commutative) (bvor-associative))
           :use ((:instance bvor-associative)
                 (:instance bvor-associative (x y) (y x))))))

(defthm bvor-of-0-arg2
  (equal (bvor size 0 x)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvor))))

;drop or disable if we are commuting constants forward...
(defthm bvor-of-0-arg3
  (equal (bvor size x 0)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvor))))

;; TODO: Rewrite bvor when one arg is a mask of all ones

(defthm bvor-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvor size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvor))))

;disable?
;make a cheap version?
(defthm bvor-when-size-is-not-integerp
  (implies (not (integerp size))
           (equal (bvor size x y) 0))
  :hints (("Goal" :in-theory (e/d (bvor) nil))))

(defthm bvor-when-size-is-0
  (equal (bvor 0 x y)
         0)
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-when-not-integerp-arg2
  (implies (not (integerp x))
           (equal (bvor size x y)
                  (bvchop size y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-when-not-integerp-arg3
  (implies (not (integerp y))
           (equal (bvor size x y)
                  (bvchop size x)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-bvchop-arg2
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvor size (bvchop size2 x) y)
                  (bvor size x y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-bvchop-arg3
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvor size x (bvchop size2 y))
                  (bvor size x y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-same
  (equal (bvor size x x)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-same-2
  (equal (bvor size x (bvor size x y))
         (bvor size x y))
  :hints (("Goal"
           :cases ((integerp size))
           :use (:instance bvor-associative (x x) (y x) (z y)))))

(defthm bvor-1-of-getbit-0-arg2
  (equal (bvor 1 (getbit 0 x) y)
         (bvor 1 x y))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-1-of-getbit-0-arg3
  (equal (bvor 1 y (getbit 0 x))
         (bvor 1 y x))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvchop-of-bvor-same
  (implies (natp size)
           (equal (bvchop size (bvor size x y))
                  (bvor size x y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm unsigned-byte-p-of-bvor
  (equal (unsigned-byte-p size (bvor size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm unsigned-byte-p-of-bvor-gen
  (implies (and (<= size size2)
                (natp size))
           (equal (unsigned-byte-p size2 (bvor size x y))
                  (natp size2)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p-of-bvor)
           :use (:instance unsigned-byte-p-of-bvor))))

;use trim instead?
;drop?
(defthmd bvor-of-bvchop-tighten-2
   (implies (and (< size1 size2)
                 (natp size1)
                 (natp size2)
                 (integerp y)
                 (integerp x))
            (equal (bvor size1 x (bvchop size2 y))
                   (bvor size1 x (bvchop size1 y))))
   :hints (("Goal" :in-theory (enable bvor))))

;drop?
(defthmd bvor-of-bvchop-tighten-1
   (implies (and (< size1 size2)
                 (natp size1)
                 (natp size2)
                 (integerp y)
                 (integerp x))
            (equal (bvor size1 (bvchop size2 y) x)
                   (bvor size1 (bvchop size1 y) x)))
   :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-bvchop-arg2-gen
  (implies (and (<= size size2)
                (natp size)
                (integerp size2))
           (equal (bvor size (bvchop size2 y) x)
                  (bvor size y x)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-bvchop-arg3-gen
  (implies (and (<= size size2)
                (natp size)
                (integerp size2))
           (equal (bvor size x (bvchop size2 y))
                  (bvor size x y)))
  :hints (("Goal" :in-theory (enable bvor))))

;todo: combine with other one..
(defthm bvchop-of-bvor-does-nothing
  (implies (and (<= size n)
                (integerp n)
                (natp size))
           (equal (bvchop n (bvor size x y))
                  (bvor size x y))))

(defthm getbit-of-bvor-too-high
  (implies (and (<= size n)
                (natp n)
                (natp size))
           (equal (getbit n (bvor size x y))
                  0))
  :hints (("Goal" :in-theory (enable getbit-too-high))))

(defthmd bvor-combine-constants
  (implies (syntaxp (and (quotep y) ;tested first to fail fast
                         (quotep x)
                         (quotep size)))
           (equal (bvor size x (bvor size y z))
                  (bvor size (bvor size x y) z))))

(defthm slice-of-bvor
   (implies (and (< highbit size)
                 (<= lowbit highbit)
                 (integerp size)
                 (<= 0 size)
                 (natp lowbit)
                 (natp highbit)
                 (integerp x)
                 (integerp y))
            (equal (slice highbit lowbit (bvor size x y))
                   (bvor (+ 1 highbit (- lowbit))
                            (slice highbit lowbit x)
                            (slice highbit lowbit y))))
  :hints (("Goal" :in-theory (e/d (slice bvor natp bvchop-of-logtail) (bvchop-of-logtail-becomes-slice)))))

(defthm bvchop-of-bvor
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (bvchop size1 (bvor size2 x y))
                  (bvor size1 x y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm slice-of-bvor-tighten
  (implies (and (< (+ 1 highbit) size)
;                (<= lowbit highbit)
                (integerp size)
                (< 0 size)
                (natp lowbit)
                (natp highbit)
                (integerp x)
                (integerp y))
           (equal (slice highbit lowbit (bvor size x y))
                  (slice highbit lowbit (bvor (+ 1 highbit) x y))))
  :hints (("Goal" :cases ((<= lowbit highbit))
           :in-theory (e/d (slice bvor natp bvchop-of-logtail)
                           (slice-becomes-bvchop bvchop-of-logtail-becomes-slice)))))

(defthm slice-of-bvor-too-high
  (implies (and (<= n low)
                (integerp low)
                (natp n))
           (equal (slice high low (bvor n x y))
                  0))
  :hints (("Goal" :in-theory (enable slice-too-high-is-0))))

;this one pushes the getbit through
(defthm getbit-of-bvor
  (implies (and (< n size)
                (natp n)
                (integerp size))
           (equal (getbit n (bvor size x y))
                  (bvor 1 (getbit n x) (getbit n y))))
  :hints
  (("Goal" :cases ((and (integerp x) (integerp y))
                   (and (integerp x) (not (integerp y)))
                   (and (not (integerp x)) (integerp y)))
    :in-theory (e/d (getbit)
                    (bvchop-1-becomes-getbit slice-becomes-getbit)))))

;this one does not push the getbit through
(defthm getbit-0-of-bvor
  (implies (and (< 0 size)
                (integerp size))
           (equal (getbit 0 (bvor size x y))
                  (bvor 1 x y)))
  :hints (("Goal" :cases ((integerp size)))))

(defthm bvor-numeric-bound
  (implies (and (<= (expt 2 size) k)
                (natp size))
           (< (bvor size x y) k))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvor-gen
                                  (y y) (x x) (size size) (size2 size))
           :in-theory (e/d (zip) (unsigned-byte-p-of-bvor-gen
                                  unsigned-byte-p-of-bvor)))))

;drop?
(defthm slice-of-logior
  (equal (slice low high (logior x y))
         (logior (slice low high x)
                 (slice low high y)))
  :hints (("Goal" ;:cases ((equal low high) (< low high))
           :in-theory (e/d (slice getbit)
                           (slice-becomes-bvchop
                            BVCHOP-1-BECOMES-GETBIT
                            slice-becomes-getbit
                            BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                            )))))
;good
;todo: replace the other
(defthm slice-of-bvor-gen
  (implies (and (< highbit size)
                (integerp size)
                (natp lowbit)
                (natp highbit)
                )
           (equal (slice highbit lowbit (bvor size x y))
                  (bvor (+ 1 highbit (- lowbit))
                        (slice highbit lowbit x)
                        (slice highbit lowbit y))))
  :hints (("Goal" :cases ((<= lowbit highbit))
           :in-theory (enable bvor))))

(defthm <-of-bvor-and-expt
  (implies (and (integerp x)
                (integerp y)
                (natp i)
                (natp size))
           (equal (< (bvor size x y) (expt 2 i))
                  (and (< (bvchop size x) (expt 2 i))
                       (< (bvchop size y) (expt 2 i)))))
  :hints
  (("Goal"
    :use (:instance unsigned-byte-p-of-logior
                    (i (bvchop size x))
                    (j (bvchop size y))
                    (n i))
    :in-theory (e/d (bvor unsigned-byte-p)
                    (unsigned-byte-p-of-logior)))))

;todo: gen to constant powers of 2
(defthm bvor-bound-64-hack
  (implies (and (integerp x)
                (integerp y)
                (natp size))
           (equal (< (bvor size x y) 64)
                  (and (< (bvchop size x) 64)
                       (< (bvchop size y) 64))))
  :hints (("Goal" :use (:instance <-of-bvor-and-expt (i 6))
           :in-theory (disable <-of-bvor-and-expt))))

;drop?
(defthmd bvor-logtail-arg1
  (implies (and (natp size)
                (< 0 size)
                (natp n))
           (equal (bvor size (logtail n x) y)
                  (bvor size (slice (+ -1 n size) n x) y)))
  :hints (("Goal" :in-theory (enable bvor bvchop-of-logtail-becomes-slice))))

;drop?
(defthmd bvor-logtail-arg2
  (implies (and (natp size)
                (< 0 size)
                (natp n))
           (equal (bvor size y (logtail n x))
                  (bvor size y (slice (+ -1 n size) n x))))
  :hints (("Goal" :in-theory (enable bvor bvchop-of-logtail-becomes-slice))))

;in case we are not commuting..
(defthm equal-of-bvor-and-bvor
  (equal (equal (bvor size x y) (bvor size y x))
         t))

;weird rule
(defthm unsigned-byte-p-of-bvor-2
  (implies (and (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (natp n))
           (unsigned-byte-p n (bvor m x y)))
  :hints (("Goal" :in-theory (enable bvor))))

;use trim?
(defthm bvor-of-bvor-tighten
  (implies (and (< size size2)
                (natp size)
                (natp size2)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvor size (bvor size2 x y) z)
                  (bvor size (bvor size x y) z)))
  :hints (("Goal" :in-theory (e/d (bvor) ( BVCHOP-1-BECOMES-GETBIT)))))

;use trim?
(defthm bvor-of-bvor-tighten-2
  (implies (and (< size size2)
                (natp size)
                (natp size2)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvor size z (bvor size2 x y))
                  (bvor size z (bvor size x y))))
  :hints (("Goal" :in-theory (e/d (bvor) ( BVCHOP-1-BECOMES-GETBIT)))))
