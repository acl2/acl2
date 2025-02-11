; Bitwise or
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;(include-book "bvchop")
(include-book "getbit")
(local (include-book "slice"))
(local (include-book "logior-b"))
(local (include-book "unsigned-byte-p"))

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
           :use (bvor-associative
                 (:instance bvor-associative (x y) (y x))))))

(defthmd bvor-commute-constant
  (implies (syntaxp (and (quotep y)
                         (not (quotep x))))
           (equal (bvor size x y)
                  (bvor size y x))))

(defthm bvor-of-0-arg2
  (equal (bvor size 0 x)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvor))))

;drop or disable if we are commuting constants forward...
(defthm bvor-of-0-arg3
  (equal (bvor size x 0)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvor))))

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
  :hints (("Goal" :in-theory (enable bvor))))

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

(defthm bvor-of-bvchop-same-arg2
  (equal (bvor size (bvchop size x) y)
         (bvor size x y))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-bvchop-same-arg3
  (equal (bvor size x (bvchop size y))
         (bvor size x y))
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
  :hints (("Goal" :in-theory (enable bvor getbit))))

(defthm bvor-1-of-getbit-0-arg3
  (equal (bvor 1 y (getbit 0 x))
         (bvor 1 y x))
  :hints (("Goal" :in-theory (enable bvor getbit))))

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
           :use unsigned-byte-p-of-bvor)))

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

(defthm bvor-of-constant-chop-arg2
   (implies (and (syntaxp (and (quotep x)
                               (quotep size)))
                 (not (unsigned-byte-p size x))
                 (natp size) ; prevents loops
                 )
            (equal (bvor size x y)
                   (bvor size (bvchop size x) y)))
   :hints (("Goal" :in-theory (enable bvor))))

;; may not be needed if we commute constants forward
(defthm bvor-of-constant-chop-arg3
   (implies (and (syntaxp (and (quotep y)
                               (quotep size)))
                 (not (unsigned-byte-p size y))
                 (natp size) ; prevents loops
                 )
            (equal (bvor size x y)
                   (bvor size x (bvchop size y))))
   :hints (("Goal" :in-theory (enable bvor))))

;good
(defthm slice-of-bvor
  (implies (and (< highbit size)
                (integerp size)
                (natp lowbit)
                (natp highbit))
           (equal (slice highbit lowbit (bvor size x y))
                  (bvor (+ 1 highbit (- lowbit))
                        (slice highbit lowbit x)
                        (slice highbit lowbit y))))
  :hints (("Goal" :cases ((<= lowbit highbit))
           :in-theory (enable bvor))))

(defthm bvchop-of-bvor
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (bvchop size1 (bvor size2 x y))
                  (bvor size1 x y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvchop-of-bvor-gen
  (implies (and (natp size1)
                (natp size2))
           (equal (bvchop size1 (bvor size2 x y))
                  (if (<= size1 size2)
                      (bvor size1 x y)
                     (bvor size2 x y)))))

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
                           (slice-becomes-bvchop )))))

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
                    ()))))

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



;; We do it when at least one arg is a constant
(defthm slice-of-bvor-when-constant
  (implies (and (syntaxp (and (if (quotep x) t (quotep y))
                              (quotep highbit)
                              (quotep lowbit)
                              ;; (quotep size)
                              ))
                (< highbit size)
                (integerp size)
                (natp lowbit)
                (natp highbit))
           (equal (slice highbit lowbit (bvor size x y))
                  (bvor (+ 1 highbit (- lowbit))
                        ;; at least one of these slices gets computed:
                        (slice highbit lowbit x)
                        (slice highbit lowbit y))))
  :hints (("Goal" :by slice-of-bvor)))

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
    :use (:instance unsigned-byte-p-of-logior-strong
                    (i (bvchop size x))
                    (j (bvchop size y))
                    (n i))
    :in-theory (e/d (bvor unsigned-byte-p)
                    (unsigned-byte-p-of-logior-strong)))))

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
  :hints (("Goal" :in-theory (e/d (bvor) ()))))

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
  :hints (("Goal" :in-theory (e/d (bvor) ()))))

(defthm bitp-of-bvor-of-1
  (bitp (bvor 1 x y))
  :rule-classes :type-prescription
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvor (size 1))
           :in-theory (disable unsigned-byte-p-of-bvor
                               unsigned-byte-p-of-bvor-gen))))

;bozo move hyps to conclusion?
; a bit odd
(defthm unsigned-byte-p-of-bvor2
  (implies (and (unsigned-byte-p n a)
                (unsigned-byte-p n b)
                (natp n)
                (natp size))
           (unsigned-byte-p n (bvor size a b)))
  :hints (("Goal" :in-theory (enable bvor))))

;kind of a weird rule..
(defthm unsigned-byte-p-of-bvor3
  (implies (and (< n size)
                (natp n)
                (natp size))
           (equal (unsigned-byte-p n (bvor size a b))
                  (and (unsigned-byte-p n (bvchop size a))
                       (unsigned-byte-p n (bvchop size b)))))
  :hints (("Goal" :in-theory (enable bvor))))

(defthmd bvor-tighten-free
  (implies (and (unsigned-byte-p newsize y)
                (< newsize oldsize)
                (unsigned-byte-p newsize x)
                (natp oldsize))
           (equal (bvor oldsize x y)
                  (bvor newsize x y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-slice-tighten
   (implies (and (<= size (- high low))
                 (natp size)
                 (< 0 size)
                 (natp low)
                 (natp high)
                 (integerp x)
                 (integerp y)
                 )
            (equal (bvor size x (slice high low y))
                   (bvor size x (slice (+ low size -1) low y))))
   :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-slice-tighten-alt
   (implies (and (<= size (- high low))
                 (natp size)
                 (< 0 size)
                 (natp low)
                 (natp high)
                 (integerp x)
                 (integerp y)
                 )
            (equal (bvor size (slice high low y) x)
                   (bvor size (slice (+ low size -1) low y) x)))
   :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-slice-tighten-2
  (implies (and (< size (+ 1 high (- low)))
                (< 0 size)
                (natp size)
                (natp low)
                (natp high)
                (integerp x)
                (integerp y))
           (equal (bvor size y (slice high low x))
                  (bvor size y (slice (+ low size -1) low x))))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-slice-tighten-1
   (implies (and (< size (+ 1 high (- low)))
                 (< 0 size)
                 (natp size)
                 (natp low)
                 (natp high)
                 (integerp x)
                 (integerp y))
            (equal (bvor size (slice high low x) y)
                   (bvor size (slice (+ low size -1) low x) y)))
  :hints (("Goal" :in-theory (enable bvor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvor-of-constant-arg2-when-all-ones
  (implies (and (syntaxp (and (quotep x)
                              (quotep size)))
                (equal x (+ -1 (expt 2 size)))
                (natp size))
           (equal (bvor size x y)
                  (+ -1 (expt 2 size))))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-constant-arg3-when-all-ones
  (implies (and (syntaxp (and (quotep y)
                              (quotep size)))
                (equal y (+ -1 (expt 2 size)))
                (natp size))
           (equal (bvor size x y)
                  (+ -1 (expt 2 size))))
  :hints (("Goal" :in-theory (enable bvor))))
