; A function to multiply two bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "getbit")
(include-book "bvmult-def")
(local (include-book "slice"))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/lg" :dir :system))

(defthm integerp-of-bvmult
  (integerp (bvmult size x y)))

(defthm natp-of-bvmult
  (natp (bvmult size x y)))

(defthm bvmult-of-0-arg1
  (equal (bvmult 0 x y)
         0)
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvmult-of-0-arg2
  (equal (bvmult size 0 y)
         0)
  :hints (("Goal" :in-theory (enable bvmult))))

;; If we are not commuting constants forward
(defthmd bvmult-of-0-arg3
  (equal (bvmult size x 0)
         0)
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvmult-of-1-arg2
  (equal (bvmult size 1 y)
         (bvchop size y))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvmult-of-bvchop-arg3
  (equal (bvmult size x (bvchop size y))
         (bvmult size x y))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvmult))))

(defthm bvmult-commutative
  (equal (bvmult size x y)
         (bvmult size y x))
;  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable bvmult))))

;rename
(defthm bvmult-of-bvchop-arg2
  (equal (bvmult size (bvchop size x) y)
         (bvmult size x y))
  :hints (("Goal" :use (:instance bvmult-of-bvchop-arg3 (x y) (y x))
           :in-theory (disable bvmult-of-bvchop-arg3))))

(defthm getbit-0-of-bvmult
   (implies (and (< 0 size)
                 (integerp size)
                 (integerp x)
                 (integerp y))
            (equal (getbit 0 (bvmult size x y))
                   (bvmult 1 x y)))
   :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvmult-1-1
  (implies (integerp x)
           (equal (bvmult 1 1 x)
                  (bvchop 1 x)))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvchop-of-bvmult
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2)
                )
           (equal (bvchop size1 (bvmult size2 y z))
                  (bvmult size1 y z)))
  :hints (("Goal" :in-theory (enable bvmult ;bvchop-bvchop
                                   ))))

(defthm unsigned-byte-p-of-bvmult
  (implies (and (<= size2 size)
                (natp size)
                (natp size2))
           (UNSIGNED-BYTE-P SIZE (BVMULT SIZE2 Y Z)))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvmult-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvmult size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvchop-of-bvmult2
  (implies (and (<= size2 size1)
                (natp size1)
                (natp size2))
           (equal (bvchop size1 (bvmult size2 y z))
                  (bvmult size2 y z))))

(defthm bvmult-associative
  (equal (bvmult size (bvmult size x y) z)
         (bvmult size x (bvmult size y z)))
  :hints (("Goal" :in-theory (enable bvmult))))

;loop stopper?
(defthm bvmult-commutative-2
  (equal (bvmult size y (bvmult size x z))
         (bvmult size x (bvmult size y z)))
  :hints (("Goal" :in-theory (disable bvmult-associative)
           :use ((:instance bvmult-associative)
                 (:instance bvmult-associative (x y) (y x))))))

(defthm bvmult-combine-constants
  (implies (syntaxp (and (quotep y) ;I put this one first to fail fast
                         (quotep x)
                         (quotep size)))
           (equal (bvmult size x (bvmult size y z))
                  (bvmult size (bvmult size x y) z))))

;this can't loop with x a constant, because then the bvmult would have been evaluated
(defthmd bvmult-commute-constant
  (implies (syntaxp (and (quotep y)
                         (quotep size)))
           (equal (bvmult size x y)
                  (bvmult size y x))))

;; not needed if we are commuting more generally
(defthmd bvmult-commute-constant2
  (implies (syntaxp (and (quotep k)
                         (not (quotep x))))
           (equal (bvmult size x (bvmult size k y))
                  (bvmult size k (bvmult size x y)))))

(defthm bvmult-when-arg1-is-not-an-integer
  (implies (not (integerp x))
           (equal (bvmult size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvmult-when-arg2-is-not-an-integer
  (implies (not (integerp y))
           (equal (bvmult size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvmult-non-negative
  (not (< (bvmult size x y)
          0)))

(defthm bvmult-of-bvchop-1-better
  (implies (and (<= size size2)
                (natp size2))
           (equal (bvmult size (bvchop size2 x) y)
                  (bvmult size x y)))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvmult))))

(defthm bvmult-of-bvchop-2-better
  (implies (and (<= size size2)
                (natp size2))
           (equal (bvmult size y (bvchop size2 x))
                  (bvmult size y x)))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvmult))))

(defthm bvmult-subst2-constant-version
  (implies (and (equal (bvchop size2 x) y)
                (syntaxp (and (quotep y)
                              (not (quotep x))))
                (<= size size2)
                (natp size2)
                (natp size))
           (equal (bvmult size x z)
                  (bvmult size y z))))

(defthm bvmult-subst2-alt-constant-version
  (implies (and (equal (bvchop size2 x) y)
                (syntaxp (and (quotep y)
                              (not (quotep x))))
                (<= size size2)
                (natp size2)
                (natp size))
           (equal (bvmult size z x)
                  (bvmult size z y))))

(defthmd bvchop-of-*-becomes-bvmult
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop size (* x y))
                  (bvmult size x y)))
  :hints (("Goal" :in-theory (enable bvmult))))

(theory-invariant (incompatible (:rewrite bvchop-of-*-becomes-bvmult) (:definition bvmult)))

;saves us from having to chose a prefered form.  maybe i'm just being a wimp
(defthm bvmult-equal-bvchop-times-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (equal (bvmult 32 x y)
                         (bvchop 32 (* x y)))
                  t))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm equal-of-bvmult-and-*
  (implies (and (integerp x)
                (integerp y)
                (natp size))
           (equal (equal (bvmult size x y) (* x y))
                  (unsigned-byte-p size (* x y))))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm equal-of-bvmult-and-*-alt
  (implies (and (integerp x)
                (integerp y)
                (natp size))
           (equal (equal (* x y) (bvmult size x y))
                  (unsigned-byte-p size (* x y))))
  :hints (("Goal" :in-theory (enable bvmult))))

;todo: allow the sizes to differ
(defthm bvmult-of-expt
  (implies (natp size)
           (equal (bvmult size (expt 2 size) x)
                  0))
  :hints (("Goal" :in-theory (enable bvmult))))

;todo: allow the sizes to differ
(defthm bvmult-of-expt-alt
  (implies (natp size)
           (equal (bvmult size x (expt 2 size))
                  0))
  :hints (("Goal" :use bvmult-of-expt
           :in-theory (disable bvmult-of-expt))))

(defthmd getbit-of-*-becomes-getbit-of-bvmult
  (implies (and (natp n)
                (integerp x)
                (integerp y))
           (equal (getbit n (* x y))
                  (getbit n (bvmult (+ 1 n) x y))))
  :hints (("Goal" :in-theory (enable bvmult))))

(theory-invariant (incompatible (:rewrite getbit-of-*-becomes-getbit-of-bvmult) (:definition bvmult)))

(defthmd slice-of-*-becomes-slice-of-bvmult
  (implies (and (natp high)
                (natp low) ;drop?
                (integerp x)
                (integerp y))
           (equal (slice high low (* x y))
                  (slice high low (bvmult (+ 1 high) x y))))
  :hints (("Goal" :in-theory (enable bvmult))))

(theory-invariant (incompatible (:rewrite slice-of-*-becomes-slice-of-bvmult) (:definition bvmult)))

(defthm bvmult-of-ifix-arg2
  (equal (bvmult size (ifix x) y)
         (bvmult size x y))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvmult-of-ifix-arg3
  (equal (bvmult size x (ifix y))
         (bvmult size x y))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm getbit-of-bvmult-of-expt
  (implies (and (< n (+ 1 size))
                (>= size2 (+ 1 size))
                ;; (integerp x)
                (natp size)
                (natp size2)
                (natp n))
           (equal (getbit size (bvmult size2 (expt 2 n) x))
                  (getbit (- size n) x)))
  :hints (("Goal" :in-theory (enable bvmult getbit
                                     natp ;yuck
                                     ))))

(defthm getbit-of-bvmult-of-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (< (lg k) (+ 1 size))
                (>= size2 (+ 1 size))
                ;; (integerp x)
                (natp size)
                (natp size2)
                (natp (lg k)))
           (equal (getbit size (bvmult size2 k x))
                  (getbit (- size (lg k)) x)))
  :hints (("Goal" :use (:instance getbit-of-bvmult-of-expt (n (lg k)))
           :in-theory (disable getbit-of-bvmult-of-expt))))
