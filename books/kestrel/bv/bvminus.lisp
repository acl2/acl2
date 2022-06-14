; A function to subtract two bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider defining bvminus in terms of bvplus and bvuminus.

(include-book "bvchop")
(include-book "bvuminus")

;; Compute the (modular) difference of X and Y.
;; TODO: Consider defining this in terms of bvplus and bvuminus.
(defund bvminus (size x y)
  (declare (type (integer 0 *) size))
  (bvchop size (- (ifix x) (ifix y))))

(defthm integerp-of-bvminus
  (integerp (bvminus size x y)))

(defthm natp-of-bvminus
  (natp (bvminus size x y)))

(defthm bvminus-when-arg2-is-not-an-integer
  (implies (not (integerp y))
           (equal (bvminus size x y)
                  (bvchop size x)))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-when-size-is-0
  (equal (bvminus 0 x y)
         0)
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvminus size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-when-size-is-not-integerp
  (implies (not (integerp size))
           (equal (bvminus size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-same
  (equal (bvminus size x x)
         0)
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-subst-value-arg-2
  (implies (and (equal (bvchop n x) k)
                (syntaxp (and (quotep k) (not (quotep x)))))
           (equal (bvminus n x y)
                  (bvminus n k y)))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-subst-value-arg-3
  (implies (and (equal (bvchop n x) k)
                (syntaxp (and (quotep k) (not (quotep x)))))
           (equal (bvminus n y x)
                  (bvminus n y k)))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable bvminus bvchop-of-sum-cases))))

(defthm bvminus-of-0
  (equal (bvminus size x 0)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthmd bvminus-of-0-arg2
  (equal (bvminus size 0 y)
         (bvuminus size y))
  :hints (("Goal" :in-theory (enable bvminus bvuminus))))

(defthm equal-of-0-and-bvminus
  (equal (equal 0 (bvminus size x y))
         (equal (bvchop size x)
                (bvchop size y)))
  :hints (("Goal" :in-theory (enable bvminus bvchop-of-sum-cases))))

(defthm unsigned-byte-p-of-bvminus-gen-better
  (implies (and (>= size1 size)
                (integerp size)
                (>= size 0)
                (integerp size1))
           (unsigned-byte-p size1 (bvminus size i j)))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-of-bvchop-arg2
  (implies (and (<= size size1)
                (integerp size1))
           (equal (bvminus size (bvchop size1 x) y)
                  (bvminus size x y)))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-of-bvchop-arg2-same
  (equal (bvminus size (bvchop size x) y)
         (bvminus size x y))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-of-bvchop-arg3
  (implies (and (<= size size1)
                (integerp size1))
           (equal (bvminus size y (bvchop size1 x))
                  (bvminus size y x)))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvminus))))

(defthm bvminus-of-bvchop-arg3-same
  (equal (bvminus size y (bvchop size x))
         (bvminus size y x))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvminus))))

(defthm bvminus-normalize-constant-arg1
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (unsigned-byte-p size k))
                (natp size) ; prevents loops
                )
           (equal (bvminus size k x)
                  (bvminus size (bvchop size k) x)))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-of-bvuminus
  (equal (bvminus size x (bvuminus size y))
         (bvplus size x y))
  :hints (("Goal" :in-theory (enable bvchop-when-i-is-not-an-integer
                                     bvchop-of-sum-cases
                                     bvplus
                                     bvuminus
                                     bvminus))))

;; Another rule may turn the RHS into a call of bvuminus.
(defthm bvminus-when-arg1-is-not-an-integer
  (implies (not (integerp x))
           (equal (bvminus size x y)
                  (bvminus size 0 y)))
  :hints (("Goal" :in-theory (enable bvminus))))

;; Should we leave this enabled?  Perhaps we should, so we only have to deal with addition and unary negation, not subtraction.
(defthm bvminus-becomes-bvplus-of-bvuminus
  (equal (bvminus size x y)
         (bvplus size x (bvuminus size y)))
  :hints (("Goal" :cases ((natp size))
           :in-theory (e/d (natp bvminus bvplus bvuminus) (bvchop-of-minus  BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)))))

(defthm bvminus-1-0
  (equal (bvminus 1 0 x)
         (getbit 0 x))
  :hints (("Goal" :cases ((equal 0 x) (equal 1 x))
           :in-theory (e/d (bvminus getbit bvchop-when-i-is-not-an-integer)
                           (bvchop-1-becomes-getbit slice-becomes-getbit)))))
