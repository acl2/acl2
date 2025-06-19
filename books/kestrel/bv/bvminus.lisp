; A function to subtract two bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider defining bvminus in terms of bvplus and bvuminus.

(include-book "bvchop")
(include-book "bvuminus")
(local (include-book "slice"))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

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

(defthmd bvminus-of-0-arg1
  (equal (bvminus 0 x y)
         0)
  :hints (("Goal" :in-theory (enable bvminus bvuminus))))

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

(defthmd bvminus-of-0-arg2
  (equal (bvminus size 0 y)
         (bvuminus size y))
  :hints (("Goal" :in-theory (enable bvminus bvuminus))))

(defthm bvminus-of-0-arg3
  (equal (bvminus size x 0)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvminus))))

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
  (equal (bvminus size x (bvchop size y))
         (bvminus size x y))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvminus))))

(defthm bvminus-normalize-constant-arg2
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (unsigned-byte-p size k))
                (natp size) ; prevents loops
                )
           (equal (bvminus size k x)
                  (bvminus size (bvchop size k) x)))
  :hints (("Goal" :in-theory (enable bvminus))))

;rename
(defthm bvminus-normalize-constant-arg3
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (unsigned-byte-p size k))
                (natp size) ; prevents loops
                )
           (equal (bvminus size x k)
                  (bvminus size x (bvchop size k))))
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
                           ()))))

(defthm bvchop-of-bvminus
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (bvchop size1 (bvminus size2 y z))
                  (bvminus size1 y z)))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-of-bvplus-same-arg2
  (equal (bvminus size k (bvplus size j k))
         (bvuminus size j))
  :hints (("Goal" :in-theory (enable bvplus bvuminus bvchop-of-sum-cases bvminus))))

;; gets rid of x
(defthm bvminus-of-+-same-arg2
  (implies (and (integerp x)
                (integerp y))
           (equal (bvminus size x (+ x y))
                  (bvuminus size y)))
  :hints (("Goal" :in-theory (enable bvplus bvuminus bvchop-of-sum-cases bvminus))))

;; gets rid of x
(defthm bvminus-of-+-same-arg2-alt
  (implies (and (integerp x)
                (integerp y))
           (equal (bvminus size x (+ y x))
                  (bvuminus size y)))
  :hints (("Goal" :in-theory (enable bvplus bvuminus bvchop-of-sum-cases bvminus))))

(defthmd bvminus-of-+-arg2
  (implies (and (integerp x1)
                (integerp x2))
           (equal (bvminus size (+ x1 x2) y)
                  (bvminus size (bvplus size x1 x2) y)))
  :hints (("Goal" :in-theory (enable bvminus bvplus))))

(defthmd bvminus-of-+-arg3
  (implies (and (integerp y1)
                (integerp y2))
           (equal (bvminus size x (+ y1 y2))
                  (bvminus size x (bvplus size y1 y2))))
  :hints (("Goal" :in-theory (enable bvminus bvplus))))

(defthmd bvminus-when-equal-of-bvchop-and-bvchop
  (implies (equal (bvchop size x)
                  (bvchop size y))
           (equal (bvminus size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvminus bvchop-of-sum-cases))))

;; combines the constants
;; maybe not needed if we always go to bvuminus
(defthm bvminus-of-bvplus-of-constant-and-bvplus-of-constant
  (implies (syntaxp (and (quotep k1) (quotep k2)))
           (equal (bvminus size (bvplus size k1 x) (bvplus size k2 y))
                  (bvminus size (bvplus size (bvminus size k1 k2) x) y)))
  :hints (("Goal" :in-theory (enable bvminus bvplus))))

;; maybe not needed if we always go to bvuminus
;; (x+y)-y = x
(defthm bvminus-of-bvplus-same
  (equal (bvminus size (bvplus size x y) y)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvminus bvplus))))

;; (y+x)-y = x
(defthm bvminus-of-bvplus-same-alt
  (equal (bvminus size (bvplus size y x) y)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvminus bvplus))))

;; (y-x) + x = y
(defthm bvplus-of-bvminus-same-arg2
  (equal (bvplus size (bvminus size y x) x)
         (bvchop size y))
  :hints (("Goal" :in-theory (enable bvminus bvplus))))

;; x + (y-x) = y
(defthm bvplus-of-bvminus-same-arg3
  (equal (bvplus size x (bvminus size y x))
         (bvchop size y))
  :hints (("Goal" :in-theory (enable bvminus bvplus))))

;; (y1+x)-(y2+x) = y1-y2
;; todo: other variants of this
(defthm bvminus-of-bvplus-and-bvplus-same-2-2
  (equal (bvminus size (bvplus size y1 x) (bvplus size y2 x))
         (bvminus size y1 y2))
  :hints (("Goal" :in-theory (enable bvplus bvminus)))  ;todo: better proof?
  )

(defthm bvminus-of-constant-and-bvplus-of-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (natp size))
           (equal (bvminus size k1 (bvplus size k2 x))
                  (bvminus size
                           (bvminus size k1 k2) ;gets computed
                           x)))
  :hints (("Goal" :in-theory (enable bvminus bvplus bvchop-of-sum-cases))))

(defthm bvminus-of-bvplus-of-constant-and-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (natp size))
           (equal (bvminus size (bvplus size k1 x) k2)
                  (bvminus size
                           x
                           (bvminus size k2 k1) ;gets computed
                           )))
  :hints (("Goal" :in-theory (enable bvminus bvplus bvchop-of-sum-cases))))

(defthm bvminus-cancel-3-2
  (implies (natp size)
           (equal (bvminus size (bvplus size y (bvplus size z x)) (bvplus size w x))
                  (bvminus size (bvplus size y z) w)))
  :hints (("Goal" :in-theory (enable bvminus-becomes-bvplus-of-bvuminus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvminus-of-bvplus-tighten-arg2
  (implies (and (< size size2)
                (natp size)
                (integerp size2))
           (equal (bvminus size (bvplus size2 x y) z)
                  (bvminus size (bvplus size x y) z)))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm bvminus-of-bvplus-tighten-arg3
  (implies (and (< size size2)
                (natp size)
                (integerp size2))
           (equal (bvminus size x (bvplus size2 y z))
                  (bvminus size x (bvplus size y z))))
  :hints (("Goal" :use ((:instance bvminus-of-bvchop-arg3-same (y (bvplus size2 y z)))
                        (:instance bvminus-of-bvchop-arg3-same (y (bvplus size y z))))
           :in-theory (disable bvminus-of-bvchop-arg3-same
                               bvminus-of-bvchop-arg3
                               bvminus-becomes-bvplus-of-bvuminus))))
