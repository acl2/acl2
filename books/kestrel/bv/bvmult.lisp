; A function to multiply two bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "getbit")
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

;;this should probably nfix its arguments (at least ifix them) or chop them
(defund bvmult (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (bvchop size (* (ifix x) (ifix y))))

(defthm integerp-of-bvmult
  (integerp (bvmult size x y)))

(defthm natp-of-bvmult
  (natp (bvmult size x y)))

(defthm bvmult-of-0
  (equal (bvmult size 0 k)
         0)
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvmult-of-1
  (equal (bvmult size 1 k)
         (bvchop size k))
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
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep size)))
           (equal (bvmult size x (bvmult size y z))
                  (bvmult size (bvmult size x y) z))))

;this can't loop with x a constant, because then the bvmult would have been evaluated
(defthmd bvmult-commute-constant
  (implies (syntaxp (and (quotep k)
                         (quotep size)))
           (equal (bvmult size x k)
                  (bvmult size k x))))


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
