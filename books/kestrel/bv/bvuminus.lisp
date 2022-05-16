; Arithmetic negation of a bit-vector
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvplus")
(include-book "bvchop")
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;; "bit-vector unary minus"
;; Compute the (modular) negation / additive inverse of X.
(defund bvuminus (size x)
  (declare (type (integer 0 *) size))
  ;; (bvminus size 0 x)
  (bvchop size (- (ifix x))))

(defthm integerp-of-bvuminus
  (integerp (bvuminus size x))
  :hints (("Goal" :in-theory (enable bvuminus))))

(defthm natp-of-bvuminus
  (natp (bvuminus size x))
  :hints (("Goal" :in-theory (enable bvuminus))))

(defthm unsigned-byte-p-of-bvuminus
  (implies (and (>= size1 size)
                (integerp size)
                (>= size 0)
                (integerp size1))
           (unsigned-byte-p size1 (bvuminus size i)))
  :hints (("Goal" :in-theory (e/d (bvuminus unsigned-byte-p) (BVCHOP-OF-MINUS)))))

(defthm bvuminus-when-arg-is-not-an-integer
  (implies (not (integerp x))
           (equal (bvuminus size x)
                  0))
  :hints (("Goal" :in-theory (enable bvuminus))))

(defthm bvuminus-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvuminus size x)
                  0))
  :hints (("Goal" :in-theory (enable bvuminus))))

(defthm bvuminus-equal-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (natp size))
           (equal (equal k (bvuminus size x))
                  (and (unsigned-byte-p size k)
                       (equal (bvuminus size k) (bvchop size x)))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p bvchop-of-sum-cases bvuminus))))

;0 is special, because its negation is always the same number (0 itself)
(defthm equal-of-0-and-bvuminus
  (equal (equal 0 (bvuminus size x))
         (equal 0 (bvchop size x)))
  :hints (("Goal" :in-theory (enable bvuminus)
           :use (:instance bvuminus-equal-constant (k 0)))))

(defthm bvuminus-of-bvuminus
  (equal (bvuminus size (bvuminus size x))
         (bvchop size x))
  :hints (("Goal" :in-theory (enable BVCHOP-WHEN-I-IS-NOT-AN-INTEGER bvchop-of-sum-cases bvuminus))))

(defthm bvuminus-of-0
  (equal (bvuminus size 0)
         0)
  :hints (("Goal" :in-theory (enable bvuminus bvchop-when-i-is-not-an-integer))))

(defthm bvuminus-when-bvchop-known-subst
  (implies (and (equal free (bvchop size x))
                (syntaxp (and (quotep free)
                              (not (quotep x)) ;prevents loops
                              )))
           (equal (bvuminus size x)
                  (bvuminus size free) ;gets computed if size is a constant
                  ))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvuminus bvchop-when-i-is-not-an-integer))))

(defthm bvchop-of-bvuminus
  (implies (and (<= size1 size2)
                ;(natp size1)
                (natp size2))
           (equal (bvchop size1 (bvuminus size2 x))
                  (bvuminus size1 x)))
  :hints (("Goal" :in-theory (e/d (bvuminus)
                                  (bvchop-of-minus)))))

(defthm bvchop-of-bvuminus-same
  (equal (bvchop size (bvuminus size x))
         (bvuminus size x))
  :hints (("Goal" :in-theory (e/d (bvuminus)
                                  (bvchop-of-minus)))))

(defthm bvuminus-of-bvchop-arg2
  (implies (and (<= size size1)
                (integerp size1))
           (equal (bvuminus size (bvchop size1 x))
                  (bvuminus size x)))
  :hints (("Goal" :in-theory (e/d (bvuminus) ()))))

(defthm bvuminus-of-bvchop-arg2-same
  (equal (bvuminus size (bvchop size x))
         (bvuminus size x))
  :hints (("Goal" :in-theory (e/d (bvuminus) ()))))

(defthm bvplus-of-bvuminus-same
  (equal (bvplus size (bvuminus size x) x)
         0)
  :hints (("Goal" :in-theory (enable bvplus bvuminus))))

(defthm bvplus-of-bvuminus-same-alt
  (equal (bvplus size x (bvuminus size x))
         0)
  :hints (("Goal" :use (:instance bvplus-of-bvuminus-same)
           :in-theory (disable bvplus-of-bvuminus-same))))

(defthm equal-of-bvuminus-and-bvchop-same
  (equal (equal (bvuminus size x)
                (bvchop size x))
         (or (equal 0 (bvchop size x))
             (equal (expt 2 (+ -1 size)) (bvchop size x))))
  :hints (("Goal" :cases ((natp size)) :in-theory (enable bvuminus))))

(defthm equal-of-bvchop-and-bvuminus-same
  (equal (equal (bvchop size x)
                (bvuminus size x))
         (or (equal 0 (bvchop size x))
             (equal (expt 2 (+ -1 size)) (bvchop size x))))
  :hints (("Goal" :cases ((natp size)) :in-theory (enable bvuminus))))

(defthm unsigned-byte-p-of-bvuminus-bigger-simple
  (implies (and (< m n)
                (natp m)
                (natp n))
           (equal (unsigned-byte-p m (bvuminus n x))
                  (or (equal 0 (bvchop n x))
                      (< (+ (expt 2 n) (- (expt 2 m)))
                         (bvchop n x)))))
  :hints (("Goal" :in-theory (enable bvuminus unsigned-byte-p))))

;rename
(defthm bvplus-of-bvuminus-same-2
  (implies (natp size)
           (equal (bvplus size x (bvplus size (bvuminus size x) y))
                  (bvchop size y)))
  :hints (("Goal" :in-theory (e/d (bvplus
                                   bvuminus bvchop-when-i-is-not-an-integer)
                                  (bvchop-of-minus)))))

;rename
(defthm bvplus-of-bvuminus-same-2-alt
  (implies (natp size)
           (equal (bvplus size (bvuminus size x) (bvplus size x y))
                  (bvchop size y)))
  :hints (("Goal" :use (:instance bvplus-of-bvuminus-same-2)
           :in-theory (disable bvplus-of-bvuminus-same-2))))



;; -(x+y) becomes -x + -y
(defthm bvuminus-of-bvplus
  (equal (bvuminus size (bvplus size x y))
         (bvplus size (bvuminus size x) (bvuminus size y)))
  :hints (("Goal" :in-theory (enable bvuminus bvplus))))

(defthm bvuminus-1
  (equal (bvuminus 1 x)
         (getbit 0 x))
  :hints (("Goal" :cases ((equal 0 x) (equal 1 x))
           :in-theory (e/d (bvuminus getbit)
                           (bvchop-1-becomes-getbit
                            slice-becomes-getbit)))))
