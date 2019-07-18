; BV Library: bvplus
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "getbit")
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "unsigned-byte-p"))

;; Compute the sum of X and Y, chopped down to SIZE bits.
(defund bvplus (size x y)
  (declare (type (integer 0 *) size))
  (bvchop size (+ (ifix x) (ifix y))))

(defthm bvplus-associative
  (equal (bvplus size (bvplus size x y) z)
         (bvplus size x (bvplus size y z)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-commutative
  (equal (bvplus size x y)
         (bvplus size y x))
  :hints (("Goal" :in-theory (enable bvplus))))

;loop stopper?
(defthm bvplus-commutative-2
  (equal (bvplus size y (bvplus size x z))
         (bvplus size x (bvplus size y z)))
  :hints (("Goal" :in-theory (disable bvplus-associative)
           :use ((:instance bvplus-associative)
                 (:instance bvplus-associative (x y) (y x))))))

;; The (bvplus size x y) in the conclusion gets computed.
(defthm bvplus-combine-constants
  (implies (syntaxp (and (quotep y) ;I put this one first to fail fast
                         (quotep x)
                         (quotep size)))
           (equal (bvplus size x (bvplus size y z))
                  (bvplus size (bvplus size x y) z))))

(defthm bvplus-of-0
  (equal (bvplus size 0 x)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvplus))))

;gen?
(defthm bvplus-of-bvchop-arg1
  (equal (bvplus size (bvchop size x) y)
         (bvplus size x y))
  :hints (("Goal" :in-theory (enable bvplus bvchop-when-i-is-not-an-integer))))

;gen?
(defthm bvplus-of-bvchop-arg2
  (equal (bvplus size x (bvchop size y))
         (bvplus size x y))
  :hints (("Goal" :in-theory (enable bvplus bvchop-when-i-is-not-an-integer))))

(defthm unsigned-byte-p-of-bvplus
  (implies (and (<= n m)
                (natp n)
                (integerp m))
           (unsigned-byte-p m (bvplus n x y)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvplus size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvplus))))

;drop?
(defthm bvchop-of-bvplus2
  (implies (and (<= size2 size1)
                (natp size1)
                (natp size2))
           (equal (bvchop size1 (bvplus size2 y z))
                  (bvplus size2 y z))))

(defthm bvplus-when-arg1-is-not-an-integer
  (implies (not (integerp x))
           (equal (bvplus size x y)
                  (bvchop size y)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-when-arg2-is-not-an-integer
  (implies (not (integerp y))
           (equal (bvplus size x y)
                  (bvchop size x)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-subst-value
  (implies (and (equal (bvchop n x) k) ;k comes second so that this is not a binding hyp
                (syntaxp (and (quotep k)
                              (not (quotep x)))))
           (equal (bvplus n y x)
                  (bvplus n k y)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-subst-value-alt
  (implies (and (equal (bvchop n x) k) ;k comes second so that this is not a binding hyp
                (syntaxp (and (quotep k)
                              (not (quotep x)))))
           (equal (bvplus n x y)
                  (bvplus n k y)))
  :hints (("Goal" :use (:instance bvplus-subst-value)
           :in-theory (disable bvplus-subst-value))))

(defthm bvplus-of-1-subst
  (implies (and (equal (getbit 0 x) k) ;k comes second so that this is not a binding hyp
                (syntaxp (and (quotep k)
                              (not (quotep x)))))
           (equal (bvplus 1 y x)
                  (bvplus 1 k y)))
  :hints (("Goal" :use (:instance bvplus-subst-value (n 1)))))

(defthm bvplus-of-1-subst-alt
  (implies (and (equal (getbit 0 x) k) ;k comes second so that this is not a binding hyp
                (syntaxp (and (quotep k)
                              (not (quotep x)))))
           (equal (bvplus 1 x y)
                  (bvplus 1 k y)))
  :hints (("Goal" :use (:instance bvplus-of-1-subst))))

(defthm bvchop-of-bvplus
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2)
                )
           (equal (bvchop size1 (bvplus size2 y z))
                  (bvplus size1 y z)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvchop-of-bvplus-same
  (equal (bvchop size (bvplus size y z))
         (bvplus size y z))
  :hints (("Goal" :in-theory (enable bvplus))))

;fixme improve BVCHOP-+-CANCEL-0

;rename?
(defthm bvplus-cancel
  (equal (equal (bvplus size x y) (bvplus size x z))
         (equal (bvchop size y) (bvchop size z)))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvplus))))

(defthm bvplus-cancel-third-third
  (implies (integerp a)
           (equal (equal (bvplus size k1 (bvplus size x a)) (bvplus size k2 (bvplus size y a)))
                  (equal (bvplus size k1 x) (bvplus size k2 y))))
  :hints (("Goal" :use (:instance bvplus-cancel (x a)
                                  (y (bvplus size k1 x))
                                  (z (bvplus size k2 y))))))

(defthm bvplus-cancel-cross
  (equal (equal (bvplus size y x)
                (bvplus size x z))
         (equal (bvchop size y)
                (bvchop size z))))

(defthm bvplus-cancel-cross2
  (equal (equal (bvplus size x y)
                (bvplus size z x))
         (equal (bvchop size y) (bvchop size z)))
  :hints (("Goal" :use (:instance bvplus-cancel-cross)
           :in-theory (disable bvplus-cancel-cross))))

(defthm equal-of-bvplus-and-bvplus-cancel-arg2-arg2
  (equal (equal (bvplus size y x) (bvplus size z x))
         (equal (bvchop size y) (bvchop size z))))

(defthm equal-of-bvplus-and-bvplus-cancel-arg2-all-helper
 (implies (and (posp size)
               (unsigned-byte-p size x))
          (equal (equal (bvplus size y x) x)
                 (equal (bvchop size y) 0)))
 :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases))))

;why "all"?
;lhs is out of order..
(defthm equal-of-bvplus-cancel-arg2
  (implies (posp size)
           (equal (equal (bvplus size y x) x)
                  (and (unsigned-byte-p size x)
                       (equal (bvchop size y) 0))))
  :hints (("Goal" :use (:instance equal-of-bvplus-and-bvplus-cancel-arg2-all-helper
                                  (x (bvchop size x)))
           :in-theory (disable equal-of-bvplus-and-bvplus-cancel-arg2-all-helper))))

(defthm equal-of-bvplus-cancel-arg2-alt
  (implies (posp size)
           (equal (equal x (bvplus size y x))
                  (and (unsigned-byte-p size x)
                       (equal (bvchop size y) 0))))
  :hints (("Goal" :use (:instance equal-of-bvplus-cancel-arg2)
           :in-theory (disable equal-of-bvplus-cancel-arg2))))

(defthm equal-of-bvplus-cancel-arg1
  (implies (posp size)
           (equal (equal x (bvplus size x y))
                  (and (unsigned-byte-p size x)
                       (equal (bvchop size y) 0))))
  :hints (("Goal" :use (:instance equal-of-bvplus-cancel-arg2)
           :in-theory (disable equal-of-bvplus-cancel-arg2))))

;fixme same as bvplus-cancel
(defthm equal-of-bvplus-and-bvplus-cancel-arg1-arg1
  (equal (equal (bvplus size x y) (bvplus size x z))
         (equal (bvchop size y) (bvchop size z)))
  :hints (("Goal" :use (:instance equal-of-bvplus-and-bvplus-cancel-arg2-arg2)
           :in-theory (disable equal-of-bvplus-and-bvplus-cancel-arg2-arg2))))

(defthm equal-of-bvplus-and-bvplus-cancel-arg2-and-arg3
  (implies (natp size)
           (equal (equal (bvplus size y x) (bvplus size z (bvplus size w x)))
                  (equal (bvchop size y) (bvplus size z w))))
  :hints (("Goal" :use (:instance equal-of-bvplus-and-bvplus-cancel-arg1-arg1
                                  (z (bvplus size z w)))
           :in-theory (disable equal-of-bvplus-and-bvplus-cancel-arg1-arg1 bvplus-cancel))))

(defthm equal-of-bvplus-and-bvplus-cancel-arg3-and-arg3
  (implies (natp size)
           (equal (equal (bvplus size v (bvplus size y x)) (bvplus size z (bvplus size w x)))
                  (equal (bvplus size v y) (bvplus size z w))))
  :hints (("Goal" :use (:instance equal-of-bvplus-and-bvplus-cancel-arg1-arg1
                                  (y (bvplus size v y))
                                  (z (bvplus size z w)))
           :in-theory (disable equal-of-bvplus-and-bvplus-cancel-arg1-arg1 bvplus-cancel))))

;other versions? alt and commuted!
(defthm equal-of-bvplus-and-bvplus-cancel-gen
  (implies (and (<= size size2)
                (integerp size2)
                (natp size))
           (equal (equal (bvplus size y x) (bvplus size2 k x))
                  (and (unsigned-byte-p size (bvplus size2 k x))
                       (equal (bvchop size y) (bvchop size k)))))
  :hints (("Goal" :use (:instance bvchop-identity  (i (bvplus size2 k x))))))

(defthm equal-of-bvplus-and-bvplus-cancel-gen-alt
  (implies (and (<= size size2)
                (integerp size2)
                (natp size))
           (equal (equal (bvplus size2 k x)
                         (bvplus size y x))
                  (and (unsigned-byte-p size (bvplus size2 k x))
                       (equal (bvchop size y)
                              (bvchop size k)))))
  :hints (("Goal" :use (:instance equal-of-bvplus-and-bvplus-cancel-gen)
           :in-theory (disable equal-of-bvplus-and-bvplus-cancel-gen))))

(defthm equal-of-bvplus-cancel-2-of-more-and-1-of-more
  (implies (natp size)
           (equal (equal (bvplus size y (bvplus size x z)) (bvplus size x w))
                  (equal (bvplus size y z) (bvchop size w)))))

(defthm equal-of-bvplus-cancel-3-of-more-and-1-of-more
  (implies (natp size)
           (equal (equal (bvplus size y (bvplus size zz (bvplus size x z))) (bvplus size x w))
                  (equal (bvplus size y (bvplus size zz z)) (bvchop size w)))))

;kill bvplus-subst-value and bvplus-subst-value-alt?
(defthm bvplus-when-equal-of-constant-and-bvchop-arg2
  (implies (and (equal (bvchop freesize x) freeval) ;freeval comes second so that this is not a binding hyp
                (syntaxp (and (quotep freeval) (not (quotep x)) (quotep size) (quotep freesize)))
                (<= size freesize)
                (natp size)
                (integerp freesize))
           (equal (bvplus size x y)
                  (bvplus size freeval y)))
  :hints (("Goal" :in-theory (e/d (bvplus)
                                  nil))))

(defthm bvplus-when-equal-of-constant-and-bvchop-arg3
  (implies (and (equal (bvchop freesize x) freeval) ;freeval comes second so that this is not a binding hyp
                (syntaxp (and (quotep freeval) (not (quotep x)) (quotep size) (quotep freesize)))
                (<= size freesize)
                (natp size)
                (integerp freesize))
           (equal (bvplus size y x)
                  (bvplus size y freeval)))
  :hints (("Goal" :use (:instance bvplus-when-equal-of-constant-and-bvchop-arg2)
           :in-theory (disable bvplus-when-equal-of-constant-and-bvchop-arg2))))

(defthmd bvplus-commute-constant
  (implies (syntaxp (and (quotep k)
                         (not (quotep x))))
           (equal (bvplus size x k)
                  (bvplus size k x))))

;gen
;rename
(defthm equal-of-+-and-bv
  (implies (and (integerp x1)
                (integerp x2)
                (natp n))
           (equal (equal (+ x1 x2) (bvplus n y z))
                  (if (< (+ x1 x2) 0)
                      nil
                    (if (<= (expt 2 n) (+ x1 x2))
                        nil
                      (equal (bvplus n x1 x2) (bvplus n y z))))))
  :hints (("Goal" :in-theory (enable bvplus))))

;; Rewrite bvplus to + when possible
(defthmd bvplus-becomes-+
  (implies (and (< (+ x y) (expt 2 n))
                (natp x)
                (natp y))
           (equal (bvplus n x y)
                  (+ x y)))
  :hints (("Goal" :in-theory (e/d (expt ;why?
                                   bvchop-identity)
                                  (expt-hack)))))

;; x plus 1 is greater than x unless the addition overflows or x is just wider than size.
;todo: gen the 1.
(defthm <-of-bvplus-of-1-overflow
  (implies (and (integerp x)
                (natp size))
           (equal (< x (bvplus size 1 x))
                  (< x (+ -1 (expt 2 size))))) ;size is usually a constant
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases unsigned-byte-p)
                                  (bvchop-identity
                                   bvchop-does-nothing-rewrite))
           :use (:instance bvchop-identity (i x)))))

;gen the 0
;generic rule for all bvops? what if the size isn't a constant?
(defthm bvplus-not-negative
  (not (< (bvplus size x y) 0)))
