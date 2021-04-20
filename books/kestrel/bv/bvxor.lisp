; BV Library: bvxor
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "logxor-b")
(include-book "bvchop")
(include-book "getbit")
(local (include-book "../utilities/equal-of-booleans"))
(local (include-book "unsigned-byte-p"))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(defund bvxor (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (logxor (bvchop size x)
          (bvchop size y)))

(defthm bvxor-type
  (and (integerp (bvxor size x y))
       (<= 0 (bvxor size x y)))
  :rule-classes :type-prescription)

(in-theory (disable (:type-prescription bvxor))) ; bvxor-type is at least as good

;rename params in this and other rules
(defthm bvxor-associative
  (equal (bvxor size (bvxor size x y) z)
         (bvxor size x (bvxor size y z)))
  :hints (("Goal" :in-theory (enable bvxor natp))))

(defthm bvxor-commutative
  (equal (bvxor size x y)
         (bvxor size y x))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-commutative-2
  (equal (bvxor size x (bvxor size y z))
         (bvxor size y (bvxor size x z)))
  :hints (("Goal" :in-theory (e/d (bvxor-commutative) (bvxor-associative))
           :use ((:instance bvxor-associative)
                 (:instance bvxor-associative (x y) (y x))))))

(defthm bvxor-same
  (equal (bvxor size x x)
         0)
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-same-2
  (equal (bvxor size x (bvxor size x y))
         (bvchop size y))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvxor))))

(defthm bvxor-of-0-arg1
  (equal (bvxor 0 x y)
         0)
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-of-0-arg2
  (equal (bvxor size 0 y)
         (bvchop size y))
  :hints (("Goal" :in-theory (enable bvxor))))

;in case we don't have commutativity - drop, since we'll always commute constants to the front?
(defthm bvxor-of-0-arg3
  (equal (bvxor size x 0)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-combine-constants
  (implies (syntaxp (and (quotep y) ;put this hyp first to fail fast
                         (quotep x)
                         (quotep size)))
           (equal (bvxor size x (bvxor size y z))
                  (bvxor size (bvxor size x y) z)))
  :hints (("Goal" :in-theory (enable bvxor))))

;i guess this is how we should phrase all the bvchop-of-xxx rules?
;when n=size this will cause the bvxor to be rewritten again, unlike if we let bvchop-identity fire.  does that slow things down much?
(defthm bvchop-of-bvxor
  (implies (and (natp n)
                (natp size))
           (equal (bvchop n (bvxor size x y))
                  (bvxor (min n size) x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

;todo more like this for other ops
(defthm bvxor-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvxor size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-when-size-is-not-an-integer
  (implies (not (integerp size))
           (equal (bvxor size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvxor))))

;backchain-limit?
(defthm bvxor-when-x-is-not-an-integer
  (implies (not (integerp x))
           (equal (bvxor size x y)
                  (bvchop size y)))
  :hints (("Goal" :in-theory (enable bvxor))))

;backchain-limit?
(defthm bvxor-when-y-is-not-an-integer
  (implies (not (integerp y))
           (equal (bvxor size x y)
                  (bvchop size x)))
  :hints (("Goal" :in-theory (enable bvxor))))

;drop? or keep since it's a simple rule
(defthm unsigned-byte-p-of-bvxor
  (equal (unsigned-byte-p size (bvxor size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm unsigned-byte-p-of-bvxor-gen
  (implies (<= size size2)
           (equal (unsigned-byte-p size2 (bvxor size x y))
                  (natp size2)))
  :hints (("Goal" :in-theory (e/d (natp) (unsigned-byte-p-of-bvxor))
           :use (:instance unsigned-byte-p-of-bvxor (y y) (x x) (size size)))))

(defthm bvxor-cancel
  (equal (equal (bvxor size x y) (bvxor size x z))
         (equal (bvchop size y) (bvchop size z)))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-cancel-alt
  (equal (equal (bvxor size y x) (bvxor size z x))
         (equal (bvchop size y) (bvchop size z)))
  :hints (("Goal" :in-theory (enable bvxor-commutative))))

(defthm bvxor-cancel-cross-1
  (equal (equal (bvxor size x y) (bvxor size z x))
         (equal (bvchop size y) (bvchop size z)))
  :hints (("Goal" :in-theory (enable bvxor-commutative))))

(defthm bvxor-cancel-cross-2
  (equal (equal (bvxor size y x) (bvxor size x z))
         (equal (bvchop size y) (bvchop size z)))
  :hints (("Goal" :in-theory (enable bvxor-commutative))))

;gen the 1?
(defthm bvxor-1-of-getbit-arg2
  (equal (bvxor 1 x (getbit 0 y))
         (bvxor 1 x y))
  :hints (("Goal" :in-theory (enable bvxor))))

;gen the 1?
(defthm bvxor-1-of-getbit-arg1
  (equal (bvxor 1 (getbit 0 x) y)
         (bvxor 1 x y))
  :hints (("Goal" :use (:instance bvxor-1-of-getbit-arg2 (y x) (x y)))))

(defthm bvxor-of-bvchop-1
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvxor size (bvchop size2 x) y)
                  (bvxor size x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-of-bvchop-2
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvxor size x (bvchop size2 y))
                  (bvxor size x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

;todo make a general lemma for all bvs, like we do for trimming?
(defthm getbit-of-bvxor-too-high
  (implies (<= size (nfix n))
           (equal (getbit n (bvxor size x y))
                  0))
  :hints (("Goal" :cases ((and (integerp n)(natp size))
                          (and (not (integerp n))(natp size))
                          )

           :in-theory (enable getbit-too-high))))

;When n=0, size=1, and x or y a huge bvxornest of size 1 (common after bit-blasting), this would push the getbits through the huge next.
(defthmd getbit-of-bvxor-core
  (implies (and (< n size)
                (posp size))
           (equal (getbit n (bvxor size x y))
                  (bvxor 1 (getbit n x) (getbit n y))))
  :hints (("Goal"
           :in-theory (e/d (getbit slice bvxor
                                   bvchop-of-logtail)
                           (slice-becomes-getbit
                            bvchop-1-becomes-getbit
                            bvchop-of-logtail-becomes-slice)))))

;if the size is 1 this rebuilds the term (bvxor 1 x y) - maybe be a bit innefficient
(defthm getbit-0-of-bvxor
  (implies (posp size)
           (equal (getbit 0 (bvxor size x y))
                  (bvxor 1 x y)))
  :hints (("Goal" :in-theory (enable getbit-of-bvxor-core))))

(defthm getbit-of-bvxor-eric
  (implies (and (< 0 n) ;prevents the n=0,size=1 case
                (< n size)
                (integerp size))
           (equal (getbit n (bvxor size x y))
                  (bvxor 1 (getbit n x) (getbit n y))))
    :hints (("Goal" :in-theory (enable getbit-of-bvxor-core))))

;todo move to using just this rule?
(defthm getbit-of-bvxor
  (implies (and (< n size)
                (posp size))
           (equal (getbit n (bvxor size x y))
                  (if (equal 0 n)
                      (bvxor 1 x y) ;better to not push the getbits inside in this case (could just go to bitxor)
                    (bvxor 1 (getbit n x) (getbit n y)))))
  :hints (("Goal" :in-theory (enable getbit-of-bvxor-core))))

(defthm bvxor-numeric-bound
  (implies (<= (expt 2 size) k)
           (< (bvxor size x y) k))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvxor)
           :in-theory (disable unsigned-byte-p-of-bvxor unsigned-byte-p-of-bvxor-gen))))

(defthm bvxor-cancel-lemma1
  (implies (posp size)
           (equal (equal x (bvxor size x y))
                  (and (unsigned-byte-p size x)
                       (equal (bvchop size y) 0))))
  :hints (("Goal" :use (:instance bvxor-cancel (x x) (z 0) (y y))
           :in-theory (disable bvxor-cancel))))

(defthm bvxor-cancel-lemma1-alt
  (implies (and (natp size)
                (< 0 size))
           (equal (equal x (bvxor size y x))
                  (and (unsigned-byte-p size x)
                       (equal (bvchop size y) 0))))
  :hints (("Goal" :use (:instance bvxor-cancel-lemma1)
           :in-theory (e/d (bvxor-commutative)
                           (bvxor-cancel-cross-2 bvxor-cancel-cross-1 bvxor-cancel-lemma1)))))

(defthm bvxor-cancel-lemma1-bvchop-version
  (implies (and (natp size)
                (< 0 size))
           (equal (equal (bvchop size x) (bvxor size x y))
                  (equal (bvchop size y) 0)))
  :hints (("Goal" :use (:instance bvxor-cancel (x (bvchop size x)) (z 0) (y y))
           :in-theory (disable bvxor-cancel))))

(defthm bvxor-cancel-lemma1-bvchop-version-alt
  (implies (and (natp size)
                (< 0 size))
           (equal (equal (bvchop size x) (bvxor size y x))
                  (equal (bvchop size y) 0)))
  :hints (("Goal" :use (:instance bvxor-cancel (x (bvchop size x)) (z 0) (y y))
           :in-theory (disable bvxor-cancel bvxor-cancel-lemma1-bvchop-version))))

(defthm bvxor-cancel-lemma1-bvchop-version-alt2
  (implies (and (natp size)
                (< 0 size))
           (equal (equal (bvxor size y x) (bvchop size x))
                  (equal (bvchop size y) 0)))
  :hints (("Goal" :use (:instance bvxor-cancel (x (bvchop size x)) (z 0) (y y))
           :in-theory (disable bvxor-cancel bvxor-cancel-lemma1-bvchop-version
                               bvxor-cancel-lemma1-bvchop-version-alt))))

(defthm bvxor-cancel-lemma1-bvchop-version-alt3
  (implies (and (natp size)
                (< 0 size))
           (equal (equal (bvxor size x y) (bvchop size x))
                  (equal (bvchop size y) 0)))
  :hints (("Goal" :use (:instance bvxor-cancel (x (bvchop size x)) (z 0) (y y))
           :in-theory (disable bvxor-cancel bvxor-cancel-lemma1-bvchop-version
                               bvxor-cancel-lemma1-bvchop-version-alt2))))

(defthmd bvxor-both-sides
  (implies (equal x y)
           (equal (bvxor size x z)
                  (bvxor size y z))))

(defthm equal-of-constant-and-bvxor-of-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (natp size))
           (equal (equal k1 (bvxor size k2 x))
                  (and (unsigned-byte-p size k1)
                       (equal (bvxor size k1 k2) (bvchop size x)))))
  :hints (("Goal"
           :use (:instance bvxor-both-sides (x (bvxor size K1 K2))
                           (y (bvchop size X))
                           (z k2))
           :in-theory (enable bvxor-commutative))))

(defthm bvxor-of-bvchop-same-arg1
  (equal (bvxor size (bvchop size x) y)
         (bvxor size x y))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-of-bvchop-same-arg2
  (equal (bvxor size x (bvchop size y))
         (bvxor size x y))
  :hints (("Goal" :in-theory (enable bvxor))))

;no hyps
(defthm bvchop-of-bvxor-same
  (equal (bvchop size (bvxor size x y))
         (bvxor size x y))
  :hints (("Goal" :cases ((integerp size)))))

;todo: add more
(defthm equal-of-bvxor-and-bvxor-arg1-arg2
  (equal (equal (bvxor size x y) (bvxor size w (bvxor size x z)))
         (equal (bvchop size y) (bvxor size w z)))
  :hints (("Goal" :use (:instance bvxor-cancel (z (bvxor size w z)))
           :in-theory (e/d (bvxor-commutative-2) (bvxor-cancel)))))

;make versions of these for other ops..
(defthm bvxor-subst-arg2
  (implies (and (syntaxp (not (quotep x)))
                (equal (bvchop free x) k)
                (syntaxp (quotep k))
                (<= n free)
                (integerp free))
           (equal (bvxor n x y)
                  (bvxor n k y)))
  :hints (("Goal" :in-theory (e/d (bvxor) nil))))

(defthm bvxor-subst-arg3
  (implies (and (syntaxp (not (quotep y)))
                (equal (bvchop free y) k)
                (syntaxp (quotep k))
                (<= n free)
                (integerp free))
           (equal (bvxor n x y)
                  (bvxor n x k)))
  :hints (("Goal" :in-theory (e/d (bvxor) nil))))

(defthm equal-of-0-and-bvxor
  (equal (equal 0 (bvxor size x y))
         (equal (bvchop size x) (bvchop size y)))
  :hints (("Goal" :use (:instance bvxor-cancel
                                  (y (bvchop size x))
                                  (z (bvchop size y))
                                  (x (bvchop size y)))
           :in-theory (e/d (bvxor-commutative) (bvxor-cancel)))))

(defthm bvxor-of-constant-trim-arg1
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (unsigned-byte-p size k))
                (integerp size))
           (equal (bvxor size k x)
                  (bvxor size (bvchop size k) x))))

(defthm bvxor-of-+-of-expt-2-same-arg2
  (implies (and (integerp x)
                (natp n))
           (equal (bvxor n (+ (expt 2 n) x) y)
                  (bvxor n x y))))

(defthm bvxor-of-+-of-expt-2-same-arg3
  (implies (and (integerp x)
                (natp n))
           (equal (bvxor n y (+ (expt 2 n) x))
                  (bvxor n y x))))

(defthm bvxor-of-+-of-times-of-expt-same-arg3-arg2-arg1
  (implies (and ;(integerp x)
                (integerp y)
                (integerp z)
                (posp n))
           (equal (bvxor n x (+ y (* (expt 2 n) z)))
                  (bvxor n x y))))

(defthm bvxor-of-+-of-times-of-expt-same-arg3-arg2-arg2
  (implies (and ;(integerp x)
                (integerp y)
                (integerp z)
                (posp n))
           (equal (bvxor n x (+ y (* z (expt 2 n))))
                  (bvxor n x y))))

(defthm bvxor-of-+-of-times-of-expt-same-arg3-arg2-arg1-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 n))
                (integerp x)
                (integerp y)
                (integerp z)
                (posp n))
           (equal (bvxor n x (+ y (* k z)))
                  (bvxor n x y))))
