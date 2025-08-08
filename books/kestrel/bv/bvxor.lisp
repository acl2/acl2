; BV Library: bvxor
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
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(local (include-book "slice"))
(local (include-book "logxor-b"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "unsigned-byte-p"))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

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
           :use (bvxor-associative
                 (:instance bvxor-associative (x y) (y x))))))

(defthmd bvxor-commute-constant
  (implies (syntaxp (and (quotep y)
                         (not (quotep x))))
           (equal (bvxor size x y)
                  (bvxor size y x))))

;; not needed if we are commuting more generally
(defthmd bvxor-commute-constant2
  (implies (syntaxp (and (quotep k)
                         (not (quotep x))))
           (equal (bvxor size x (bvxor size k y))
                  (bvxor size k (bvxor size x y)))))

(defthm bvxor-same
  (equal (bvxor size x x)
         0)
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-same-2
  (equal (bvxor size x (bvxor size x y))
         (bvchop size y))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvxor))))

;; A bvxor of size 0 is 0.
(defthm bvxor-of-0-arg1
  (equal (bvxor 0 x y)
         0)
  :hints (("Goal" :in-theory (enable bvxor))))

;; Do not remove: helps justify the correctness of some operations done by Axe.
(defthm bvxor-of-0-arg2
  (equal (bvxor size 0 y)
         (bvchop size y))
  :hints (("Goal" :in-theory (enable bvxor))))

;; Do not remove: helps justify the correctness of some operations done by Axe.
;; Disabled, since we'll always commute constants to the front.
(defthmd bvxor-of-0-arg3
  (equal (bvxor size x 0)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-combine-constants
  (implies (syntaxp (and (quotep y) ;tested first to fail fast
                         (quotep x)
                         (quotep size)))
           (equal (bvxor size x (bvxor size y z))
                  (bvxor size (bvxor size x y) z)))
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

;i guess this is how we should phrase all the bvchop-of-xxx rules?
;when n=size this will cause the bvxor to be rewritten again, unlike if we let bvchop-identity fire.  does that slow things down much?
(defthm bvchop-of-bvxor
  (implies (and (natp n)
                (natp size))
           (equal (bvchop n (bvxor size x y))
                  (bvxor (min n size) x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

;no hyps
(defthm bvchop-of-bvxor-same
  (equal (bvchop size (bvxor size x y))
         (bvxor size x y))
  :hints (("Goal" :cases ((integerp size)))))


(defthm unsigned-byte-p-of-bvxor-gen
  (implies (<= size size2)
           (equal (unsigned-byte-p size2 (bvxor size x y))
                  (natp size2)))
  :hints (("Goal" :in-theory (e/d (natp) (unsigned-byte-p-of-bvxor))
           :use (:instance unsigned-byte-p-of-bvxor (y y) (x x) (size size)))))

(defthm unsigned-byte-p-of-bvxor-alt
  (implies (and (unsigned-byte-p size x)
                (unsigned-byte-p size y))
           (unsigned-byte-p size (bvxor size2 x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

;; todo: rename these to have equal in the name:
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

;rename bvxor-of-bvchop-arg2
(defthm bvxor-of-bvchop-1
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvxor size (bvchop size2 x) y)
                  (bvxor size x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

;rename bvxor-of-bvchop-arg3
(defthm bvxor-of-bvchop-2
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvxor size x (bvchop size2 y))
                  (bvxor size x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-of-bvchop-same-arg1
  (equal (bvxor size (bvchop size x) y)
         (bvxor size x y))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-of-bvchop-same-arg2
  (equal (bvxor size x (bvchop size y))
         (bvxor size x y))
  :hints (("Goal" :in-theory (enable bvxor))))

;todo make a general lemma for all bvs, like we do for trimming?
(defthm getbit-of-bvxor-too-high
  (implies (<= size (nfix n))
           (equal (getbit n (bvxor size x y))
                  0))
  :hints (("Goal" :cases ((and (integerp n)(natp size))
                          (and (not (integerp n))(natp size)))
           :in-theory (enable getbit-too-high))))

;When n=0, size=1, and x or y is a huge bvxor nest of size 1 (common after bit-blasting), this would push the getbits through the huge nest.
(defthmd getbit-of-bvxor-core
  (implies (and (< n size)
                (posp size))
           (equal (getbit n (bvxor size x y))
                  (bvxor 1 (getbit n x) (getbit n y))))
  :hints (("Goal"
           :in-theory (enable getbit slice bvxor bvchop-of-logtail))))

;if the size is 1 this rebuilds the term (bvxor 1 x y) - may be a bit innefficient
(defthm getbit-0-of-bvxor
  (implies (posp size)
           (equal (getbit 0 (bvxor size x y))
                  (bvxor 1 x y)))
  :hints (("Goal" :in-theory (enable getbit-of-bvxor-core))))

;rename
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

;; Seems safe because the (getbit n x) in the conclusion gets computed (could further simplify the RHS).
(defthmd getbit-of-bvxor-when-quotep
  (implies (and (syntaxp (and (quotep x)
                              (quotep n)))
                (< n size)
                (posp size))
           (equal (getbit n (bvxor size x y))
                  (bvxor 1 (getbit n x) (getbit n y))))
  :hints (("Goal" :in-theory (enable getbit-of-bvxor-core))))

(defthm bvxor-numeric-bound
  (implies (<= (expt 2 size) k)
           (< (bvxor size x y) k))
  :hints (("Goal" :use unsigned-byte-p-of-bvxor
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
  :hints (("Goal" :use bvxor-cancel-lemma1
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
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-subst-arg3
  (implies (and (syntaxp (not (quotep y)))
                (equal (bvchop free y) k)
                (syntaxp (quotep k))
                (<= n free)
                (integerp free))
           (equal (bvxor n x y)
                  (bvxor n x k)))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm equal-of-0-and-bvxor
  (equal (equal 0 (bvxor size x y))
         (equal (bvchop size x) (bvchop size y)))
  :hints (("Goal" :use (:instance bvxor-cancel
                                  (y (bvchop size x))
                                  (z (bvchop size y))
                                  (x (bvchop size y)))
           :in-theory (e/d (bvxor-commutative) (bvxor-cancel)))))

(defthm bvxor-of-constant-chop-arg2
   (implies (and (syntaxp (and (quotep x)
                               (quotep size)))
                 (not (unsigned-byte-p size x))
                 (natp size) ; prevents loops
                 )
            (equal (bvxor size x y)
                   (bvxor size (bvchop size x) y)))
   :hints (("Goal" :in-theory (enable bvxor))))

;; may not be needed if we commute constants forward
(defthm bvxor-of-constant-chop-arg3
   (implies (and (syntaxp (and (quotep y)
                               (quotep size)))
                 (not (unsigned-byte-p size y))
                 (natp size) ; prevents loops
                 )
            (equal (bvxor size x y)
                   (bvxor size x (bvchop size y))))
   :hints (("Goal" :in-theory (enable bvxor))))

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

;todo: drop
(defthm bvxor-of-bvchop-tighten-2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp y)
                (integerp x))
           (equal (bvxor size1 x (bvchop size2 y))
                  (bvxor size1 x (bvchop size1 y))))
  :hints (("Goal" :in-theory (enable bvxor ;bvchop-bvchop
                                     ))))

;todo: drop
(defthm bvxor-of-bvchop-tighten-1
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp y)
                (integerp x))
           (equal (bvxor size1 (bvchop size2 y) x)
                  (bvxor size1 (bvchop size1 y) x)))
  :hints (("Goal" :in-theory (enable bvxor ;bvchop-bvchop
                                     ))))

(defthm bitp-of-bvxor-of-1
  (bitp (bvxor 1 x y))
  :rule-classes :type-prescription
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvxor (size 1))
           :in-theory (disable unsigned-byte-p-of-bvxor
                               unsigned-byte-p-of-bvxor-gen))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm slice-of-bvxor
  (implies (and (< high size)
                ;; (<= low high)
                (integerp size)
                (natp low)
                (natp high))
           (equal (slice high low (bvxor size x y))
                  (bvxor (+ 1 high (- low))
                         (slice high low x)
                         (slice high low y))))
  :hints (("Goal" :in-theory (enable slice bvxor natp bvchop-of-logtail))))

;bozo or just use SLICE-TOO-HIGH-IS-0 - which is cheaper?
;or just pass slice through?
(defthm slice-of-bvxor-too-high
  (implies (and (<= size low)
                (integerp low)
                (natp size))
           (equal (slice high low (bvxor size x y))
                  0))
  :hints (("Goal" :in-theory (enable slice-too-high-is-0))))

(defthm slice-of-bvxor-gen
  (implies (and (natp low)
                (integerp high)
                (natp size))
           (equal (slice high low (bvxor size x y))
                  (if (<= size low)
                      0
                    (if (< high size)
                        (bvxor (+ 1 high (- low))
                               (slice high low x)
                               (slice high low y))
                      (bvxor (+ size (- low))
                             (slice (+ -1 size) low x)
                             (slice (+ -1 size) low y))))))
  :hints (("Goal" :in-theory (enable slice bvxor natp bvchop-of-logtail))))

;here we tighten the slice
(defthm slice-of-bvxor-tighten2
  (implies (and (<= size high)
                (<= low size)
                (natp high)
                (natp low)
                (natp size))
           (equal (slice high low (bvxor size x y))
                  (slice (+ -1 size) low (bvxor size x y))))
  :hints (("Goal" :in-theory (e/d (slice) (slice-becomes-bvchop
                                           logtail-of-bvchop-becomes-slice)))))

;drop in favor of trim rules?
(defthm slice-of-bvxor-tighten
  (implies (and (< (+ 1 high) size)
;                (<= low high)
                (integerp size)
                (< 0 size)
                (natp low)
                (natp high))
           (equal (slice high low (bvxor size x y))
                  (slice high low (bvxor (+ 1 high) x y))))
  :hints (("Goal" :cases ((<= low high))
          :in-theory (e/d (slice bvxor natp  bvchop-of-logtail) (slice-becomes-bvchop)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvxor-cancel-2-of-more-and-1-of-more
  (equal (equal (bvxor size y (bvxor size x z)) (bvxor size x w))
         (equal (bvxor size y z) (bvchop size w))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;newly disabled
(defthmd logxor-bvchop-bvchop
  (implies (and (integerp x)
                (<= 0 size)
                (integerp size)
                (integerp y))
           (equal (LOGXOR (BVCHOP size x)
                          (BVCHOP size y))
                  (bvxor size x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

(theory-invariant (incompatible (:definition bvxor) (:rewrite logxor-bvchop-bvchop)))

(defthmd logxor-of-bvchop-and-bvchop
  (implies (and (integerp x)
                (integerp y)
                (natp size1)
                (natp size2))
           (equal (LOGXOR (BVCHOP size1 x)
                          (BVCHOP size2 y))
                  (if (<= size1 size2)
                      (bvxor size2 (bvchop size1 x) y)
                    (bvxor size1 x (bvchop size2 y)))))
  :hints (("Goal" :in-theory (enable bvxor))))

(theory-invariant (incompatible (:definition bvxor) (:rewrite logxor-of-bvchop-and-bvchop)))

(defthmd logxor-of-bvchop-becomes-bvxor-arg1
  (implies (and (unsigned-byte-p size y)
                (integerp x)
                (natp size))
           (equal (logxor (bvchop size x) y)
                  (bvxor size x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

(theory-invariant (incompatible (:definition bvxor) (:rewrite logxor-of-bvchop-becomes-bvxor-arg1)))

(defthmd logxor-of-bvchop-becomes-bvxor-arg2
  (implies (and (unsigned-byte-p size x)
                (integerp y)
                (natp size))
           (equal (logxor x (bvchop size y))
                  (bvxor size x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

(theory-invariant (incompatible (:definition bvxor) (:rewrite logxor-of-bvchop-becomes-bvxor-arg2)))

;rename
(defthm equal-of-bvxor-and-bvxor-same-7
  (equal (equal (bvxor size zw (bvxor size x z)) (bvxor size y (bvxor size x zu)))
         (equal (bvxor size zw z) (bvxor size y zu))))

;rename
(defthm equal-of-bvxor-and-bvxor-same-8
  (equal (equal (bvxor size zw x) (bvxor size y (bvxor size x zu)))
         (equal (bvchop size zw) (bvxor size y zu))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;We'd like BVNOT to be invisible when commuting BVXOR nests.  But BVNOT is not
;;unary, so I don't think ACL2's built-in notion of invisible-fns will work.
;;So we implement our own version here for BVXOR calls.

;TODO: Move to bv-syntax file?
;fixme should we check the size of the bvnot call?
(defun strip-off-bvnot-call (term)
  (declare (xargs :guard t))
  (if (and (consp term)
           (eq 'bvnot (car term))
           (consp (cdr term))
           (consp (cddr term)))
      (fargn term 2)
    term))

;ffixme don't mess up associativity - see should-commute-args and make a non-axe version?
(defund smaller-bvxor-arg (term1 term2)
; (declare (xargs :guard t)) ;todo add a guard
  (smaller-termp (strip-off-bvnot-call term1)
                 (strip-off-bvnot-call term2)))

(defthm bvxor-commutative-alt
  (implies (syntaxp (smaller-bvxor-arg b a))
           (equal (bvxor size a b)
                  (bvxor size b a)))
  :rule-classes ((:rewrite :loop-stopper nil ;((a b bvxor))
                           ))
  :hints (("Goal" :in-theory (enable bvxor))))

(in-theory (disable bvxor-commutative))
(theory-invariant (incompatible (:rewrite bvxor-commutative) (:rewrite bvxor-commutative-alt)))

(defthm bvxor-commutative-2-alt
  (implies (syntaxp (smaller-bvxor-arg a b))
           (equal (bvxor size b (bvxor size a c))
                  (bvxor size a (bvxor size b c))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable bvxor))))

(in-theory (disable bvxor-commutative-2))
(theory-invariant (incompatible (:rewrite bvxor-commutative-2) (:rewrite bvxor-commutative-2-alt)))
