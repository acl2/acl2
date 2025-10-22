; BV Library: bvplus
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvplus-def")
(include-book "getbit")
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(local (include-book "slice"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "unsigned-byte-p"))

(defthm bvplus-associative
  (equal (bvplus size (bvplus size x y) z)
         (bvplus size x (bvplus size y z)))
  :hints (("Goal" :in-theory (enable bvplus))))

;; may be less likely to disrupt huge bvplus nests
;; see also bvplus-commute-constant2
(defthm bvplus-associative-when-constant-arg1
  (implies (syntaxp (quotep x))
           (equal (bvplus size (bvplus size x y) z)
                  (bvplus size x (bvplus size y z))))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-commutative
  (equal (bvplus size x y)
         (bvplus size y x))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-commutative-2
  (equal (bvplus size y (bvplus size x z))
         (bvplus size x (bvplus size y z)))
  :hints (("Goal" :in-theory (disable bvplus-associative)
           :use ((:instance bvplus-associative)
                 (:instance bvplus-associative (x y) (y x))))))

;; not needed if we are commuting more generally
(defthmd bvplus-commute-constant
  (implies (syntaxp (and (quotep k)
                         (not (quotep x))))
           (equal (bvplus size x k)
                  (bvplus size k x))))

;; not needed if we are commuting more generally
(defthmd bvplus-commute-constant2
  (implies (syntaxp (and (quotep k)
                         (not (quotep x))))
           (equal (bvplus size x (bvplus size k y))
                  (bvplus size k (bvplus size x y)))))

;; The (bvplus size x y) in the conclusion gets computed.
(defthm bvplus-combine-constants
  (implies (syntaxp (and (quotep y) ;I put this one first to fail fast
                         (quotep x)
                         (quotep size)))
           (equal (bvplus size x (bvplus size y z))
                  (bvplus size (bvplus size x y) z))))

(defthm bvplus-of-0-arg2
  (equal (bvplus size 0 y)
         (bvchop size y))
  :hints (("Goal" :in-theory (enable bvplus))))

;; Disabled since usually commute constants forward
(defthmd bvplus-of-0-arg3
  (equal (bvplus size x 0)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvplus))))

; almost subsumed by bvplus-of-bvchop-arg2-gen
(defthm bvplus-of-bvchop-arg2
  (equal (bvplus size (bvchop size x) y)
         (bvplus size x y))
  :hints (("Goal" :in-theory (enable bvplus bvchop-when-i-is-not-an-integer))))

(defthm bvplus-of-bvchop-arg2-gen
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvplus size (bvchop size2 x) y)
                  (bvplus size x y)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-when-i-is-not-an-integer))))

; almost subsumed by bvplus-of-bvchop-arg3-gen
(defthm bvplus-of-bvchop-arg3
  (equal (bvplus size x (bvchop size y))
         (bvplus size x y))
  :hints (("Goal" :in-theory (enable bvplus bvchop-when-i-is-not-an-integer))))

(defthm bvplus-of-bvchop-arg3-gen
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvplus size x (bvchop size2 y))
                  (bvplus size x y)))
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

(defthm bvplus-when-not-natp-arg1-cheap
  (implies (not (natp size))
           (equal (bvplus size x y)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
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
  :hints (("Goal" :use bvplus-subst-value
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
  :hints (("Goal" :use bvplus-of-1-subst)))

;avoid re-consing (bvplus size1 y z) when the sizes are equal?
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

(defthm equal-of-bvplus-and-bvplus-cancel-arg1-arg1
  (equal (equal (bvplus size x y) (bvplus size x z))
         (equal (bvchop size y) (bvchop size z)))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvplus))))

;todo: rename vars
(defthm bvplus-cancel-arg3-arg3
  (equal (equal (bvplus size k1 (bvplus size x a)) (bvplus size k2 (bvplus size y a)))
         (equal (bvplus size k1 x) (bvplus size k2 y)))
  :hints (("Goal" :use (:instance equal-of-bvplus-and-bvplus-cancel-arg1-arg1
                                  (x a)
                                  (y (bvplus size k1 x))
                                  (z (bvplus size k2 y))))))

(defthm equal-of-bvplus-and-bvplus-cancel-arg2-arg1
  (equal (equal (bvplus size y x) (bvplus size x z))
         (equal (bvchop size y)
                (bvchop size z))))

(defthm equal-of-bvplus-and-bvplus-cancel-arg1-arg2
  (equal (equal (bvplus size x y) (bvplus size z x))
         (equal (bvchop size y) (bvchop size z)))
  :hints (("Goal" :use equal-of-bvplus-and-bvplus-cancel-arg2-arg1
           :in-theory (disable equal-of-bvplus-and-bvplus-cancel-arg2-arg1))))

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
  :hints (("Goal" :use equal-of-bvplus-cancel-arg2
           :in-theory (disable equal-of-bvplus-cancel-arg2))))

(defthm equal-of-bvplus-cancel-arg1
  (implies (posp size)
           (equal (equal x (bvplus size x y))
                  (and (unsigned-byte-p size x)
                       (equal (bvchop size y) 0))))
  :hints (("Goal" :use equal-of-bvplus-cancel-arg2
           :in-theory (disable equal-of-bvplus-cancel-arg2))))

(defthm equal-of-bvplus-and-bvplus-cancel-arg2-and-arg3
  (implies (natp size)
           (equal (equal (bvplus size y x) (bvplus size z (bvplus size w x)))
                  (equal (bvchop size y) (bvplus size z w))))
  :hints (("Goal" :use (:instance equal-of-bvplus-and-bvplus-cancel-arg1-arg1
                                  (z (bvplus size z w)))
           :in-theory (disable equal-of-bvplus-and-bvplus-cancel-arg1-arg1))))

(defthm equal-of-bvplus-and-bvplus-cancel-arg3-and-arg3
  (implies (natp size)
           (equal (equal (bvplus size v (bvplus size y x)) (bvplus size z (bvplus size w x)))
                  (equal (bvplus size v y) (bvplus size z w))))
  :hints (("Goal" :use (:instance equal-of-bvplus-and-bvplus-cancel-arg1-arg1
                                  (y (bvplus size v y))
                                  (z (bvplus size z w)))
           :in-theory (disable equal-of-bvplus-and-bvplus-cancel-arg1-arg1))))

;other versions? alt and commuted!
(defthm equal-of-bvplus-and-bvplus-cancel-gen
  (implies (and (<= size size2)
                (integerp size2)
                (natp size))
           (equal (equal (bvplus size y x) (bvplus size2 k x))
                  (and (unsigned-byte-p size (bvplus size2 k x))
                       (equal (bvchop size y) (bvchop size k)))))
  :hints (("Goal" :use (:instance bvchop-identity (i (bvplus size2 k x))))))

(defthm equal-of-bvplus-and-bvplus-cancel-gen-alt
  (implies (and (<= size size2)
                (integerp size2)
                (natp size))
           (equal (equal (bvplus size2 k x)
                         (bvplus size y x))
                  (and (unsigned-byte-p size (bvplus size2 k x))
                       (equal (bvchop size y)
                              (bvchop size k)))))
  :hints (("Goal" :use equal-of-bvplus-and-bvplus-cancel-gen
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
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-when-equal-of-constant-and-bvchop-arg3
  (implies (and (equal (bvchop freesize x) freeval) ;freeval comes second so that this is not a binding hyp
                (syntaxp (and (quotep freeval) (not (quotep x)) (quotep size) (quotep freesize)))
                (<= size freesize)
                (natp size)
                (integerp freesize))
           (equal (bvplus size y x)
                  (bvplus size y freeval)))
  :hints (("Goal" :use bvplus-when-equal-of-constant-and-bvchop-arg2
           :in-theory (disable bvplus-when-equal-of-constant-and-bvchop-arg2))))



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
  (implies (and (< (+ x y) (expt 2 size))
                (natp x)
                (natp y))
           (equal (bvplus size x y)
                  (+ x y)))
  :hints (("Goal" :in-theory (e/d (expt ;why?
                                   bvchop-identity)
                                  (expt-hack)))))

;; Similar to the above
;rename
;here we drop the bvchop (and thus avoid conflicts with the anti-bvplus rules)
(defthmd bvplus-opener
  (implies (and (unsigned-byte-p size (+ x y))
                (natp size)
                (integerp x)
                (integerp y))
           (equal (bvplus size x y)
                  (+ x y)))
  :hints (("Goal" :in-theory (e/d (bvplus) (;
                                            )))))

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

(defthmd bvplus-of-+-arg3
  (implies (and (integerp y)
                (integerp z))
           (equal (bvplus size x (+ y z))
                  (bvplus size x (bvplus size y z))))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthmd bvplus-of-+-arg2
  (implies (and (integerp y)
                (integerp z))
           (equal (bvplus size (+ y z) x)
                  (bvplus size (bvplus size y z) x)))
  :hints (("Goal" :use bvplus-of-+-arg3)))

(theory-invariant (incompatible (:rewrite bvplus-of-+-arg3) (:definition bvplus)))
(theory-invariant (incompatible (:rewrite bvplus-of-+-arg2) (:definition bvplus)))

(defthm bvplus-trim-leading-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (unsigned-byte-p size k))
                (natp size) ; prevents loops
                )
           (equal (bvplus size k x)
                  (bvplus size (bvchop size k) x)))
  :hints (("Goal" :in-theory (enable bvplus)
           :cases ((natp size)))))




;todo: instead, introduce bvminus
;todo: rename
(defthm bvplus-minus-cancel
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (natp size)
                )
           (equal (bvplus size y (bvplus size (- y) x))
                  (bvchop size x)))
    :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-of-expt-same-arg2
  (implies (natp size)
           (equal (bvplus size x (expt 2 size))
                  (bvchop size x)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-subst-smaller-term-arg2
  (implies (and (equal (bvchop n y) (bvchop n free))
                (syntaxp (smaller-termp free y)))
           (equal (bvplus n x y)
                  (bvplus n x free)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-subst-smaller-term-arg1
  (implies (and (equal (bvchop n x) (bvchop n free))
                (syntaxp (smaller-termp free x)))
           (equal (bvplus n x y)
                  (bvplus n free y)))
  :hints (("Goal" :use (:instance bvplus-subst-smaller-term-arg2
                                  (x y)
                                  (y x))
           :in-theory (disable bvplus-subst-smaller-term-arg2))))

(defthmd bvchop-of-+-becomes-bvplus
  (implies (and (integerp x) ;these are new, since bvplus ifixes its args
                (integerp y))
           (equal (bvchop size (+ x y))
                  (bvplus size x y)))
  :hints (("Goal" :in-theory (enable bvplus))))

(theory-invariant (incompatible (:rewrite bvchop-of-+-becomes-bvplus) (:definition bvplus)))

(defthmd slice-of-+-becomes-slice-of-bvplus
  (implies (and (natp high)
                (natp low) ;drop?
                (integerp x)
                (integerp y))
           (equal (slice high low (+ x y))
                  (slice high low (bvplus (+ 1 high) x y))))
  :hints (("Goal" :in-theory (enable bvplus))))

(theory-invariant (incompatible (:rewrite slice-of-+-becomes-slice-of-bvplus) (:definition bvplus)))

(defthmd getbit-of-+-becomes-getbit-of-bvplus
  (implies (and (natp n)
                (integerp x)
                (integerp y))
           (equal (getbit n (+ x y))
                  (getbit n (bvplus (+ 1 n) x y))))
  :hints (("Goal" :in-theory (enable bvplus))))

(theory-invariant (incompatible (:rewrite getbit-of-+-becomes-getbit-of-bvplus) (:definition bvplus)))

;mixes abstractions
(defthm bvplus-of-expt-2
  (equal (bvplus size x (expt 2 size))
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvplus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm equal-of-bvchop-and-bvplus-cancel-1
  (equal (equal (bvchop size x) (bvplus size x y))
         (equal 0 (bvchop size y)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases))))

(defthm equal-of-bvplus-and-bvchop-cancel-1
  (equal (equal (bvplus size x y) (bvchop size x))
         (equal 0 (bvchop size y)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases))))

(defthm equal-of-bvchop-and-bvplus-same-arg2
  (implies (natp size)
           (equal (equal (bvchop size x) (bvplus size y x))
                  (equal (bvchop size y) 0)))
  :hints (("Goal"
           :in-theory (enable bvplus bvchop-of-sum-cases))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvplus-of-bvplus-tighten-arg2
  (implies (and (< size size2)
                (natp size)
                (integerp size2))
           (equal (bvplus size (bvplus size2 x y) z)
                  (bvplus size (bvplus size x y) z)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-of-bvplus-tighten-arg3
  (implies (and (< size size2)
                (natp size)
                (integerp size2))
           (equal (bvplus size x (bvplus size2 y z))
                  (bvplus size x (bvplus size y z))))
  :hints (("Goal" :in-theory (enable bvplus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvplus-of-ifix-arg2
  (equal (bvplus size (ifix x) y)
         (bvplus size x y))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-of-ifix-arg3
  (equal (bvplus size x (ifix y))
         (bvplus size x y))
  :hints (("Goal" :in-theory (enable bvplus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: or go to bvplus of bvplus
(defthm bvplus-of-+-combine-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (integerp x)
                (integerp k1)
                (integerp k2))
           (equal (bvplus size k1 (+ k2 x))
                  (bvplus size (+ k1 k2) x)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-equal-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (integerp k1)
                (integerp k2)
                (natp size))
           (equal (equal (bvplus size k2 x) k1)
                  (and (unsigned-byte-p size k1)
                       (equal (bvchop size x) (bvchop size (- k1 k2))))))
  :hints (("Goal" :in-theory (enable bvplus BVCHOP-OF-SUM-CASES UNSIGNED-BYTE-P))))
