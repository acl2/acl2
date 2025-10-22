; BV Library: bitxor
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvxor")
(local (include-book "slice"))
(local (include-book "logxor-b"))

(defund bitxor (x y)
  (declare (type integer x)
           (type integer y)
           (xargs :type-prescription (bitp (bitxor x y))))
  (bvxor 1 x y))

;; This version requires bitp inputs and so may be faster and may also help
;; catch bugs via stricter guard obligations.  We intened to keep this enabled
;; for reasoning.
(defun bitxor$ (x y)
  (declare (xargs :guard (and (bitp x) (bitp y))
                  :split-types t
                  :type-prescription (bitp (bitxor$ x y)))
           (type bit x y))
  (mbe :logic (bitxor x y)
       :exec (the bit (logxor x y))))

(defthm bitp-of-bitxor
  (bitp (bitxor x y)))

(defthm bitxor-associative
  (equal (bitxor (bitxor x y) z)
         (bitxor x (bitxor y z)))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthmd bitxor-commutative
  (equal (bitxor x y)
         (bitxor y x))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthmd bitxor-commutative-2
  (equal (bitxor x (bitxor y z))
         (bitxor y (bitxor x z)))
  :hints (("Goal" :use (:instance bvxor-commutative-2 (y x) (x y) (z z))
           :in-theory (enable bitxor))))

;more rules like this?
;more general rule to commute (if both are nodenums, pull the smaller one in?)
(defthmd bitxor-commute-constant
  (implies (syntaxp (quotep y))
           (equal (bitxor x y)
                  (bitxor y x)))
  :hints (("Goal" :use bitxor-commutative
           :in-theory (disable bitxor-commutative))))

(defthmd bitxor-combine-constants
  (implies (syntaxp (and (quotep y) ;put this hyp first to fail faster
                         (quotep x)))
           (equal (bitxor x (bitxor y z))
                  (bitxor (bitxor x y) z))))

(defthm bitxor-same
  (equal (bitxor x x)
         0)
  :hints (("Goal" :in-theory (enable bitxor))))

(defthm bitxor-same-2
  (equal (bitxor x (bitxor x y))
         (getbit 0 y))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthm bitxor-of-0-arg1
  (equal (bitxor 0 x)
         (getbit 0 x))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthm bitxor-of-0-arg2
  (equal (bitxor x 0)
         (getbit 0 x))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthm bitxor-of-constant-chop-arg1
  (implies (and (syntaxp (quotep x))
                (not (unsigned-byte-p 1 x)))
           (equal (bitxor x y)
                  (bitxor (getbit 0 x) y)))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthm bitxor-of-constant-chop-arg2
  (implies (and (syntaxp (quotep y))
                (not (unsigned-byte-p 1 y)))
           (equal (bitxor x y)
                  (bitxor x (getbit 0 y))))
  :hints (("Goal" :in-theory (enable bitxor))))

;justifies the correctness of some operations performed by Axe
(defthmd unsigned-byte-p-1-of-bitxor
  (unsigned-byte-p 1 (bitxor x y))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthm unsigned-byte-p-of-bitxor
  (implies (posp size)
           (unsigned-byte-p size (bitxor x y)))
  :hints (("Goal" :in-theory (enable bitxor))))

;todo: rename to have 0 in the name
(defthm bitxor-of-getbit-arg2
  (equal (bitxor y (getbit 0 x))
         (bitxor y x))
  :hints (("Goal" :in-theory (enable bitxor))))

;todo: rename to have 0 in the name
(defthm bitxor-of-getbit-arg1
  (equal (bitxor (getbit 0 x) y)
         (bitxor x y))
  :hints (("Goal" :in-theory (enable bitxor-commutative))))

(defthm bitxor-when-x-is-not-an-integer
  (implies (not (integerp x))
           (equal (bitxor x y)
                  (getbit 0 y)))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthm bitxor-when-y-is-not-an-integer
  (implies (not (integerp y))
           (equal (bitxor x y)
                  (getbit 0 x)))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthmd bitxor-split
  (equal (bitxor x y)
         (if (equal 1 (getbit 0 y))
             (if (equal 1 (getbit 0 x))
                 0
               1)
           (if (equal 1 (getbit 0 x))
                 1
             0)))
  :hints (("Goal" :in-theory (enable bitxor bvxor getbit))))

(defthm getbit-of-bitxor-all-cases
  (implies (natp n)
           (equal (getbit n (bitxor x y))
                  (if (equal n 0)
                      (bitxor x y)
                    0)))
  :hints (("Goal" :in-theory (enable bitxor))))

;leave this last
(defthm bvxor-1-becomes-bitxor
  (equal (bvxor 1 x y)
         (bitxor x y))
  :hints (("Goal" :in-theory (enable bitxor))))

;had (:rewrite bitxor) here, which isn't even a rule...
(theory-invariant (incompatible (:definition bitxor) (:rewrite bvxor-1-becomes-bitxor)))

(defthm bitxor-subst-arg1
  (implies (and (equal (getbit 0 x) free)
                (syntaxp (and (quotep free)
                              (not (quotep x)))))
           (equal (bitxor x y)
                  (bitxor free y))))

(defthm bitxor-subst-arg2
  (implies (and (equal (getbit 0 x) free)
                (syntaxp (and (quotep free)
                              (not (quotep x)))))
           (equal (bitxor y x)
                  (bitxor y free))))

(defthm bitxor-numeric-bound-2
  (implies (<= 2 k)
           (equal (< (bitxor x y) k)
                  t)))

(defthmd bitxor-both-sides
  (implies (equal x y)
           (equal (bitxor x z)
                  (bitxor y z))))

(defthm equal-of-constant-and-bitxor-of-constant
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)))
           (equal (equal k1 (bitxor k2 x))
                  (and (unsigned-byte-p 1 k1)
                       (equal (bitxor k1 k2) (getbit 0 x)))))
  :hints (("Goal"
           :use (:instance bitxor-both-sides (x (bitxor k1 k2))
                           (y (getbit 0 x))
                           (z k2))
           :in-theory (enable bitxor-commutative))))

;more like this!
(defthm equal-of-bitxor-and-bitxor-same
  (equal (equal (bitxor x y) (bitxor x z))
         (equal (getbit 0 y) (getbit 0 z)))
  :hints (("Goal" :in-theory (e/d (bitxor getbit) (bvxor-1-becomes-bitxor)))))

(defthm equal-of-bitxor-and-bitxor-same-alt
  (equal (equal (bitxor x1 y) (bitxor x2 y))
         (equal (getbit 0 x1) (getbit 0 x2)))
  :hints (("Goal" :in-theory (e/d (bitxor getbit) (bvxor-1-becomes-bitxor)))))

(defthm bitxor-of-ifix-arg1
  (equal (bitxor (ifix x) y)
         (bitxor x y))
  :hints (("Goal" :in-theory (enable getbit-when-val-is-not-an-integer))))

(defthm bitxor-of-ifix-arg2
  (equal (bitxor x (ifix y))
         (bitxor x y))
  :hints (("Goal" :in-theory (enable getbit-when-val-is-not-an-integer))))

(defthm bitxor-of-*-of-2 ;todo: gen the 2
  (implies (integerp bit2)
           (equal (bitxor bit1 (* 2 bit2))
                  (bitxor bit1 0)))
  :hints (("Goal" :in-theory (e/d (bitxor bvxor getbit)
                                  (bvxor-1-becomes-bitxor )))))

(defthm equal-of-0-and-bitxor
  (equal (equal 0 (bitxor x y))
         (equal (getbit 0 x)
                (getbit 0 y)))
  :hints (("Goal"
           :cases ((equal 0 (getbit 0 x))
                   (equal 1 (getbit 0 x))))))

(defthm equal-of-bitxor-same
  (equal (equal x (bitxor x y))
         (and (unsigned-byte-p 1 x)
              (equal 0 (getbit 0 y))))
  :hints (("Goal" :cases ((equal 0 (getbit 0 x))))))

(defthm equal-of-bitxor-same-alt
  (equal (equal x (bitxor y x))
         (and (unsigned-byte-p 1 x)
              (equal 0 (getbit 0 y))))
  :hints (("Goal" :use equal-of-bitxor-same
           :in-theory (e/d (bitxor-commutative) (equal-of-bitxor-same)))))

(defthm equal-of-bitxor-and-bitxor-same-2
  (equal (equal (bitxor x w) (bitxor y (bitxor x z)))
         (equal (getbit 0 w) (bitxor y z)))
  :hints (("Goal" :in-theory (e/d (bitxor)
                                  (bvxor-1-becomes-bitxor)))))

(defthm equal-of-bitxor-and-bitxor-same-3
  (equal (equal (bitxor w (bitxor x z)) (bitxor x y))
         (equal (bitxor w z) (getbit 0 y)))
  :hints (("Goal" :in-theory (e/d (bitxor)
                                  (bvxor-1-becomes-bitxor)))))

(defthm equal-of-bitxor-and-bitxor-same-4
  (equal (equal (bitxor y x) (bitxor x z))
         (equal (getbit 0 y) (getbit 0 z)))
  :hints (("Goal" :in-theory (e/d (bitxor getbit)
                                  (bvxor-1-becomes-bitxor)))))


(defthm equal-of-bitxor-and-bitxor-same-5
  (equal (equal (bitxor x y) (bitxor z x))
         (equal (getbit 0 y) (getbit 0 z)))
  :hints (("Goal" :in-theory (e/d (bitxor getbit)
                                  (bvxor-1-becomes-bitxor)))))


(defthm equal-of-bitxor-and-bitxor-same-6
  (equal (equal (bitxor y x) (bitxor z x))
         (equal (getbit 0 y) (getbit 0 z)))
  :hints (("Goal" :in-theory (e/d (bitxor getbit)
                                  (bvxor-1-becomes-bitxor)))))

(defthm bvchop-of-bitxor
  (implies (and (< 0 n)
                (natp n))
           (equal (bvchop n (bitxor x y))
                  (bitxor x y))))

(defthm bitxor-of-bvchop-arg1
  (implies (posp size)
           (equal (bitxor (bvchop size x) y)
                  (bitxor x y)))
  :hints (("Goal" :in-theory (e/d (bitxor) (bvxor-1-becomes-bitxor)))))

(defthm bitxor-of-bvchop-arg2
  (implies (posp size)
           (equal (bitxor y (bvchop size x))
                  (bitxor y x)))
  :hints (("Goal" :use bitxor-of-bvchop-arg1
           :in-theory (disable bitxor-of-bvchop-arg1))))

(defthm bitxor-of-bvxor-arg1
  (implies (posp size)
           (equal (bitxor (bvxor size x y) z)
                  (bitxor (bitxor x y) z)))
  :hints (("Goal" ;:cases ((equal size 1))
           :in-theory (e/d (;bitxor
                            ) (;BVXOR-1-BECOMES-BITXOR
                               bitxor-commutative
                               bitxor-commutative
                               bitxor-associative)))))

(defthm bitxor-of-bvxor-arg2
  (implies (posp size)
           (equal (bitxor z (bvxor size x y))
                  (bitxor z (bitxor x y)))))

;need more bitxor cancel rules?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bitxor-commutative-alt
  (implies (syntaxp (smaller-bvxor-arg b a))
           (equal (bitxor a b)
                  (bitxor b a)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable bitxor-commutative))))

(in-theory (disable bitxor-commutative))
(theory-invariant (incompatible (:rewrite bitxor-commutative) (:rewrite bitxor-commutative-alt)))

(defthm bitxor-commutative-2-alt
  (implies (syntaxp (smaller-bvxor-arg a b))
           (equal (bitxor b (bitxor a c))
                  (bitxor a (bitxor b c))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable bitxor-commutative-2))))

(in-theory (disable bitxor-commutative-2))
(theory-invariant (incompatible (:rewrite bitxor-commutative-2) (:rewrite bitxor-commutative-2-alt)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm slice-of-bitxor-too-high
  (implies (and (<= 1 low)
                (integerp low))
           (equal (slice high low (bitxor x y))
                  0))
  :hints (("Goal" :in-theory (e/d (bitxor slice-too-high-is-0)
                                  (bvxor-1-becomes-bitxor)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;don't need if we have polarity?
(defthm bitxor-subst-arg2-one-version
  (implies (and (not (equal (getbit 0 x) free)) ;we expect free to be 0
                (syntaxp (equal free ''0))
                (equal 0 free))
           (equal (bitxor y x)
                  (bitxor y 1)))
  :hints (("Goal" :in-theory (enable bitxor-split))))

;don't need if we have polarity?
(defthm bitxor-subst-arg1-one-version
  (implies (and (not (equal (getbit 0 x) free)) ;we expect free to be 0
                (syntaxp (equal free ''0))
                (equal 0 free))
           (equal (bitxor x y)
                  (bitxor 1 y)))
  :hints (("Goal" :use bitxor-subst-arg2-one-version)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm not-equal-of-getbit-of-0-and-bitxor-of-1
  (not (equal (getbit 0 x) (bitxor 1 x)))
  :hints (("Goal" :cases ((equal 0 (getbit 0 x))))))

(defthm not-equal-of-getbit-of-0-and-bitxor-of-1-alt
  (not (equal (bitxor 1 x) (getbit 0 x)))
  :hints (("Goal" :use not-equal-of-getbit-of-0-and-bitxor-of-1
           :in-theory (disable not-equal-of-getbit-of-0-and-bitxor-of-1))))

(defthm equal-of-getbit-and-bitxor-same
  (equal (equal (getbit 0 x) (bitxor x y))
         (equal 0 (getbit 0 y)))
  :hints (("Goal"
           :use BITXOR-OF-GETBIT-ARG2 ;do we have the complete set of these?
           :in-theory (e/d (;bitxor bvxor
                            )
                           (;bvxor-1-becomes-bitxor logxor-bvchop-bvchop
                            bitxor-of-getbit-arg2)))))

(defthm equal-of-getbit-and-bitxor-same-alt2
  (equal (equal (getbit 0 x) (bitxor y x)) ;x might appear in other positions as well...
         (equal 0 (getbit 0 y)))
  :hints (("Goal"
           :use BITXOR-OF-GETBIT-ARG2 ;do we have the complete set of these?
           :in-theory (e/d (;bitxor bvxor
                            )
                           (;bvxor-1-becomes-bitxor logxor-bvchop-bvchop
                            bitxor-of-getbit-arg2)))))

(defthm equal-of-getbit-and-bitxor-same-alt
  (equal (equal (bitxor x y) (getbit 0 x))
         (equal 0 (getbit 0 y)))
  :hints (("Goal" :use equal-of-getbit-and-bitxor-same
           :in-theory (disable equal-of-getbit-and-bitxor-same))))

(defthm equal-of-getbit-and-bitxor-same-alt3
  (equal (equal (bitxor y x) (getbit 0 x))
         (equal 0 (getbit 0 y)))
  :hints (("Goal" :use equal-of-getbit-and-bitxor-same
           :in-theory (disable equal-of-getbit-and-bitxor-same))))

(defthm getbit-0-of-logxor
  (equal (getbit 0 (logxor x y))
         (bitxor x y))
  :hints (("Goal" ;:cases ()
           :in-theory (e/d (bitxor bvxor getbit) (BVXOR-1-BECOMES-BITXOR logxor)))))

(defthmd equal-of-bitxor-and-1
  (equal (equal (bitxor x y) 1)
         (or (and (equal (getbit 0 x) 1)
                  (equal (getbit 0 y) 0))
             (and (equal (getbit 0 x) 0)
                  (equal (getbit 0 y) 1)))))

(defthmd equal-of-bitxor-and-0
  (equal (equal (bitxor x y) 0)
         (or (and (equal (getbit 0 x) 0)
                  (equal (getbit 0 y) 0))
             (and (equal (getbit 0 x) 1)
                  (equal (getbit 0 y) 1)))))
