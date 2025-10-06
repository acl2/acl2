; Signed bit-vector "less than" comparison
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "sbvlt-def")
(include-book "bvchop")
(include-book "getbit")
(local (include-book "logext")) ;todo: include less?
(include-book "kestrel/utilities/polarity" :dir :system)
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;drop?
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "unsigned-byte-p"))
(local (include-book "signed-byte-p"))

(defthm not-sbvlt-same
  (not (sbvlt size x x))
  :hints (("Goal" :in-theory (enable sbvlt))))

;todo: not true:
;; (defthm sbvlt-when-size-is-not-positive
;;   (implies (<= size 0)
;;            (not (sbvlt size x y)))
;;   :hints (("Goal"
;; ;           :cases ((equal 0 size))
;;            :in-theory (enable sbvlt))))

(defthm sbvlt-of-bvchop-arg2
  (implies (posp size)
           (equal (sbvlt size (bvchop size k) x)
                  (sbvlt size k x)))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-of-bvchop-arg3
  (implies (posp size)
           (equal (sbvlt size x (bvchop size k))
                  (sbvlt size x k)))
  :hints (("Goal" :in-theory (enable sbvlt))))

;; x<free and free<=y imply x<y
(defthmd sbvlt-transitive-core-1
  (implies (and (sbvlt size x free)
                (not (sbvlt size y free)))
           (sbvlt size x y))
  :hints (("Goal" :in-theory (enable sbvlt))))

;hyps reordered in case the known fact is about y
(defthmd sbvlt-transitive-core-1-alt
  (implies (and (not (sbvlt size y free))
                (sbvlt size x free))
           (sbvlt size x y))
  :hints (("Goal" :in-theory (enable sbvlt))))

;; x<=free and free<y imply x<y
(defthmd sbvlt-transitive-core-2
  (implies (and (not (sbvlt size free x))
                (sbvlt size free y))
           (sbvlt size x y))
  :hints (("Goal" :in-theory (enable sbvlt))))

;hyps reordered in case the known fact is about y
(defthmd sbvlt-transitive-core-2-alt
  (implies (and (sbvlt size free y)
                (not (sbvlt size free x)))
           (sbvlt size x y))
  :hints (("Goal" :in-theory (enable sbvlt))))

;fixme what about rules to turn an sbvlt into nil?
(defthm sbvlt-transitive-1-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (sbvlt size y free))
                (syntaxp (quotep free))
                (sbvlt size k free) ; gets computed
                )
           (sbvlt size k y))
  :hints (("Goal" :in-theory (enable sbvlt-transitive-core-1))))

(defthm sbvlt-transitive-2-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (sbvlt size free y)
                (syntaxp (quotep free))
                (not (sbvlt size free k)) ; gets computed
                )
           (sbvlt size k y))
  :hints (("Goal" :in-theory (enable sbvlt-transitive-core-2))))

(defthm sbvlt-transitive-1-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (sbvlt size x free)
                (syntaxp (quotep free))
                (not (sbvlt size k free)) ; gets computed
                )
           (sbvlt size x k))
  :hints (("Goal" :in-theory (enable sbvlt-transitive-core-1))))

(defthm sbvlt-transitive-2-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (sbvlt size free x))
                (syntaxp (quotep free))
                (sbvlt size free k) ; gets computed
                )
           (sbvlt size x k))
  :hints (("Goal" :in-theory (enable sbvlt))))

;fixme make a version with a strict < as a hyp (can then weaken the other hyp by 1? what about overflow?) see sbvlt-false-when-sbvlt-gen
;;y<=free and free<=x imply y<=x
(defthmd sbvlt-transitive-core-3
  (implies (and (not (sbvlt size free y))
                (not (sbvlt size x free)))
           (not (sbvlt size x y)))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-transitive-3-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (sbvlt size free y))
                (syntaxp (quotep free))
                (not (sbvlt size k free)) ; gets computed
                )
           (not (sbvlt size k y)))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-transitive-3-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (sbvlt size x free))
                (syntaxp (quotep free))
                (not (sbvlt size free k)) ; gets computed
                )
           (not (sbvlt size x k)))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-when-not-integerp-arg2
  (implies (not (integerp x))
           (equal (sbvlt size x y)
                  (sbvlt size 0 y)))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-when-not-integerp-arg3
  (implies (not (integerp y))
           (equal (sbvlt size x y)
                  (sbvlt size x 0)))
  :hints (("Goal" :in-theory (enable sbvlt))))

;rename
;fffixme more like this (> instead of <, not a negated sbvlt, bvlt instead of sbvlt)
;; this may be expensive
(defthm equal-constant-when-not-sbvlt
  (implies (and (syntaxp (quotep k))
                (not (sbvlt freesize x free))
                (syntaxp (and (quotep free)
                              (quotep freesize)))
                (sbvlt freesize k free))
           (not (equal k x))))

;rename.  be consistent about "equal-constant" vs "equal-of-constant"
; when free<x and k<=free, we know x<>k
;; this may be expensive
(defthm equal-of-constant-when-sbvlt
  (implies (and (syntaxp (quotep k))
                (sbvlt freesize free x) ;2 free vars here
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                (sbvle freesize k free)) ;gets computed
           (not (equal k x))))

;; Rewrite sbvlt to < when possible
(defthmd sbvlt-becomes-<
  (implies (and (< x (expt 2 (+ -1 n)))
                (< y (expt 2 (+ -1 n)))
                (posp n)
                (natp x)
                (natp y))
           (equal (sbvlt n x y)
                  (< x y)))
  :hints (("Goal" :in-theory (enable sbvlt logext-identity signed-byte-p))))

;gen
(defthm not-sbvlt-of-maxint-32
  (not (sbvlt 32 2147483647 x))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-when-<
  (implies (and (< x y)
                (unsigned-byte-p (+ -1 n) x)
                (unsigned-byte-p (+ -1 n) y)
                (posp n))
           (sbvlt n x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil)))
  :hints (("Goal" :in-theory (enable SBVLT))))

(defthm sbvlt-transitive-another-cheap
  (implies (and (not (sbvlt 32 free x))
                (sbvlt free2 free y) ;poor man's backchain limit (Axe lacks backchain limits)
                (equal 32 free2))
           (sbvlt 32 x y))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm not-sbvlt-when-sbvlt-rev-cheap
  (implies (sbvlt size x y)
           (not (sbvlt size y x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable sbvlt))))

;used by Axe (which doesn't support backchain-limits)
(defthm not-sbvlt-when-sbvlt-rev-cheap-2
  (implies (and (sbvlt free x y)
                (equal free 32)) ;the free var is a poor man's backchain limit
           (not (sbvlt 32 y x)))
  :hints(("Goal" :in-theory (enable sbvlt))))

;can this be generalized?
(defthm not-sbvlt-when-<=
  (implies (and (syntaxp (quotep k2))
                (unsigned-byte-p 31 k2) ;gets computed
                (<= x k) ;k is a free var
                (syntaxp (quotep k))
                (unsigned-byte-p 31 k) ;gets computed
                (<= k k2) ;gets computed
                (natp x))
           (not (sbvlt 32 k2 x)))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-of-+-of-expt-arg1
  (implies (and (integerp x)
                (posp size))
           (equal (sbvlt size (+ x (expt 2 size)) y)
                  (sbvlt size x y)))
  :hints (("Goal" :in-theory (e/d (sbvlt) (expt)))))

(defthm sbvlt-of-+-of-expt-arg2
  (implies (and (integerp y)
                (posp size))
           (equal (sbvlt size x (+ y (expt 2 size)))
                  (sbvlt size x y)))
  :hints (("Goal" :in-theory (e/d (sbvlt) (expt)))))

(defthm sbvlt-of-+-of-expt-arg2-gen
 (implies (and (<= size size2)
               (integerp size2)
               (integerp y)
               (posp size))
          (equal (sbvlt size x (+ y (expt 2 size2)))
                 (sbvlt size x y)))
 :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-when-not-integerp-of-size
  (implies (not (integerp size))
           (equal (sbvlt size x y)
                  (sbvlt 1 x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-of-logext-arg2
  (equal (sbvlt size (logext size x) y)
         (sbvlt size x y))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-of-logext-arg3
  (equal (sbvlt size x (logext size y))
         (sbvlt size x y))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthmd <-of-logext-and-0-alt
  (equal (< (logext 32 x) 0)
         (sbvlt 32 x 0))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-subst-constant
  (implies (and (syntaxp (not (quotep x)))
                (equal (bvchop free x) k)
                (syntaxp (quotep k))
                (<= size free)
                (posp size)
                (integerp free))
           (equal (sbvlt size x y)
                  (sbvlt size k y)))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-subst-constant-alt
  (implies (and (syntaxp (not (quotep x)))
                (equal (bvchop free x) k)
                (syntaxp (quotep k))
                (<= size free)
                (posp size)
                (integerp free))
           (equal (sbvlt size y x)
                  (sbvlt size y k)))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-subst-constant-same-arg2
  (implies (and (syntaxp (not (quotep x)))
                (equal (bvchop size x) k)
                (syntaxp (quotep k))
                (posp size)
                )
           (equal (sbvlt size x y)
                  (sbvlt size k y)))
  :hints (("Goal" ;:cases ((posp size))
           :in-theory (enable sbvlt))))

;rename
(defthm size-of--1-and-0
  (sbvlt size -1 0)
  :hints (("Goal" :in-theory (enable sbvlt))))

;rename
(defthm sbvlt-trim-constant-right
  (implies (and (syntaxp (and (quotep k) (quotep size)))
                (not (unsigned-byte-p size k))
                (posp size))
           (equal (sbvlt size x k)
                  (sbvlt size x (bvchop size k))))
  :hints (("Goal" :in-theory (enable sbvlt)
           :cases ((natp size)))))

;rename
(defthm sbvlt-trim-constant-left
  (implies (and (syntaxp (and (quotep k) (quotep size)))
                (not (unsigned-byte-p size k))
                (posp size))
           (equal (sbvlt size k x)
                  (sbvlt size (bvchop size k) x)))
  :hints (("Goal" :in-theory (enable sbvlt)
           :cases ((natp size)))))

(defthm sbvlt-transitive-free
  (implies (and (sbvlt size x free)
;                (syntaxp (and (quotep free) (quotep size)))
                (sbvlt size free y))
           (sbvlt size x y))
  :hints (("Goal" :in-theory (enable sbvlt))))

;restrict?
(defthm sbvlt-transitive-free-back
  (implies (and (not (sbvlt size x free))
                (not (sbvlt size free y)))
           (not (sbvlt size x y)))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-transitive-1
  (implies (and (sbvlt 32 i free)
                (not (sbvlt 32 len free)))
           (sbvlt 32 i len)))

;todo: flesh out this theory fully
;could be expensive...
(defthm sbvlt-transitive-another
  (implies (and (not (sbvlt 32 free x))
                (sbvlt 32 free y))
           (sbvlt 32 x y)))

(defthm not-sbvlt-of-maxint
  (implies (and (syntaxp (quotep k))
                (equal k (- (expt 2 (- size 1)) 1))
                (posp size))
           (not (sbvlt size k x)))
  :hints (("Goal" :in-theory (enable sbvlt))))

;loops with defn sbvlt?
(defthmd <=-of-logext-and--1
  (equal (< -1 (logext size y))
         (not (sbvlt size y 0)))
  :hints (("Goal" :in-theory (enable sbvlt))))

;todo: rename
(defthm not-equal-max-int-when-<=
  (implies (and (not (sbvlt 32 free x))
                (not (equal (bvchop 32 free) 2147483647)))
           (not (equal 2147483647 (bvchop 32 x))))
  :hints (("Goal" :in-theory (enable sbvlt))))

;; Either x<y or y<x or they are equal.
;move
(defthm sbvlt-trichotomy
  (or (sbvlt size x y)
      (sbvlt size y x)
      (equal (bvchop size x) (bvchop size y)))
  :rule-classes nil
  :hints (("Goal" :cases ((posp size))
           :in-theory (enable sbvlt
                              EQUAL-OF-LOGEXT-AND-LOGEXT))))

(defthm sbvlt-of-minus-one
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal k (+ -1 (expt 2 size))) ;minus one
                (unsigned-byte-p free x)
                (< free size)
                (natp size))
           (sbvlt size k x))
  :hints (("Goal" :in-theory (enable sbvlt))))

;; When do we want this?
(defthmd sbvlt-of-0-arg3
  (implies (posp size)
           (equal (sbvlt size x 0)
                  (equal 1 (getbit (+ -1 size) x))))
  :hints (("Goal" :in-theory (enable sbvlt logext-cases))))

;; In case we don't want to rewrite the sbvlt.
(defthm getbit-when-not-sbvlt-of-0-cheap
  (implies (not (sbvlt 32 x 0))
           (equal (getbit 31 x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable sbvlt))))

;; In case we don't want to rewrite the sbvlt.
(defthm getbit-when-sbvlt-of-0-cheap
  (implies (sbvlt 32 x 0)
           (equal (getbit 31 x)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable sbvlt))))

;todo: gen the 0
(defthm sbvlt-unique-weaken
  (implies (and (syntaxp (want-to-weaken (sbvlt 32 i 0)))
                (not (sbvlt 32 0 i)))
           (equal (sbvlt 32 i 0)
                  (not (equal 0 (bvchop 32 i)))))
  :hints (("Goal" :in-theory (enable sbvlt))))

;gen
(defthm sbvlt-of-maxint-when-sbvlt
  (implies (sbvlt 32 n free)
           (sbvlt 32 n 2147483647)))

(defthm sbvlt-of-ifix-arg2
  (equal (sbvlt size (ifix x) y)
         (sbvlt size x y))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-of-ifix-arg3
  (equal (sbvlt size x (ifix y))
         (sbvlt size x y))
  :hints (("Goal" :in-theory (enable sbvlt))))
