; Rules about BVLT
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvlt-def")
(include-book "unsigned-byte-p")
(include-book "bvplus") ;drop!
(include-book "bvminus") ;drop! but is used below
(include-book "kestrel/arithmetic-light/ceiling-of-lg-def" :dir :system)
(local (include-book "kestrel/arithmetic-light/ceiling-of-lg" :dir :system))
(local (include-book "slice")) ; since we open getbit below
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;rename
(defthm bvlt-of-0-arg3
  (not (bvlt size x 0))
  :hints (("Goal" :in-theory (enable bvlt))))

;use polarity?
(defthmd bvlt-of-0-arg2
  (equal (bvlt size 0 x)
         (not (equal 0 (bvchop size x))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm booleanp-of-bvlt
  (booleanp (bvlt size x y)))

;rename?
(defthm not-bvlt-self
  (not (bvlt size x x))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm not-equal-when-bvlt
  (implies (bvlt freesize x y)
           (not (equal x y))))

(defthm not-equal-when-bvlt-alt
  (implies (bvlt freesize y x)
           (not (equal x y))))

;rename
(defthm bvlt-trim-constant-arg2
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (unsigned-byte-p size k))
                (natp size) ; prevents loops
                )
           (equal (bvlt size x k)
                  (bvlt size x (bvchop size k))))
  :hints (("Goal" :in-theory (enable bvlt))))

;rename
(defthm bvlt-trim-constant-arg1
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (unsigned-byte-p size k))
                (natp size) ; prevents loops
                )
           (equal (bvlt size k x)
                  (bvlt size (bvchop size k) x)))
  :hints (("Goal" :in-theory (enable bvlt))))

;rename
(defthm not-bvlt-of-max-arg2
  (not (bvlt size (+ -1 (expt 2 size)) x))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm not-bvlt-of-max-arg2-constant-version
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal k (+ -1 (expt 2 size)))) ;gets computed
           (not (bvlt size k x))))

;todo: use polarities?
(defthm bvlt-of-max-arg3
  (implies (natp size)
           (equal (bvlt size x (+ -1 (expt 2 size)))
                  (not (equal (+ -1 (expt 2 size)) (bvchop size x)))))
  :hints (("Goal" :in-theory (enable bvlt))))

;todo: use polarities?
(defthm bvlt-of-max-arg3-constant-version
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal k (+ -1 (expt 2 size))) ;gets computed
                (natp size))
           (equal (bvlt size x k)
                  (not (equal k (bvchop size x)))))
  :hints (("Goal" :in-theory (enable bvlt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; x<free and free<=y imply x<y
(defthmd bvlt-transitive-core-1
  (implies (and (bvlt size x free)
                (not (bvlt size y free)))
           (bvlt size x y))
  :hints (("Goal" :in-theory (enable bvlt))))

;; Special case where x is a constant.
(defthm bvlt-transitive-1-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size y free))
                (syntaxp (quotep free))
                (bvlt size k free) ; gets computed
                )
           (bvlt size k y))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-1))))

;; Special case where y is a constant.
(defthm bvlt-transitive-1-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (bvlt size x free)
                (syntaxp (quotep free))
                (not (bvlt size k free)) ; gets computed
                )
           (bvlt size x k))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; x<=free and free<y imply x<y
(defthmd bvlt-transitive-core-2
  (implies (and (not (bvlt size free x))
                (bvlt size free y))
           (bvlt size x y))
  :hints (("Goal" :in-theory (enable bvlt))))

;; Special case where x is a constant.
(defthm bvlt-transitive-2-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (bvlt size free y)
                (syntaxp (quotep free))
                (not (bvlt size free k)) ; gets computed
                )
           (bvlt size k y))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-2))))

;; Special case where y is a constant.
(defthm bvlt-transitive-2-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size free x))
                (syntaxp (quotep free))
                (bvlt size free k) ; gets computed
                )
           (bvlt size x k))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;todo: make a version with a strict < as a hyp (can then weaken the other hyp by 1? what about overflow?)
;; y<=free and free<=x imply y<=x
(defthmd bvlt-transitive-core-3
  (implies (and (not (bvlt size free y))
                (not (bvlt size x free)))
           (not (bvlt size x y)))
  :hints (("Goal" :in-theory (enable bvlt))))

;; Special case where x is a constant.
(defthm bvlt-transitive-3-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size free y))
                (syntaxp (quotep free))
                (not (bvlt size k free)) ; gets computed
                )
           (not (bvlt size k y)))
  :hints (("Goal" :in-theory (enable bvlt))))

;; Special case where y is a constant.
(defthm bvlt-transitive-3-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size x free))
                (syntaxp (quotep free))
                (not (bvlt size free k)) ; gets computed
                )
           (not (bvlt size x k)))
  :hints (("Goal" :in-theory (enable bvlt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;y<free and free-1<=x imply y<=x
(defthmd bvlt-transitive-core-4
  (implies (and (bvlt size y free)
                (not (bvlt size x (+ -1 free))) ; if free=0, then (bvlt size y free) above will be false
                (integerp free)
                (natp size))
           (not (bvlt size x y)))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases))))

;; Special case where x is a constant.
(defthm bvlt-transitive-4-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (bvlt size y free) ; y<free
                (syntaxp (quotep free))
                (not (bvlt size k (+ -1 free))) ;gets computed ; free-1<=k
                (integerp free) ; gets computed
                (natp size))
           (not (bvlt size k y)))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-4))))

;; Special case where y is a constant and we rephrase to match the free var better.
(defthm bvlt-transitive-4-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size x free)) ; free<=x
                (syntaxp (quotep free))
                (bvle size k free) ;gets computed, k<=free
                (integerp free) ; gets computed
                (natp size))
           (not (bvlt size x k)))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases) :use (:instance bvlt-transitive-core-4 (free (+ 1 free)) (y k)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;y<=free+1 and free<x imply y<=x
(defthmd bvlt-transitive-core-5
  (implies (and (not (bvlt size (+ 1 free) y))
                (bvlt size free x)
                (integerp free)
                (natp size))
           (not (bvlt size x y)))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases))))

;; Special case where x is a constant and we rephrase to match the free var better.
(defthm bvlt-transitive-5-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size free y)) ; y<=free
                (syntaxp (quotep free))
                ;(bvlt size (+ -1 free) k) ;gets computed
                (bvle size free k) ;gets computed
                (integerp free)
                (natp size))
           (not (bvlt size k y)))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases)
           :use (:instance bvlt-transitive-core-5 (x k) (free (+ -1 free))))))

;; Special case where y is a constant
(defthm bvlt-transitive-5-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (bvlt size free x) ;implies that free isn't the max, so overflow below won't happen
                (syntaxp (quotep free))
                (not (bvlt size (+ 1 free) k)) ;gets computed
                (integerp free)
                (natp size))
           (not (bvlt size x k)))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-5))))

;same as bvlt-transitive-core-4-b?
;drop?
;; (defthm bvlt-transitive-free-back
;;   (implies (and (syntaxp (quotep size))
;;                 (syntaxp (quotep y))
;;                 (not (bvlt size x free))
;;                 (syntaxp (quotep free))
;;                 (bvle size y free))
;;            (not (bvlt size x y)
;;                   ))
;;   :hints (("Goal" :in-theory (enable bvlt))))

;; (defthm bvlt-transitive-free2
;;   (implies (and (bvlt size free x)
;;                 (bvle size y free))
;;            (bvlt size y x)
;;                   )
;;   :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-of-1
  (implies (posp size)
           (equal (bvlt size x 1)
                  (equal 0 (bvchop size x))))
  :hints (("Goal" :cases ((posp size))
           :in-theory (enable bvlt))))

(defthm bvlt-of-bvchop-arg2
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvlt size (bvchop size2 x) y)
                  (bvlt size x y)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-of-bvchop-arg3
  (implies (<= size size2)
           (equal (bvlt size y (bvchop size2 x))
                  (and (bvlt size y x)
                       ;if size2 isn't an integer, the bvchop is 0
                       (integerp size2))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-when-bvchop-known-subst
  (implies (and (syntaxp (not (quotep x)))
                (equal free (bvchop freesize x)) ;reordered to match better (TODO: But now this is a binding hyp)
                (syntaxp (quotep free))
                (<= size freesize)
                (natp freesize)
                (natp size))
           (equal (bvlt size y x)
                  (bvlt size y free)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-when-bvchop-known-subst-alt
  (implies (and (syntaxp (not (quotep x)))
                (equal free (bvchop freesize x)) ;reordered to match better (TODO: But now this is a binding hyp)
                (syntaxp (quotep free))
                (<= size freesize)
                (natp freesize)
                (natp size))
           (equal (bvlt size x y)
                  (bvlt size free y)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-when-arg1-is-not-an-integer
  (implies (not (integerp x))
           (equal (bvlt size x y)
                  (bvlt size 0 y)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-when-arg2-is-not-an-integer
  (implies (not (integerp x))
           (equal (bvlt size y x)
                  (bvlt size y 0)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-of-max-minus-1-arg2
  (implies (posp size)
           (equal (bvlt size (+ -2 (expt 2 size)) x)
                  (equal (+ -1 (expt 2 size)) (bvchop size x))))
  :hints (("Goal" :in-theory (enable bvlt)
           :do-not '(generalize eliminate-destructors))))

;; ;use polarity?
(defthm bvlt-of-max-minus-1-arg2-constant-version
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal k (+ -2 (expt 2 size))) ;gets computed
                (posp size))
           (equal (bvlt size k x)
                  (equal (+ 1 k) (bvchop size x)))))

;can be expensive.  needs polarities
(defthmd bvlt-when-bvlt-must-be
  (implies (not (bvlt size y x))
           (equal (bvlt size x y)
                  (not (equal (bvchop size y) (bvchop size x)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-when-bvlt-must-be-fake-free
  (implies (and (not (bvlt free y x)) ;this free var is because the axe rewriter and axe prover dont support backchain limits
                (equal free size))
           (equal (bvlt size x y)
                  (not (equal (bvchop size y)
                              (bvchop size x)))))
  :hints (("Goal" :use bvlt-when-bvlt-must-be)))

(defthm bvlt-of-max-when-bvlt
  (implies (bvlt size x free)
           (bvlt size x (+ -1 (expt 2 size))))
  :hints (("Goal" :use (:instance bvlt-transitive-core-1 (free free) (y (+ -1 (expt 2 size))))
           :in-theory (e/d (zp)
                           (bvlt-transitive-1-a
                            bvlt-transitive-2-a
                            bvlt-transitive-1-b
                            bvlt-transitive-2-b
                            ;;BVLT-TRANSITIVE-FREE-BACK
                            ;;BVLT-TRANSITIVE-FREE2-BACK
                            )))))

(defthmd bvlt-of-max-when-bvlt-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (+ -1 (expt 2 size)))
                (bvlt size x free))
           (bvlt size x k)))

;rename
(defthm bvlt-when-not-posp-arg1
  (implies (not (posp size))
           (not (bvlt size x y)))
  :hints (("Goal"
           :cases ((equal 0 size))
           :in-theory (enable bvlt))))

;is this expensive?
;the quotep hyps are new
;rename
(defthm equal-of-bvchop-impossible
  (implies (and (syntaxp (and (quotep val)
                              (quotep size)))
                (bvlt size free x)
                (syntaxp (quotep free))
                (bvle size val free) ;gets evaluated
                (natp size))
           (not (equal val (bvchop size x)))))

;this seemed to be involved in loops
;so the syntaxp hyps are new
;this was the same as the non-alt version.  just fixed it Tue Jan 26 00:16:17 2010
;rename
(defthm equal-of-bvchop-impossible-alt
  (implies (and (syntaxp (and (quotep val)
                              (quotep size)))
                (bvlt size free x)
                (syntaxp (quotep free))
                (bvle size val free) ;gets evaluated
                (natp size))
           (not (equal (bvchop size x) val))))

;rename to <-of-constant-becomes-bvlt
;disabled during library proofs
;todo: it might be better to look at the size of the constant and see if the other term fits in that many bits.
(defthmd <-becomes-bvlt
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p free x)
                (integerp k))
           (equal (< k x)
                  (if (unsigned-byte-p free k)
                      (bvlt free k x)
                    (< k 0))))
  :hints (("Goal" :in-theory (enable bvlt))))

;disabled during library proofs
;rename to <-of-constant-becomes-bvlt-alt
;todo: it might be better to look at the size of the constant and see if the other term fits in that many bits.
(defthmd <-becomes-bvlt-alt
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p free x)
                (integerp k))
           (equal (< x k)
                  (if (unsigned-byte-p free k)
                      (bvlt free x k)
                    (not (< k 0)))))
  :hints (("Goal" :in-theory (enable bvlt unsigned-byte-p))))

;do we need this?  make a weak version of <-becomes-bvlt?
;rename
(defthmd <-becomes-bvlt-alt-weak
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p free x)
                (unsigned-byte-p free k))
           (equal (< x k)
                  (bvlt free x k)))
  :hints (("Goal" :use <-becomes-bvlt-alt
           :in-theory (disable <-becomes-bvlt-alt))))

;disabled during library proofs
;could this be expensive?
(defthmd <-becomes-bvlt-free
  (implies (and (unsigned-byte-p free x)
                (unsigned-byte-p free y))
           (equal (< x y)
                  (bvlt free x y)))
  :hints (("Goal" :use (:instance <-becomes-bvlt-alt (k y))
           :in-theory (disable <-becomes-bvlt-alt))))

;could this be expensive?
;disabled during library proofs
(defthmd <-becomes-bvlt-free-alt
  (implies (and (unsigned-byte-p free y)
                (unsigned-byte-p free x))
           (equal (< x y)
                  (bvlt free x y)))
  :hints (("Goal" :use (:instance <-becomes-bvlt-alt (k y))
           :in-theory (disable <-becomes-bvlt-alt))))

(theory-invariant (incompatible (:definition bvlt) (:rewrite <-becomes-bvlt)))
(theory-invariant (incompatible (:definition bvlt) (:rewrite <-becomes-bvlt-alt)))
(theory-invariant (incompatible (:definition bvlt) (:rewrite <-becomes-bvlt-free)))
(theory-invariant (incompatible (:definition bvlt) (:rewrite <-becomes-bvlt-free-alt)))

; y<=free and free2<=x and free = free2 imply y<=x
;todo: do we need this?
(defthm bvlt-transitive-free2-back
  (implies (and (not (bvlt size free y))
                (bvle size free2 x)
                (equal free free2) ;hack?
                )
           (not (bvlt size x y)))
  :hints (("Goal" :in-theory (enable bvlt))))

;fixme think this through
;drop?
(defthm bvlt-transitive-free2-back-constants
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep size))
                (not (bvlt size free y))
                (syntaxp (quotep free))
                (bvle size free x)
                )
           (not (bvlt size x y)))
  :hints (("Goal" :use (:instance bvlt-transitive-free2-back (free2 free))
           :in-theory (disable bvlt-transitive-free2-back))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm not-equal-of-constant-when-bvlt-constant-1
  (implies (and (syntaxp (quotep const))
                (bvlt freesize free x)
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                (bvle freesize const free))
           (not (equal const x))))

(defthm not-equal-of-constant-when-bvlt-constant-2
  (implies (and (syntaxp (quotep const))
                (bvlt freesize x free)
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                (bvle freesize free const))
           (not (equal const x))))

(defthm not-equal-of-constant-when-not-bvlt-constant-1
  (implies (and (syntaxp (quotep const))
                (not (bvlt freesize x free))
                (syntaxp (quotep freesize))
                (syntaxp (quotep free))
                (bvlt freesize const free))
           (not (equal const x))))

(defthm not-equal-of-constant-when-not-bvlt-constant-2
  (implies (and (syntaxp (quotep const))
                (not (bvlt freesize free x))
                (syntaxp (quotep freesize))
                (syntaxp (quotep free))
                (bvlt freesize free const))
           (not (equal const x))))

; can we drop the -alt rules?  or add 2 more?

(defthm not-equal-of-constant-when-bvlt-constant-1-alt
  (implies (and (syntaxp (quotep const))
                (bvlt freesize free x)
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                (bvle freesize const free))
           (not (equal x const))))

(defthm not-equal-of-constant-when-bvlt-constant-2-alt
  (implies (and (syntaxp (quotep const))
                (bvlt freesize x free)
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                (bvle freesize free const))
           (not (equal x const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm equal-of-bvchop-and-constant-when-bvlt-constant-1
  (implies (and (syntaxp (quotep const))
                (bvlt freesize free x)
                (<= freesize size)
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                (bvle freesize const free)
                (integerp size))
           (not (equal const (bvchop size x)))))

(defthm equal-of-bvchop-and-constant-when-bvlt-constant-2
  (implies (and (syntaxp (quotep const))
                (bvlt freesize x free)
                (<= freesize size)
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                (bvle freesize free const)
                (integerp size))
           (not (equal const (bvchop size x)))))

(defthm equal-of-bvchop-and-constant-when-not-bvlt-constant-1
  (implies (and (syntaxp (quotep const))
                (not (bvlt freesize x free))
                (<= freesize size)
                (syntaxp (quotep freesize))
                (syntaxp (quotep free))
                (bvlt freesize const free)
                (integerp size))
           (not (equal const (bvchop size x)))))

(defthm equal-of-bvchop-and-constant-when-not-bvlt-constant-2
  (implies (and (syntaxp (quotep const))
                (not (bvlt freesize free x))
                (<= freesize size)
                (syntaxp (quotep freesize))
                (syntaxp (quotep free))
                (bvlt freesize free const)
                (integerp size))
           (not (equal const (bvchop size x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvlt-of-bvchop-arg3-same
  (equal (bvlt size x (bvchop size y))
         (bvlt size x y))
  :hints (("Goal" :cases ((natp size)))))

(defthm bvlt-of-bvchop-arg2-same
  (equal (bvlt size (bvchop size x) y)
         (bvlt size x y))
  :hints (("Goal" :cases ((natp size)))))



;todo: compare these to the transitive rules
;todo: more like these?
(defthm bvlt-when-bvlt-wider
  (implies (and (syntaxp (quotep k))
                (bvlt bigsize x free)
                (syntaxp (quotep free))
                (<= size bigsize)
                (unsigned-byte-p size free)
                (bvle size free k)
                (natp bigsize))
           (bvlt size x k))
  :hints (("Goal"
           :use (:instance <-of-bvchop-and-bvchop-same (s2 bigsize) (s1 size))
           :in-theory (e/d (bvlt) (<-of-bvchop-and-bvchop-same)))))

(defthm not-bvlt-when-not-bvlt-narrower
  (implies (and (syntaxp (quotep k))
                (not (bvlt size x free))
                (syntaxp (quotep free))
                (<= size bigsize)
                (unsigned-byte-p size k)
                (bvle size k free)
                (natp bigsize))
           (not (bvlt bigsize x k)))
  :hints (("Goal" :use (:instance bvlt-when-bvlt-wider (k free) (free k))
           :in-theory (disable bvlt-when-bvlt-wider))))

(defthm not-bvlt-when-not-bvlt-narrower2
  (implies (and (syntaxp (quotep k))
                (not (bvlt bigsize free x))
                (syntaxp (quotep free))
                (<= size bigsize)
                (unsigned-byte-p size k)
                (unsigned-byte-p size free)
                (bvle size free k)
                (natp bigsize))
           (not (bvlt size k x)))
  :hints (("Goal"  :use (:instance <-of-bvchop-and-bvchop-same (s2 bigsize) (s1 size))
           :in-theory (e/d (bvlt) (<-of-bvchop-and-bvchop-same)))))

;; ;name okay?
;; (defthm not-bvlt-when-not-bvlt-wider
;;   (implies (and (syntaxp (quotep k))
;;                 (not (bvlt bigsize x free))
;;                 (syntaxp (quotep free))
;;                 (= size bigsize) ;fffixme!
;;                 (unsigned-byte-p size free)
;;                 (bvlt size k free)
;;                 (natp bigsize)
;;                 (natp size))
;;            (not (bvlt size x k)
;;                   ))
;;   :hints (("Goal"
;;            :use (:instance <-of-bvchop-and-bvchop-same (s2 bigsize) (s1 size))
;;            :in-theory (e/d (bvlt) (<-of-bvchop-and-bvchop-same)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;the bvplus is arg2
;this generalizes some other stuff?
(defthm bvlt-of-bvplus-constant-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep size)))
                (bvlt size k k2) ;this case
                (natp size)
                (natp k))
           (equal (bvlt size (bvplus size k2 x) k)
                  (and (bvle size (- k2) x)
                       (bvlt size x (- k k2)))))
  :hints (("Goal" :in-theory (enable bvplus bvlt bvchop-of-sum-cases))))

;fixme other cases?
(defthm bvlt-of-bvplus-constant-and-constant-safe
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep size)))
                (bvle size k2 k) ;no overflow
                (bvlt size x (- k2)) ;no overflow
                (natp size)
                (natp k))
           (equal (bvlt size (bvplus size k2 x) k)
                  (bvlt size x (bvminus size k k2))))
  :hints (("Goal" :in-theory (e/d (bvplus bvlt bvchop-of-sum-cases bvminus)
                                  (expt)))))

(defthm bvlt-of-bvplus-constant-and-constant-other
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep size)))
                (bvle size k2 k) ;this case
                (natp size)
                (natp k))
           (equal (bvlt size (bvplus size k2 x) k)
                  (if (bvlt size (bvminus size (+ -1) k2) x)
                      t
                    (bvlt size x (bvminus size k k2)))))
  :hints (("Goal" :in-theory (enable bvplus bvlt bvchop-of-sum-cases bvminus))))

(defthm bvlt-of-bvplus-constant-and-constant-gen
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep size)))
                (natp size)
                (natp k))
           (equal (bvlt size (bvplus size k2 x) k)
                  (if (bvlt size k k2)
                      (and (bvle size (- k2) x)
                           (bvlt size x (- k k2)))
                    (if (bvlt size (bvminus size (+ -1) k2) x)
                        t
                      (bvlt size x (bvminus size k k2))))))
  :hints (("Goal" :use (bvlt-of-bvplus-constant-and-constant-other
                         bvlt-of-bvplus-constant-and-constant)
           :in-theory (disable bvlt-of-bvplus-constant-and-constant-other
                               bvlt-of-bvplus-constant-and-constant))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;the bvplus is arg3
(defthm bvlt-of-bvplus-constant-and-constant-safe2
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep size)))
                (bvle size k2 k) ;no overflow
                (bvlt size x (- k2)) ;no overflow
                (natp size)
                (natp k))
           (equal (bvlt size k (bvplus size k2 x))
                  (bvlt size (bvminus size k k2) x)))
  :hints (("Goal" :in-theory (e/d (bvplus bvlt bvchop-of-sum-cases bvminus)
                                  (expt)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;use polarities
(defthmd bvlt-when-bvlt-must-be-gen
  (implies (and (not (bvlt freesize y x))
                (<= freesize size)
                (unsigned-byte-p freesize x) ;x may be a constant
;                (natp freesize) ;drop
                (integerp size))
           (equal (bvlt size x y)
                  (not (equal (bvchop size y)
                              (bvchop size x)))))
  :hints (("Goal"
           :use (bvlt-when-bvlt-must-be
                 (:instance not-bvlt-when-not-bvlt-narrower (bigsize size) (size freesize) (x y) (k x) (free x)))
           :in-theory (disable bvlt-when-bvlt-must-be-fake-free))))

;; Rewrite bvlt to < when possible
(defthmd bvlt-becomes-<
  (implies (and (< x (expt 2 n))
                (< y (expt 2 n))
                (natp x)
                (natp y))
           (equal (bvlt n x y)
                  (< x y)))
  :hints (("Goal" :in-theory (enable expt ;why?
                                     bvlt bvchop-identity))))

(defthm not-bvlt-of-constant-when-<=-of-constant
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p size k)
                (<= i free)
                (syntaxp (quotep free))
                (unsigned-byte-p size free)
                (<= free k) ;gets computed
                (natp i)
                (natp size))
           (not (bvlt size k i)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm not-bvlt-of-constant-when-<-of-constant
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p size k)
                (< i free)
                (syntaxp (quotep free))
                (unsigned-byte-p size free)
                (<= free (+ 1 k)) ;gets computed
                (natp i)
                (natp size))
           (not (bvlt size k i)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm <-when-bvlt
  (implies (and (bvlt size x y) ;size is a free var
                (unsigned-byte-p size x)
                (natp y))
           (< x y))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-when-bvlt-false
   (implies (and (syntaxp (quotep size))
                 (syntaxp (quotep k))
                 (bvlt size x free)
                 (syntaxp (quotep free))
                 (bvle size free (+ 1 k))
                 (integerp k)
                 (natp size))
            (not (bvlt size k x)))
   :hints
   (("Goal"
     :cases ((integerp k))
     :in-theory (enable bvlt bvchop-of-sum-cases))))

(defthm bvlt-when-bvlt-false2
  (implies (and (syntaxp (quotep k))
                (BVLT size free x)
                (syntaxp (quotep free))
                (syntaxp (quotep size))
                (bvle size (+ -1 k) free) ;gets evaluated
                (integerp k)
                (natp size)
                )
           (not (BVLT size x k)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   bvchop-of-sum-cases
                                   bvplus)
                                  ()))))

(defthm bvlt-when-not-bvlt-one-more
  (implies (and (syntaxp (quotep const)) ;new
                (not (bvlt size free x))
                (syntaxp (quotep free)) ;new
                (equal free (+ 1 const))
                (unsigned-byte-p size free)
                (unsigned-byte-p size const)
                (integerp size))
           (equal (bvlt size const x)
                  (equal free (bvchop size x))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-when-not-bvlt-one-less
  (implies (and (syntaxp (quotep const))
                (not (bvlt size x free))
                (syntaxp (quotep free))
                (equal free (+ -1 const))
                (unsigned-byte-p size free)
                (unsigned-byte-p size const)
;                (posp const) ; ?
                (integerp size))
           (equal (bvlt size x const)
                  (equal free (bvchop size x))))
  :hints (("Goal" :in-theory (enable bvlt))))

;rename
(defthm bvlt-false-when-bvlt-better
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (bvlt size free x) ; free < x
                (syntaxp (quotep free))
                (bvle size k (bvplus size 1 free)) ; k <= free+1, gets computed
                )
           (not (bvlt size x k))) ; not(x < k), i.e., x>=k
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable bvlt bvchop-of-sum-cases bvplus))))

;use polarities?
(defthm bvlt-unique
  (implies (and (bvlt size x free)
                (syntaxp (quotep free))
                (equal free (+ 2 k))
                (unsigned-byte-p size k)
                (natp size)
                )
           (equal (bvlt size k x)
                  (equal (+ 1 k) (bvchop size x))))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases))))

(defthm not-bvlt-of--1-arg1
  (not (bvlt size -1 x))
  :hints (("Goal" :in-theory (enable bvlt))))

;gen this somehow?
(defthm equal-of-0-when-bvlt
  (implies (bvlt size free x)
           (not (equal 0 x))))

;drop if we'll always enable bvle?
(defthm bvle-self
  (bvle size x x))

(defthm not-bvlt-when-bvlt-opposite-smaller-and-unsigned-byte-p
  (implies (and (bvlt freesize y x)
                (<= freesize size)
                (unsigned-byte-p freesize y) ; means that y is still smaller even if we consider more bits
                (integerp size)
                (natp freesize))
           (not (bvlt size x y)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm not-bvlt-of-expt-same-arg3
  (implies (natp size)
           (not (bvlt size x (expt 2 size))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-1
  (equal (bvlt 1 x y)
         (and (equal 0 (getbit 0 x))
              (equal 1 (getbit 0 y))))
  :hints (("Goal" :in-theory (enable bvlt getbit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;gen the 1
(defthm bvlt-of-bvplus-1-cancel
  (implies (posp size)
           (equal (bvlt size (bvplus size 1 x) x)
                  (equal (bvchop size x) (+ -1 (expt 2 size)))))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases bvplus))))

(defthm bvlt-of-bvplus-1-cancel-alt
  (implies (posp size)
           (equal (bvlt size x (bvplus size 1 x))
                  (not (equal (bvchop size x) (+ -1 (expt 2 size))))))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases bvplus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;figure out how to restrict this case right
(defthm bvlt-when-bvlt-reverse
  (implies (and (bvlt size free x) ;free var helps restrict this rule to the case we care about?
                (equal free y))
           (not (bvlt size x y)))
  :hints (("Goal" :in-theory (enable bvlt))))

;add a bvlt and bvlt imply bvlt rule?

;this looped before i put in the fakefree stuff (which is because the axe prover doesn have backchain limits)
(defthm bvlt-when-not-bvlt
  (implies (and (NOT (BVLT fakefreesize free x))
                (equal fakefreesize size) ;gross?
                (bvlt fakefreesize2 free k)
                (equal fakefreesize2 size) ;gross?
                )
           (bvlt size x k))
  :hints (("Goal" :in-theory (enable bvlt ;unsigned-byte-p
                                     ))))

;what other rules are missing?
(defthm bvlt-false-when-bvlt
  (implies (and (bvlt size free x)
                (bvle size k free))
           (not (bvlt size x k)))
  :hints (("Goal" :in-theory (enable bvlt unsigned-byte-p))))

(defthm bvlt-when-bvlt-smaller
  (implies (and (bvlt freesize x y)
                (<= freesize size)
                (unsigned-byte-p freesize x)
                ;; (unsigned-byte-p freesize y)
                (integerp size))
           (bvlt size x y))
  :hints (("Goal" :in-theory (enable bvlt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthmd bvchop-tighten-when-bvlt-of-constant-helper
    (implies (and (bvlt size x k) ; k is a free var
                  (syntaxp (and (quotep k)
                                (quotep size)))
                  (< (ceiling-of-lg k) size) ; avoids loops
                  (unsigned-byte-p size x) ; dropped below
                  (natp k))
             (equal (bvchop size x)
                    (bvchop (ceiling-of-lg k) x)))
    :hints (("Goal" :in-theory (enable bvlt)))))

(defthmd bvchop-tighten-when-bvlt-of-constant
  (implies (and (bvlt size x k) ; k is a free var
                (syntaxp (and (quotep k)
                              (quotep size)))
                (< (ceiling-of-lg k) size) ; avoids loops
                ;; (unsigned-byte-p size x)
                (natp k))
           (equal (bvchop size x)
                  (bvchop (ceiling-of-lg k) x)))
  :hints (("Goal" :use (:instance bvchop-tighten-when-bvlt-of-constant-helper
                                  (x (bvchop size x)))
           :in-theory (disable bvchop-tighten-when-bvlt-of-constant-helper))))

(local
  (defthmd bvchop-tighten-when-not-bvlt-of-constant-helper
    (implies (and (not (bvlt size k x)) ; k is a free var
                  (syntaxp (and (quotep k)
                                (quotep size)))
                  (< (ceiling-of-lg (+ 1 k)) size) ; avoids loops
                  (unsigned-byte-p size x) ; dropped below
                  (natp k))
             (equal (bvchop size x)
                    (bvchop (ceiling-of-lg (+ 1 k)) x)))
    :hints (("Goal" :in-theory (enable bvlt)))))

(defthmd bvchop-tighten-when-not-bvlt-of-constant
  (implies (and (not (bvlt size k x)) ; k is a free var
                (syntaxp (and (quotep k)
                              (quotep size)))
                (< (ceiling-of-lg (+ 1 k)) size) ; avoids loops
                ;; (unsigned-byte-p size x)
                (integerp size)
                (natp k))
           (equal (bvchop size x)
                  (bvchop (ceiling-of-lg (+ 1 k)) x)))
:hints (("Goal" :use (:instance bvchop-tighten-when-not-bvlt-of-constant-helper
                                (x (bvchop size x)))
         :in-theory (disable bvchop-tighten-when-not-bvlt-of-constant-helper))))
