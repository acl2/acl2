; Unsigned bit-vector "less than" comparison
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "unsigned-byte-p")
(include-book "bvplus") ;drop!
(include-book "bvminus") ;drop! but is used below
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;fixme some of these could be macros...
;unsigned less-than
(defund bvlt (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (< (bvchop size x)
     (bvchop size y)))

;unsigned less-than-or-equal
(defun bvle (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (not (bvlt size y x)))

;unsigned greater-than
(defun bvgt (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (bvlt size y x))

;unsigned greater-than-or-equal
(defun bvge (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (not (bvlt size x y)))

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
  (equal (booleanp (bvlt size x y))
         t))

;rename
(defthm bvlt-self
  (not (bvlt size x x))
  :hints (("Goal" :in-theory (enable bvlt))))

;rename
(defthm equal-when-bvlt
  (implies (bvlt freesize x y)
           (not (equal x y))))

;rename
(defthm equal-when-bvlt-alt
  (implies (bvlt freesize y x)
           (not (equal x y))))

;replace with general trim rule?
(defthm bvlt-trim-constant-arg2
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (unsigned-byte-p size k))
                (natp size) ; prevents loops
                )
           (equal (bvlt size x k)
                  (bvlt size x (bvchop size k))))
  :hints (("Goal" :in-theory (enable bvlt))))

;replace with general trim rule?
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
(defthm bvlt-of-max
  (not (bvlt size (+ -1 (expt 2 size)) x))
  :hints (("Goal" :in-theory (enable bvlt))))

;rename
(defthm bvlt-of-max-constant-version
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal k (+ -1 (expt 2 size)))) ;gets computed
           (not (bvlt size k x))))

;todo: use polarities?
(defthm bvlt-max-arg3
  (implies (natp size)
           (equal (bvlt size x (+ -1 (expt 2 size)))
                  (not (equal (+ -1 (expt 2 size)) (bvchop size x)))))
  :hints (("Goal" :in-theory (enable bvlt))))

;todo: use polarities?
(defthm bvlt-max-arg3-constant-version
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal k (+ -1 (expt 2 size))) ;gets computed
                (natp size))
           (equal (bvlt size x k)
                  (not (equal k (bvchop size x)))))
  :hints (("Goal" :in-theory (enable bvlt))))

;delete
;; (defthm bvlt-max-val
;;   (equal (bvlt 31 x 2147483647)
;;          (not (equal 2147483647 (bvchop 31 x))))
;;   :hints (("Goal" :in-theory (enable bvlt))))

;delete
;gen!
;use polarities!
;; (defthm bvlt-of-511
;;   (equal (bvlt 9 x 511)
;;          (not (equal 511 (bvchop 9 x))))
;;   :hints (("Goal"
;;            :cases ((natp size))
;;            :in-theory (e/d (bvlt)
;;                            ()))))

;delete
;; ;use polarity?
;; ;gen!
;; (defthm bvlt-32-max
;;   (implies (equal k (+ -1 (expt 2 32)))
;;            (equal (bvlt 32 x k)
;;                   (not (equal (bvchop 32 x) k))))
;;   :hints (("Goal" :in-theory (enable bvlt))))


;; x<free and free<=y imply x<y
(defthmd bvlt-transitive-core-1
  (implies (and (bvlt size x free)
                (not (bvlt size y free)))
           (equal (bvlt size x y)
                  t))
  :hints (("Goal" :in-theory (enable bvlt))))

;; x<=free and free<y imply x<y
(defthmd bvlt-transitive-core-2
  (implies (and (not (bvlt size free x))
                (bvlt size free y))
           (equal (bvlt size x y)
                  t))
  :hints (("Goal" :in-theory (enable bvlt))))

;fixme what about rules to turn a bvlt into nil?
(defthm bvlt-transitive-1-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size y free))
                (syntaxp (quotep free))
                (bvlt size k free))
           (equal (bvlt size k y)
                  t))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-1))))

(defthm bvlt-transitive-2-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (bvlt size free y)
                (syntaxp (quotep free))
                (not (bvlt size free k)))
           (equal (bvlt size k y)
                  t))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-2))))

(defthm bvlt-transitive-1-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (bvlt size x free)
                (syntaxp (quotep free))
                (not (bvlt size k free)))
           (equal (bvlt size x k)
                  t))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-1))))

(defthm bvlt-transitive-2-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size free x))
                (syntaxp (quotep free))
                (bvlt size free k))
           (equal (bvlt size x k)
                  t))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-2))))

;fixme make a version with a strict < as a hyp (can then weaken the other hyp by 1? what about overflow?)
;;y<=free and free<=x imply y<=x
(defthmd bvlt-transitive-core-3
  (implies (and (not (bvlt size free y))
                (not (bvlt size x free)))
           (not (bvlt size x y)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-transitive-3-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size free y))
                (syntaxp (quotep free))
                (not (bvlt size k free)))
           (not (bvlt size k y)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-transitive-3-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size x free))
                (syntaxp (quotep free))
                (not (bvlt size free k)))
           (not (bvlt size x k)))
  :hints (("Goal" :in-theory (enable bvlt))))

;;y<free and free-1<=x imply y<=x
(defthmd bvlt-transitive-core-4
  (implies (and (bvlt size y free)
                (not (bvlt size x (+ -1 free)))
                (integerp free)
                (natp size)
		)
           (not (bvlt size x y)))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases))))

(defthm bvlt-transitive-4-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (bvlt size y free)
                (syntaxp (quotep free))
                (not (bvlt size k (+ -1 free))) ;gets computed (what if free=0?  well, (bvlt size y free) above should not hold)
                (integerp free)
                (natp size))
           (not (bvlt size k y)))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-4))))

(defthm bvlt-transitive-4-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size x free))
                (syntaxp (quotep free))
                (bvle size k free) ;gets computed
                (integerp free)
                (natp size)
		)
           (not (bvlt size x k)))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases)  :use (:instance bvlt-transitive-core-4 (free (+ 1 free)) (y k)))))

;y<=free+1 and free<x imply y<=x
(defthmd bvlt-transitive-core-5
  (implies (and (not (bvlt size (+ 1 free) y))
                (bvlt size free x)
                (integerp free)
                (natp size))
           (not (bvlt size x y)))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases))))

(defthm bvlt-transitive-5-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (bvlt size free y))
                (syntaxp (quotep free))
                ;(bvlt size (+ -1 free) k) ;gets computed
                (bvle size free k) ;gets computed
                (integerp free)
                (natp size))
           (not (bvlt size k y)))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases)
           :use (:instance bvlt-transitive-core-5 (x k) (free (+ -1 free))))))

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
;;            (equal (bvlt size y x)
;;                   t))
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
                (equal k (+ -2 (expt 2 size)))
                (posp size)) ;gets computed
           (equal (bvlt size k x)
                  (equal (+ -1 (expt 2 size)) (bvchop size x)))))

;delete
;; ;todo: gen!
;; (defthm bvlt-2-max
;;   (equal (bvlt 2 2 x)
;;          (equal 3 (bvchop 2 x)))
;;   :hints (("Goal" :in-theory (enable bvlt))))

;can be expensive.  needs polarities
(defthmd bvlt-when-bvlt-must-be
  (implies (not (bvlt size y x))
           (equal (bvlt size x y)
                  (not (equal (bvchop size y) (bvchop size x)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-when-bvlt-must-be-fake-free
  (implies (and (not (bvlt free y x)) ;this free var is because the dag rewriter and dag prover dont support backchain limits
                (equal free size))
           (equal (bvlt size x y)
                  (not (equal (bvchop size y)
                              (bvchop size x)))))
  :hints (("Goal" :use (:instance bvlt-when-bvlt-must-be))))

;induction proof?
;wont match?
(defthm bvlt-of-max-when-bvlt
  (implies (bvlt size x free)
           (equal (bvlt size x (+ -1 (expt 2 size)))
                  t))
  :hints (("Goal" :use (:instance bvlt-transitive-core-1 (free free) (y (+ -1 (expt 2 size))))
           :in-theory (e/d (zp)
                           (;BVLT-OF-PLUS-ARG2
                            bvlt-transitive-1-a
                            bvlt-transitive-2-a
                            bvlt-transitive-1-b
                            bvlt-transitive-2-b
                            ;;BVLT-TRANSITIVE-FREE-BACK
                            ;;BVLT-TRANSITIVE-FREE2-BACK
                            )))))

;rename
(defthm bvlt-when-not-posp
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
(defthmd <-becomes-bvlt-alt
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p free x)
                (integerp k))
           (equal (< x k)
                  (if (unsigned-byte-p free k)
                      (bvlt free x k)
                    (not (< k 0)))))
  :hints (("Goal" :in-theory (enable bvlt unsigned-byte-p))))

;disabled during library proofs
;could this be expensive?
(defthmd <-becomes-bvlt-free
  (implies (and (unsigned-byte-p free x)
                (unsigned-byte-p free k))
           (equal (< x k)
                  (bvlt free x k)))
  :hints (("Goal" :use (:instance <-becomes-bvlt-alt)
           :in-theory (disable <-becomes-bvlt-alt))))

;could this be expensive?
;disabled during library proofs
(defthmd <-becomes-bvlt-free-alt
  (implies (and (unsigned-byte-p free k)
                (unsigned-byte-p free x))
           (equal (< x k)
                  (bvlt free x k)))
  :hints (("Goal" :use (:instance <-becomes-bvlt-alt)
           :in-theory (disable <-becomes-bvlt-alt))))

(theory-invariant (incompatible (:definition bvlt) (:rewrite <-becomes-bvlt)))
(theory-invariant (incompatible (:definition bvlt) (:rewrite <-becomes-bvlt-alt)))
(theory-invariant (incompatible (:definition bvlt) (:rewrite <-becomes-bvlt-free)))
(theory-invariant (incompatible (:definition bvlt) (:rewrite <-becomes-bvlt-free-alt)))

;fixme
(defthm bvlt-transitive-free2-back
  (implies (and (not (bvlt size free y))
                (bvle size free2 x)
                (equal free free2) ;hack?
                )
           (not (bvlt size x y)))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-BECOMES-BVLT-FREE <-BECOMES-BVLT <-BECOMES-BVLT-alt)))))

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

(defthm equal-of-constant-when-bvlt-constant-1
  (implies (and (syntaxp (quotep const))
                (bvlt freesize free x)
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                (bvle freesize const free))
           (not (equal const x))))

(defthm equal-of-constant-when-bvlt-constant-2
  (implies (and (syntaxp (quotep const))
                (bvlt freesize x free)
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                (bvle freesize free const))
           (not (equal const x))))

(defthm equal-of-constant-when-not-bvlt-constant-1
  (implies (and (syntaxp (quotep const))
                (not (bvlt freesize x free))
                (syntaxp (quotep freesize))
                (syntaxp (quotep free))
                (bvlt freesize const free))
           (not (equal const x))))

(defthm equal-of-constant-when-not-bvlt-constant-2
  (implies (and (syntaxp (quotep const))
                (not (bvlt freesize free x))
                (syntaxp (quotep freesize))
                (syntaxp (quotep free))
                (bvlt freesize free const))
           (not (equal const x))))

; can we drop the -alt rules?

(defthm equal-of-constant-when-bvlt-constant-1-alt
  (implies (and (syntaxp (quotep const))
                (bvlt freesize free x)
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                (bvle freesize const free))
           (not (equal x const))))

(defthm equal-of-constant-when-bvlt-constant-2-alt
  (implies (and (syntaxp (quotep const))
                (bvlt freesize x free)
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                (bvle freesize free const))
           (not (equal x const))))

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

(defthm bvlt-of-bvchop-arg3-same
  (equal (bvlt size x (bvchop size y))
         (bvlt size x y))
  :hints (("Goal" :cases ((natp size)))))

(defthm bvlt-of-bvchop-arg2-same
  (equal (bvlt size (bvchop size x) y)
         (bvlt size x y))
  :hints (("Goal" :cases ((natp size)))))



;fixme compare these to the transitive rules
;fixme more like these?
(defthm bvlt-when-bvlt-wider
  (implies (and (syntaxp (quotep k))
                (bvlt bigsize x free)
                (syntaxp (quotep free))
                (<= size bigsize)
                (unsigned-byte-p size free)
                (bvle size free k)
                (natp bigsize)
                (natp size))
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
                (natp bigsize)
                (natp size))
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
                (natp bigsize)
                (natp size))
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
;;            (equal (bvlt size x k)
;;                   nil))
;;   :hints (("Goal"
;;            :use (:instance <-of-bvchop-and-bvchop-same (s2 bigsize) (s1 size))
;;            :in-theory (e/d (bvlt) (<-of-bvchop-and-bvchop-same)))))

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

(defthm bvlt-of-bvplus-constant-and-constant-other
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep size)))
                (bvle size k2 k) ;this case
                (natp size)
                (natp k))
           (equal (bvlt size (bvplus size k2 x) k)
                  (or (bvlt size (bvminus size (+ -1) k2) x)
                      (bvlt size x (bvminus size k k2)))))
  :hints (("Goal" :in-theory (enable bvplus bvlt bvchop-of-sum-cases bvminus))))

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
     :in-theory
     (e/d (bvlt bvchop-of-sum-cases)
          (<-becomes-bvlt <-becomes-bvlt-alt)))))

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
