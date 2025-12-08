; Arithmetic negation of a bit-vector
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
(include-book "bvchop")
(include-book "getbit-def")
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system) ; for call-of, etc.
(local (include-book "slice"))
(local (include-book "bvplus"))
(local (include-book "unsigned-byte-p"))
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

(defthm bvuminus-upper-bound-linear-strong
  (implies (natp size)
           (<= (bvuminus size x) (+ -1 (expt 2 size))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable bvuminus))))

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

(defthm equal-of-constant-and-bvuminus
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (natp size))
           (equal (equal k (bvuminus size x))
                  (and (unsigned-byte-p size k)
                       (equal (bvuminus size k) (bvchop size x)))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p bvchop-of-sum-cases bvuminus))))

;; Flipped LHS.  Only needed by Axe?
(defthmd equal-of-bvuminus-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (natp size))
           (equal (equal (bvuminus size x) k)
                  (and (unsigned-byte-p size k)
                       (equal (bvuminus size k) (bvchop size x)))))
  :hints (("Goal" :use equal-of-constant-and-bvuminus
           :in-theory (disable equal-of-constant-and-bvuminus))))

;0 is special, because its negation is always the same number (0 itself)
;no syntaxp hyp for size
(defthm equal-of-0-and-bvuminus
  (equal (equal 0 (bvuminus size x))
         (equal 0 (bvchop size x)))
  :hints (("Goal" :in-theory (enable bvuminus)
           :use (:instance equal-of-bvuminus-and-constant (k 0)))))

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
  :hints (("Goal" :in-theory (enable bvuminus))))

(defthm bvuminus-of-bvchop-arg2-same
  (equal (bvuminus size (bvchop size x))
         (bvuminus size x))
  :hints (("Goal" :in-theory (enable bvuminus))))

(defthm bvplus-of-bvuminus-same
  (equal (bvplus size (bvuminus size x) x)
         0)
  :hints (("Goal" :in-theory (enable bvplus bvuminus))))

(defthm bvplus-of-bvuminus-same-alt
  (equal (bvplus size x (bvuminus size x))
         0)
  :hints (("Goal" :use bvplus-of-bvuminus-same
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
  :hints (("Goal" :use bvplus-of-bvuminus-same-2
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
                           ()))))

;can loop
;restrict to constant width?
(defthmd bvuminus-of-1-arg2
  (implies (natp width)
           (equal (bvuminus width 1)
                  (- (expt 2 width) 1)))
  :hints (("Goal" :in-theory (enable bvuminus))))



(defthmd bvuminus-subst-smaller-term
  (implies (and (equal (bvchop size x)
                       (bvchop size y))
                (syntaxp (smaller-termp y x)))
           (equal (bvuminus size x)
                  (bvuminus size y)))
  :hints (("Goal" :in-theory (enable bvuminus))))

(defthmd bvuminus-of-+
  (implies (and (integerp x)
                (integerp y))
           (equal (bvuminus size (+ x y))
                  (bvuminus size (bvplus size x y))))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvuminus-of-ifix
  (equal (bvuminus size (ifix x))
         (bvuminus size x))
  :hints (("Goal" :in-theory (enable ifix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks whether y should come before x
(defun should-commute-bvplus-argsp (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (let ((x-core (if (and (call-of 'bvuminus x) ; (bvuminus <size> <x>)
                         (<= 2 (len (fargs x))))
                    (farg2 x)
                  x))
        (y-core (if (and (call-of 'bvuminus y) ; (bvuminus <size> <x>)
                         (<= 2 (len (fargs y))))
                    (farg2 y)
                  y)))
    (smaller-termp y-core x-core)))

(defthmd bvplus-commutative-smart
  (implies (syntaxp (should-commute-bvplus-argsp x y))
           (equal (bvplus size x y)
                  (bvplus size y x)))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthmd bvplus-commutative-2-smart
  (implies (syntaxp (should-commute-bvplus-argsp x y))
           (equal (bvplus size x (bvplus size y z))
                  (bvplus size y (bvplus size x z))))
  :rule-classes ((:rewrite :loop-stopper nil)))

;; todo: consider oncommenting this
;; ;; avoid loops with the smart rules below:
;; (in-theory (e/d (bvplus-commutative-smart
;;                  bvplus-commutative-2-smart)
;;                 (bvplus-commutative
;;                  bvplus-commutative-2))

;; Test that the smart commutative rules work:
(thm
 (equal (bvplus 32 x (bvplus 32 y (bvplus 32 z (bvuminus 32 x))))
        (bvplus 32 y z))
 :hints (("Goal" :in-theory (e/d (bvplus-commutative-smart
                                  bvplus-commutative-2-smart)
                                 (bvplus-commutative
                                  bvplus-commutative-2)))))

(defthm equal-of-bvplus-of-bvuminus-and-0
  (equal (equal (bvplus size (bvuminus size x) y) 0)
         (equal (bvchop size x) (bvchop size y)))
  :hints (("Goal" :in-theory (enable bvplus bvuminus bvchop-of-sum-cases))))

;; likely to loop
(defthmd equal-of-bvuminus
  (implies (natp size)
           (equal (equal (bvuminus size x) y)
                  (and (unsigned-byte-p size y)
                       (equal (bvchop size x) (bvuminus size y)))))
  :hints (("Goal" :in-theory (enable bvuminus))))

;; fairly aggressive
(defthmd equal-of-bvuminus-and-bvplus
  (implies (natp size)
           (equal (equal (bvuminus size x) (bvplus size y z))
                  (equal (bvchop size x) (bvplus size (bvuminus size y) (bvuminus size z)))))
  :hints (("Goal" :use (:instance equal-of-bvuminus (y (bvplus size y z))))))
