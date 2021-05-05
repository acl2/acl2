; Signed bit-vector "less than" comparison
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "logext") ;todo: include less?
(include-book "kestrel/booleans/boolor" :dir :system) ;todo
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;drop?
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;;signed less-than
(defund sbvlt (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (< (logext n x)
     (logext n y)))

;;signed less-than-or-equal
(defun sbvle (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (not (sbvlt n y x)))

;;signed greater-than
(defun sbvgt (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (sbvlt n y x))

;;signed greater-than-or-equal
(defun sbvge (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (not (sbvlt n x y)))

(defthm not-sbvlt-same
  (not (sbvlt size x x))
  :hints (("Goal" :in-theory (enable sbvlt))))

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
                (sbvlt size k free))
           (sbvlt size k y))
  :hints (("Goal" :in-theory (enable sbvlt-transitive-core-1))))

(defthm sbvlt-transitive-2-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (sbvlt size free y)
                (syntaxp (quotep free))
                (not (sbvlt size free k)))
           (sbvlt size k y))
  :hints (("Goal" :in-theory (enable sbvlt-transitive-core-2))))

(defthm sbvlt-transitive-1-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (sbvlt size x free)
                (syntaxp (quotep free))
                (not (sbvlt size k free)))
           (sbvlt size x k))
  :hints (("Goal" :in-theory (enable sbvlt-transitive-core-1))))

(defthm sbvlt-transitive-2-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (sbvlt size free x))
                (syntaxp (quotep free))
                (sbvlt size free k))
           (sbvlt size x k))
  :hints (("Goal" :in-theory (enable sbvlt))))


;fixme make a version with a strict < as a hyp (can then weaken the other hyp by 1? what about overflow?)
;;y<=free and free<=x imply y<=x
(defthmd sbvlt-transitive-core-3
  (implies (and (not (sbvlt size free y))
                (not (sbvlt size x free)))
           (equal (sbvlt size x y)
                  nil))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-transitive-3-a
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (sbvlt size free y))
                (syntaxp (quotep free))
                (not (sbvlt size k free)))
           (equal (sbvlt size k y)
                  nil))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-transitive-3-b
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (sbvlt size x free))
                (syntaxp (quotep free))
                (not (sbvlt size free k)))
           (equal (sbvlt size x k)
                  nil))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm boolor-of-sbvlt-of-constant-and-sbvlt-of-constant
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (sbvlt size x k1)
                          (sbvlt size x k2))
                  (if (sbvle size k1 k2) ;gets computed
                      (sbvlt size x k2)
                    (sbvlt size x k1))))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-2
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (sbvlt size k1 x)
                          (sbvlt size k2 x))
                  (if (sbvle size k2 k1) ;gets computed
                      (sbvlt size k2 x)
                    (sbvlt size k1 x))))
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

;fffixme more like this (> instead of <, not a negated sbvlt, bvlt instead of sbvlt)
(defthm equal-constant-when-not-sbvlt
  (implies (and (syntaxp (quotep k))
                (not (sbvlt freesize x free))
                (syntaxp (and (quotep free)
                              (quotep freesize)))
                (sbvlt freesize k free))
           (equal (equal k x)
                  nil)))

;; Rewrite sbvlt to < when possible
(defthmd sbvlt-becomes-<
  (implies (and (< x (expt 2 (+ -1 n)))
                (< y (expt 2 (+ -1 n)))
                (posp n)
                (natp x)
                (natp y))
           (equal (sbvlt n x y)
                  (< x y)))
  :hints (("Goal" :in-theory (enable sbvlt bvchop-identity))))

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
  (implies (and (syntaxp (quote k2))
                (unsigned-byte-p 31 k2) ;gets computed
                (<= x k) ;k is a free var
                (syntaxp (quote k))
                (unsigned-byte-p 31 k) ;gets computed
                (<= k k2) ;gets computed
                (natp x))
           (not (sbvlt 32 k2 x)))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-of-+-expt-arg1
  (implies (and (integerp x)
                (posp size))
           (equal (sbvlt size (+ x (expt 2 size)) y)
                  (sbvlt size x y)))
  :hints (("Goal" :in-theory (e/d (sbvlt) (expt)))))

(defthm sbvlt-of-+-expt-arg2
  (implies (and (integerp y)
                (posp size))
           (equal (sbvlt size x (+ y (expt 2 size)))
                  (sbvlt size x y)))
  :hints (("Goal" :in-theory (e/d (sbvlt) (expt)))))

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
