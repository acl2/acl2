; An analogue of mod for bit-vectors
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
(include-book "unsigned-byte-p")
(include-book "bvlt") ;hmmm
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;fixme what should this do if y is 0?
(defund bvmod (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (bvchop n y))))
           )
  (bvchop n (mod (bvchop n x) ;these two bvchops are new
                  (bvchop n y)
                  )))

(defthm integerp-of-bvmod
  (integerp (bvmod size x y)))

(defthm natp-of-bvmod
  (natp (bvmod size x y))
  :rule-classes :type-prescription)

(in-theory (disable (:t bvmod))) ;natp-of-bvmod is at least as good

(defthm bvmod-of-1
  (equal (bvmod size x 1)
         0)
  :hints (("Goal" :in-theory (enable bvmod))))

(defthm bvmod-of-0-arg1
  (equal (bvmod 0 x y)
         0)
  :hints (("Goal" :in-theory (enable bvmod))))

(defthm bvmod-of-0-arg2
  (equal (bvmod size 0 y)
         0)
  :hints (("Goal" :in-theory (enable bvmod))))

;do not remove.  this helps justify the translation to STP.
(defthm bvmod-of-0-arg3
  (equal (bvmod size x 0)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvmod))))

;gen
(defthm unsigned-byte-p-of-bvmod
  (equal (unsigned-byte-p size (bvmod size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvmod))))

(defthm unsigned-byte-p-of-bvmod-gen
  (implies (and (<= n m) (natp n)
                (natp m) ;(integerp m)
                )
           (unsigned-byte-p m (bvmod n x y)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvmod (size n))
           :in-theory (disable unsigned-byte-p-of-bvmod))))

(defthm bvchop-of-bvmod
  (implies (and (<= size1 size2)
                (natp size2)
                (natp size1))
           (equal (bvchop size2 (bvmod size1 x y))
                  (bvmod size1 x y)))
  :hints (("Goal" :in-theory (enable ;bvmod bvchop
                              ))))

;; (thm
;;  (implies (and (natp size2)
;;                (natp size1))
;;           (equal (bvchop size2 (bvmod size1 x y))
;;                  (if (<= size1 size2)
;;                      (bvmod size1 x y)
;;                    (bvmod size2 x y))))
;;  :hints (("Goal" :in-theory (enable ;bvmod bvchop
;;                              ))))

;do not remove (helps justify the translation to STP)
(defthm bvmod-of-bvchop-arg2
  (equal (bvmod size (bvchop size x) y)
         (bvmod size x y))
  :hints (("Goal" :in-theory (enable bvmod))))

;do not remove (helps justify the translation to STP)
(defthm bvmod-of-bvchop-arg3
  (equal (bvmod size x (bvchop size y))
         (bvmod size x y))
  :hints (("Goal" :in-theory (enable bvmod))))

(DEFTHM BVMOD-WHEN-BVCHOP-KNOWN-SUBST
  (IMPLIES (AND (EQUAL (BVCHOP SIZE X) FREE)
                (SYNTAXP (QUOTEP FREE))
                (NATP SIZE))
           (EQUAL (BVMOD SIZE Y X)
                  (BVMOD SIZE Y FREE)))
  :HINTS (("Goal" :IN-THEORY (ENABLE))))

(DEFTHM BVMOD-WHEN-BVCHOP-KNOWN-SUBST-alt
  (IMPLIES (AND (EQUAL (BVCHOP SIZE X) FREE)
                (SYNTAXP (QUOTEP FREE))
                (NATP SIZE))
           (EQUAL (BVMOD SIZE X Y)
                  (BVMOD SIZE FREE Y)))
  :HINTS (("Goal" :IN-THEORY (ENABLE))))


(defthm bvlt-of-bvmod-false-helper
  (implies (and (syntaxp (and (quotep j)
                              (quotep k)))
                (>= j (+ -1 k))
                (posp k)
                (natp size)
                (unsigned-byte-p size k)
                (unsigned-byte-p size2 j)
                (unsigned-byte-p size x))
           (equal (bvlt size2 j (bvmod size x k))
                  nil))
  :hints (("Goal" :in-theory (enable bvlt bvmod bvchop-of-sum-cases bvchop))))

(defthm bvlt-of-bvmod-false
  (implies (and (syntaxp (and (quotep j)
                              (quotep k)
                              (quotep size)
                              (quotep size2)))
                (>= (bvchop size2 j) (+ -1 (bvchop size k)))
                (posp (bvchop size k)) ;weird?
                (natp size))
           (equal (bvlt size2 j (bvmod size x k))
                  nil))
  :hints (("Goal" :use (:instance bvlt-of-bvmod-false-helper
                                  (k (bvchop size k))
                                  (x (bvchop size x))
                                  (j (bvchop size2 j)))
           :cases ((equal 0 (bvchop size k)))
           :in-theory (e/d (bvlt) (bvlt-of-bvmod-false-helper)))))

(defthm bvmod-self
  (equal (bvmod size x x)
         0)
  :hints (("Goal" :in-theory (enable bvmod))))

;move
;rename?
(defthm unsigned-byte-p-of-mod2
  (implies (and (unsigned-byte-p size y)
                (unsigned-byte-p size x))
           (unsigned-byte-p size (mod x y)))
  :hints (("Goal" :cases ((equal 0 y))
           :in-theory (enable unsigned-byte-p))))

(defthmd mod-becomes-bvmod-core
  (implies (and (unsigned-byte-p size y)
                (unsigned-byte-p size x))
           (equal (mod x y)
                  (bvmod size x y)))
  :hints (("Goal" :in-theory (enable bvmod))))

(defthm bvmod-of-1-arg1
  (implies (posp size)
           (equal (bvmod size 1 x)
                  (if (equal (bvchop size x) 1)
                      0
                    1)))
  :hints (("Goal" :in-theory (enable bvmod))))


(defthm bvmod-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvmod size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvmod))))

(defthm equal-of-mod-and-bvmod
  (implies (and (unsigned-byte-p size x)
                (unsigned-byte-p size y))
           (equal (equal (mod x y) (bvmod size x y))
                  t))
  :hints (("Goal" :in-theory (enable bvmod))))

(defthm equal-of-bvmod-and-mod
  (implies (and (unsigned-byte-p size x)
                (unsigned-byte-p size y))
           (equal (equal (bvmod size x y) (mod x y))
                  t))
  :hints (("Goal" :in-theory (enable bvmod))))
