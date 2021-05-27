; Taking the or of two bits
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvor")

(defund bitor (x y)
  (declare (type integer x)
           (type integer y)
           (xargs :type-prescription (bitp (bitor x y))))
  (bvor 1 x y))

(defthm integerp-of-bitor
  (integerp (bitor x y)))

(defthm natp-of-bitor
  (natp (bitor x y))
  :hints (("Goal" :in-theory (enable bitor))))

;bozo enable?
(defthmd bvor-1-becomes-bitor
  (equal (bvor 1 x y)
         (bitor x y))
  :hints (("Goal" :in-theory (enable bitor))))

(theory-invariant (incompatible (:rewrite bvor-1-becomes-bitor) (:definition bitor)))

(defthm bitor-associative
  (equal (bitor (bitor x y) z)
         (bitor x (bitor y z)))
  :hints (("Goal" :in-theory (enable bitor))))

(defthm bitor-commutative
  (equal (bitor x y)
         (bitor y x))
  :hints (("Goal" :in-theory (e/d (bitor) (bvor-1-becomes-bitor)))))

(defthmd bitor-commutative-2
  (equal (bitor y (bitor x z))
         (bitor x (bitor y z)))
  :hints (("Goal" :in-theory (enable bitor bvor-commutative-2))))

;drop once we commute
(defthm bitor-of-1-arg2
  (equal (bitor x 1)
         1)
  :hints (("Goal"
           :cases ((equal 1 (bvchop 1 x))
                   (equal 0 (bvchop 1 x)))
           :in-theory (e/d (bvor bitor) (bvor-1-becomes-bitor)))))

(defthm bitor-of-1-arg1
  (equal (bitor 1 x)
         1)
  :hints (("Goal" :use (:instance bitor-of-1-arg2)
           :in-theory (disable bitor-of-1-arg2))))

(defthm bitor-of-0-arg1
  (equal (bitor 0 x)
         (getbit 0 x))
  :hints (("Goal" :in-theory (e/d (bvor bitor
                                        slice ;getbit ;bozo
                                        ) (bvor-1-becomes-bitor
                                           BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

;drop once we commute
(defthm bitor-of-0-arg2
  (equal (bitor x 0)
         (getbit 0 x)))

(defthm unsigned-byte-p-of-bitor
  (implies (posp size)
           (unsigned-byte-p size (bitor x y)))
  :hints
  (("Goal" :in-theory
    (e/d (bitor)
         (bvchop-1-becomes-getbit slice-becomes-getbit)))))

(defthmd bitor-combine-constants
  (implies (and (syntaxp (quotep y)) ;put this hyp first to fail faster
                (syntaxp (quotep x)))
           (equal (bitor x (bitor y z))
                  (bitor (bitor x y) z))))

(defthm bitor-of-getbit-arg1
  (equal (bitor (getbit 0 x) y)
         (bitor x y))
  :hints (("Goal" :in-theory (e/d (bitor) nil))))

(defthm bitor-of-getbit-arg2
  (equal (bitor y (getbit 0 x))
         (bitor y x))
  :hints (("Goal" :in-theory (e/d (bitor) nil))))

(defthm bitor-subst-arg1
  (implies (and (equal (getbit 0 x) free)
                (syntaxp (and (quotep free) (not (quotep x)))))
           (equal (bitor x y) (bitor free y))))

(defthm bitor-subst-arg2
  (implies (and (equal (getbit 0 x) free)
                (syntaxp (and (quotep free) (not (quotep x)))))
           (equal (bitor y x) (bitor y free))))

;justifies the correctness of some operations performed by Axe
(defthmd unsigned-byte-p-1-of-bitor
  (unsigned-byte-p 1 (bitor x y))
  :hints (("Goal" :in-theory (enable bitor))))

(defthm bvchop-of-bitor
  (implies (and (< 0 n)
                (natp n))
           (equal (bvchop n (bitor x y))
                  (bitor x y))))

(defthm getbit-of-bitor-all-cases
  (implies (natp n)
           (equal (getbit n (bitor x y))
                  (if (equal n 0)
                      (bitor x y)
                    0)))
  :hints (("Goal" :in-theory (enable bitor))))
