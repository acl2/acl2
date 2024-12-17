; Taking the or of two bits
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
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

;; This version requires bitp inputs and so may be faster and may also help
;; catch bugs via stricter guard obligations.  We intened to keep this enabled
;; for reasoning.
(defun bitor$ (x y)
  (declare (xargs :guard (and (bitp x) (bitp y))
                  :split-types t
                  :type-prescription (bitp (bitor$ x y)))
           (type bit x y))
  (mbe :logic (bitor x y)
       :exec (the bit (logior x y))))

(defthm bitp-of-bitor
  (bitp (bitor x y)))

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

(defthmd bitor-commute-constant
  (implies (syntaxp (quotep y))
           (equal (bitor x y)
                  (bitor y x)))
  :hints (("Goal" :use bitor-commutative
           :in-theory (disable bitor-commutative))))

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
  :hints (("Goal" :use bitor-of-1-arg2
           :in-theory (disable bitor-of-1-arg2))))

(defthm bitor-of-0-arg1
  (equal (bitor 0 x)
         (getbit 0 x))
  :hints (("Goal" :in-theory (e/d (bvor bitor
                                        slice ;getbit ;bozo
                                        ) (bvor-1-becomes-bitor
                                           )))))

;drop once we commute
(defthm bitor-of-0-arg2
  (equal (bitor x 0)
         (getbit 0 x)))

(defthm bitor-same
  (equal (bitor x x)
         (getbit 0 x))
  :hints (("Goal" :in-theory (enable bitor))))

(defthm bitor-same-2
  (equal (bitor x (bitor x y))
         (bitor x y))
  :hints (("Goal" :in-theory (enable bitor))))

(defthm unsigned-byte-p-of-bitor
  (implies (posp size)
           (unsigned-byte-p size (bitor x y)))
  :hints (("Goal" :in-theory (enable bitor))))

(defthmd bitor-combine-constants
  (implies (syntaxp (and (quotep y) ;put this hyp first to fail faster
                         (quotep x)))
           (equal (bitor x (bitor y z))
                  (bitor (bitor x y) z))))

(defthm bitor-of-constant-chop-arg1
  (implies (and (syntaxp (quotep x))
                (not (unsigned-byte-p 1 x)))
           (equal (bitor x y)
                  (bitor (getbit 0 x) y)))
  :hints (("Goal" :in-theory (enable bitor))))

(defthm bitor-of-constant-chop-arg2
  (implies (and (syntaxp (quotep y))
                (not (unsigned-byte-p 1 y)))
           (equal (bitor x y)
                  (bitor x (getbit 0 y))))
  :hints (("Goal" :in-theory (enable bitor))))

;todo: rename to have 0 in the name
(defthm bitor-of-getbit-arg1
  (equal (bitor (getbit 0 x) y)
         (bitor x y))
  :hints (("Goal" :in-theory (e/d (bitor) nil))))

;todo: rename to have 0 in the name
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

(defthm bitor-of-bvchop-arg1
  (implies (posp size)
           (equal (bitor (bvchop size x) y)
                  (bitor x y)))
  :hints (("Goal" :in-theory (enable bitor))))

(defthm bitor-of-bvchop-arg2
  (implies (posp size)
           (equal (bitor y (bvchop size x))
                  (bitor y x)))
  :hints (("Goal" :in-theory (enable bitor))))

(defthm equal-of-bitor-and-constant
  (implies (syntaxp (quotep k))
           (equal (equal (bitor x y) k)
                  (if (equal 0 k)
                      (and (equal 0 (getbit 0 x))
                           (equal 0 (getbit 0 y)))
                    (if (equal 1 k)
                        (if (equal 1 (getbit 0 x))
                            t
                          (equal 1 (getbit 0 y)))
                      nil)))))
