; BV Library: bitxor
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvxor")

(defund bitxor (x y)
  (declare (type integer x)
           (type integer y))
  (bvxor 1 x y))

(in-theory (disable (:type-prescription bitxor))) ;; bitxor-type is better

(defthm bitxor-associative
  (equal (bitxor (bitxor x y) z)
         (bitxor x (bitxor y z)))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthmd bitxor-commutative
  (equal (bitxor x y)
         (bitxor y x))
  :hints (("Goal" :in-theory (enable bitxor bvxor-commutative))))

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
  :hints (("Goal" :use (:instance bitxor-commutative)
           :in-theory (disable bitxor-commutative))))

(defthmd bitxor-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)))
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

;use trim?
(defthm bitxor-when-constant-is-not-usb-arg2
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 1 k)))
           (equal (bitxor x k)
                  (bitxor x (getbit 0 k))))
  :hints (("Goal" :in-theory (enable bitxor))))

;use trim?
(defthm bitxor-when-constant-is-not-usb-arg1
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 1 k)))
           (equal (bitxor k x)
                  (bitxor (getbit 0 k) x)))
  :hints (("Goal" :in-theory (enable bitxor))))

;justifies the correctness of some operations performed by Axe
(defthmd unsigned-byte-p-1-of-bitxor
  (unsigned-byte-p 1 (bitxor x y))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthm bitxor-type
  (or (equal 0 (bitxor x y))
      (equal 1 (bitxor x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :use (:instance unsigned-byte-p-1-of-bitxor)
           :in-theory (disable unsigned-byte-p-1-of-bitxor))))

(defthm unsigned-byte-p-of-bitxor
  (implies (posp size)
           (unsigned-byte-p size (bitxor x y)))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthm bitxor-of-getbit-arg2
  (equal (bitxor y (getbit 0 x))
         (bitxor y x))
  :hints (("Goal" :in-theory (enable bitxor))))

(defthm bitxor-of-getbit-arg1
  (equal (bitxor (getbit 0 x) y)
         (bitxor x y))
  :hints (("Goal" :in-theory (enable bitxor-commutative))))

(defthm bitxor-when-x-is-not-an-integer
  (implies (not (integerp x))
           (equal (bitxor x y)
                  (getbit 0 y)))
  :hints (("Goal" :in-theory (enable bitxor bvxor-when-x-is-not-an-integer))))

(defthm bitxor-when-y-is-not-an-integer
  (implies (not (integerp y))
           (equal (bitxor x y)
                  (getbit 0 x)))
  :hints (("Goal" :in-theory (enable bitxor bvxor-when-y-is-not-an-integer))))

(defthmd bitxor-split
  (equal (bitxor x y)
         (if (equal 1 (getbit 0 y))
             (if (equal 1 (getbit 0 x))
                 0
               1)
           (if (equal 1 (getbit 0 x))
                 1
             0)))
  :hints (("Goal" :in-theory (enable bitxor bvxor))))

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
                  t))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bitxor (size 1))
           :in-theory (disable unsigned-byte-p-of-bitxor))))

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
  :hints (("Goal" :in-theory (e/d (bitxor) (bvxor-1-becomes-bitxor)))))

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
           (equal (acl2::bitxor bit1 (* 2 bit2))
                  (acl2::bitxor bit1 0)))
  :hints (("Goal" :in-theory (e/d (acl2::bitxor acl2::bvxor getbit)
                                  (acl2::bvxor-1-becomes-bitxor bvchop-1-becomes-getbit slice-becomes-getbit)))))

(defthm equal-of-0-and-bitxor
  (equal (equal 0 (bitxor x y))
         (equal (getbit 0 x)
                (getbit 0 y)))
  :hints (("Goal"
           :cases ((equal 0 (getbit 0 x))
                   (equal 1 (getbit 0 x)))
           :in-theory (enable))))

(defthm equal-of-bitxor-same
  (equal (equal x (bitxor x y))
         (and (unsigned-byte-p 1 x)
              (equal 0 (getbit 0 y))))
  :hints (("Goal" :cases ((equal 0 (getbit 0 x))))))

(defthm equal-of-bitxor-same-alt
  (equal (equal x (bitxor y x))
         (and (unsigned-byte-p 1 x)
              (equal 0 (getbit 0 y))))
  :hints (("Goal" :use (:instance equal-of-bitxor-same)
           :in-theory (e/d (bitxor-commutative) (equal-of-bitxor-same)))))
