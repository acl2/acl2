; Taking the and of two bits
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvand")
(include-book "getbit")

(defund bitand (x y)
  (declare (type integer x)
           (type integer y)
           (xargs :type-prescription (bitp (bitand x y))))
  (bvand 1 x y))

(defthm bitand-associative
  (equal (bitand (bitand x y) z)
         (bitand x (bitand y z)))
  :hints (("Goal" :in-theory (enable bitand))))

(defthm bitand-commutative
  (equal (bitand x y)
         (bitand y x))
  :hints (("Goal" :in-theory (enable bitand))))

(defthmd bitand-commutative-2
  (equal (bitand x (bitand y z))
         (bitand y (bitand x z)))
  :hints (("Goal"
;           :use (:instance bvxor-commutative-2 (y x) (x y) (z z))
           :in-theory (enable bitand))))

(defthmd bitand-commute-constant
  (implies (syntaxp (quotep y))
           (equal (bitand x y)
                  (bitand y x)))
  :hints (("Goal" :use (:instance bitand-commutative)
           :in-theory (disable bitand-commutative))))

(defthm bitand-of-0-arg1
  (equal (bitand 0 x)
         0)
  :hints (("Goal" :in-theory (enable bitand))))

(defthm bitand-of-0-arg2
  (equal (bitand x 0)
         0)
  :hints (("Goal" :in-theory (enable bitand))))

(defthm bitand-of-1-arg2
  (equal (bitand x 1)
         (getbit 0 x))
  :hints (("Goal" :in-theory (enable bvand bitand))))

(defthm bitand-of-1-arg1
  (equal (bitand 1 x)
         (getbit 0 x))
  :hints (("Goal" :use (:instance bitand-of-1-arg2)
           :in-theory (disable bitand-of-1-arg2))))

(defthm bitand-same
  (equal (bitand x x)
         (getbit 0 x))
  :hints (("Goal" :in-theory (enable bitand))))

(defthm bitand-same-2
  (equal (bitand x (bitand x y))
         (bitand x y))
  :hints (("Goal" :in-theory (enable bitand))))

(defthm integerp-of-bitand
  (integerp (bitand x y)))

(defthm natp-of-bitand
  (natp (bitand x y))
  :hints (("Goal" :in-theory (enable bitand))))

;todo: rename to have 0 in the name
(defthm bvand-1-of-getbit-arg2
  (equal (bvand 1 x (getbit 0 y))
         (bvand 1 x y))
  :hints (("Goal" :in-theory (enable bvand))))

;todo: rename to have 0 in the name
(defthm bvand-1-of-getbit-arg1
  (equal (bvand 1 (getbit 0 x) y)
         (bvand 1 x y))
  :hints (("Goal" :in-theory (enable bvand))))

;use trim?
(defthm bitand-when-constant-is-not-usb-arg2
  (implies (not (unsigned-byte-p 1 k))
           (equal (bitand x k)
                  (bitand x (getbit 0 k))))
  :hints (("Goal" :in-theory (enable bitand))))

;use trim?
(defthm bitand-when-constant-is-not-usb-arg1
  (implies (not (unsigned-byte-p 1 k))
           (equal (bitand k x)
                  (bitand (getbit 0 k) x)))
  :hints (("Goal" :in-theory (enable bitand))))

;leave this last
;bozo enable?
(defthmd bvand-1-becomes-bitand
  (equal (bvand 1 x y)
         (bitand x y))
  :hints (("Goal" :in-theory (enable bitand))))

(theory-invariant (incompatible (:rewrite bvand-1-becomes-bitand) (:definition bitand)))

(defthmd bitand-combine-constants
  (implies (syntaxp (and (quotep y) ;put this hyp first to fail faster
                         (quotep x)))
           (equal (bitand x (bitand y z))
                  (bitand (bitand x y) z))))

(defthm bitand-of-constant-chop-arg1
  (implies (and (syntaxp (quotep x))
                (not (unsigned-byte-p 1 x)))
           (equal (bitand x y)
                  (bitand (getbit 0 x) y)))
  :hints (("Goal" :in-theory (enable bitand))))

(defthm bitand-of-constant-chop-arg2
  (implies (and (syntaxp (quotep y))
                (not (unsigned-byte-p 1 y)))
           (equal (bitand x y)
                  (bitand x (getbit 0 y))))
  :hints (("Goal" :in-theory (enable bitand))))

;todo: rename to have 0 in the name
(defthm bitand-of-getbit-arg1
  (equal (bitand (getbit 0 x) y)
         (bitand x y))
  :hints (("Goal" :in-theory (e/d (bitand) nil))))

;todo: rename to have 0 in the name
(defthm bitand-of-getbit-arg2
  (equal (bitand y (getbit 0 x))
         (bitand y x))
  :hints (("Goal" :in-theory (e/d (bitand) nil))))

(defthm bitand-of-bvchop-arg1
  (implies (posp size)
           (equal (bitand (bvchop size x) y)
                  (bitand x y)))
  :hints (("Goal" :in-theory (enable bitand))))

(defthm bitand-of-bvchop-arg2
  (implies (posp size)
           (equal (bitand y (bvchop size x))
                  (bitand y x)))
  :hints (("Goal" :in-theory (enable bitand))))

(defthm bitand-subst-arg1
  (implies (and (equal (getbit 0 x) free)
                (syntaxp (and (quotep free) (not (quotep x)))))
           (equal (bitand x y) (bitand free y))))

(defthm bitand-subst-arg2
  (implies (and (equal (getbit 0 x) free)
                (syntaxp (and (quotep free) (not (quotep x)))))
           (equal (bitand y x) (bitand y free))))


;justifies the correctness of some operations performed by Axe
(defthmd unsigned-byte-p-1-of-bitand
  (unsigned-byte-p 1 (bitand x y))
  :hints (("Goal" :in-theory (enable bitand))))

(defthm unsigned-byte-p-of-bitand
  (implies (posp size)
           (unsigned-byte-p size (bitand x y)))
  :hints (("Goal" :in-theory (e/d (bitand) nil))))

(defthm bvchop-of-bitand
  (implies (and (< 0 n)
                (natp n))
           (equal (bvchop n (bitand x y))
                  (bitand x y))))

(defthmd bitand-cases
  (equal (acl2::bitand x y)
         (if (and (equal (bvchop 1 x) 1)
                  (equal (bvchop 1 y) 1))
             1
           0)))
