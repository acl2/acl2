; Rules that recognize xor constraints
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))

;; See also ../sparse/gadgets/xor.lisp

;; TODO: Move all these xor idioms to the prime-fields library.

;; TODO: Standardize these names
;; TODO: Disable these rules?
;; TODO: Perhaps add more rules (e.g., ones with (mul 2 (mul a b p) p)).
;; TODO: Perhaps drop rules that deal with terms not in normal form

;; The basic pattern for c=bitxor(a,b) is c = a + b - 2ab, where a and b are
;; bits and all the operations are done modulo the prime.

;; a+b-(a+a)b=c -> c=bitxor(a,b)
(defthm bitxor-constraint-intro
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal (add a (add b (neg (mul (add a a p) b p) p) p) p)
                         c)
                  (equal c (acl2::bitxor a b)))))

;; This version has the equality in the LHS flipped.
(defthm bitxor-constraint-intro-alt
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal c
                         (add a (add b (neg (mul (add a a p) b p) p) p) p))
                  (equal c (acl2::bitxor a b))))
  :hints (("Goal" :use (:instance bitxor-constraint-intro)
           :in-theory (disable bitxor-constraint-intro))))

;; Compared to bitxor-constraint-intro, this has the a and b swapped in the add.
(defthm bitxor-constraint-intro-b
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal (add b (add a (neg (mul (add a a p) b p) p) p) p)
                         c)
                  (equal c (acl2::bitxor a b)))))

;; This version has the equality in the LHS flipped.
(defthm bitxor-constraint-intro-b-alt
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal c
                         (add b (add a (neg (mul (add a a p) b p) p) p) p))
                  (equal c (acl2::bitxor a b)))))

;; (a+a)*b=a+b-c -> x=bitxor(a,b)
(defthm bitxor-constraint-intro-2
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal (mul (add a a p) b p)
                         (add a (add b (neg c p) p) p))
                  (equal (mod (ifix c) p) ; just c, if we known (fep c p)
                         (acl2::bitxor a b)))))

;; This version has the equality in the LHS flipped.
(defthm bitxor-constraint-intro-2-alt
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal (add a (add b (neg c p) p) p)
                         (mul (add a a p) b p))
                  (equal (mod (ifix c) p) ; just c, if we known (fep c p)
                         (acl2::bitxor a b)))))

;; Compared to bitxor-constraint-intro-2, this swaps a and b in the add.
(defthm bitxor-constraint-intro-2b
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal (mul (add a a p) b p)
                         (add b (add a (neg c p) p) p))
                  (equal (mod (ifix c) p) ; just c, if we known (fep c p)
                         (acl2::bitxor a b)))))

;; This version has the equality in the LHS flipped.
(defthm bitxor-constraint-intro-2b-alt
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal (add b (add a (neg c p) p) p)
                         (mul (add a a p) b p))
                  (equal (mod (ifix c) p) ; just c, if we known (fep c p)
                         (acl2::bitxor a b)))))

(defthm xor-idiom-1
  (implies (and (bitp x)
                (bitp y)
                (fep z p)
                (posp p)
                (< 2 p)
                (RTL::PRIMEP P))
           (equal (equal (mul '2 (mul x y p) p) (add x (add y (mul '-1 z p) p) p))
                  (equal z (acl2::bitxor x y)))))

(defthm xor-idiom-2
  (implies (and (bitp x)
                (bitp y)
                (fep z p)
                (posp p)
                (< 2 p)
                (RTL::PRIMEP P))
           (equal (equal (mul '2 (mul x y p) p) (add y (add x (mul '-1 z p) p) p))
                  (equal z (acl2::bitxor x y))))
  :hints (("Goal" :use (:instance xor-idiom-1)
           :in-theory (disable xor-idiom-1))))

(defthm xor-idiom-3
  (implies (and (bitp x)
                (bitp y)
                (< 2 p)
                (rtl::primep p))
           (equal (add x (add y (mul '-2 (mul x y p) p) p) p)
                  (acl2::bitxor x y))))

;not needed if term is commuted right?
(defthm xor-idiom-3-alt
  (implies (and (bitp x)
                (bitp y)
                (< 2 p)
                (rtl::primep p))
           (equal (add x (add y (mul '-2 (mul y x p) p) p) p)
                  (acl2::bitxor x y))))

(defthm xor-idiom-4
  (implies (and (bitp x)
                (bitp y)
                (< 2 p)
                (rtl::primep p))
           (equal (add (mul '-2 (mul x y p) p) (add x y p) p)
                  (acl2::bitxor x y))))

(defthm xor-idiom-4-alt
  (implies (and (bitp x)
                (bitp y)
                (< 2 p)
                (rtl::primep p))
           (equal (add (mul '-2 (mul x y p) p) (add y x p) p)
                  (acl2::bitxor x y))))
