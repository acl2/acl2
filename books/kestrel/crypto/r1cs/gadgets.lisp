; R1CS gadgets
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; This book defines and verifies a variety of snark "gadgets" -- ways to check
;; various constraints using only operations from the prime field (addition,
;; subtraction, and multiplication).  This version of the file passes the prime
;; explicitly to the operations, but see also gadgets-alt.lisp.

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;
;; Bit constraint (a constraint that ensures that a value is a bit: 0 or 1)
;;

;; bits are in the field
(defthm bitp-in-field
  (implies (and (bitp x)
                (rtl::primep prime))
           (fep x prime))
  :hints (("Goal" :in-theory (enable fep bitp))))

;;
;; nonzero constraint
;;

;;todo: add guard
;; True iff a is not zero.
(defun-sk nonzero-constraint (a prime)
  (exists inv (and (fep inv prime)
                   (equal (mul inv a prime) 1))))

(defthm nonzero-constraint-correct-1
  (implies (and (fep a prime)
                (rtl::primep prime))
           (implies (nonzero-constraint a prime)
                    (not (equal a 0)))))

(defthm nonzero-constraint-correct-2
  (implies (and (fep a prime)
                (rtl::primep prime))
           (implies (not (equal a 0))
                    (nonzero-constraint a prime)))
  :hints (("Goal" :use (:instance nonzero-constraint-suff
                                  (inv (inv a prime))))))

(defthm nonzero-constraint-correct
  (implies (and (fep a prime)
                (rtl::primep prime))
           (iff (nonzero-constraint a prime)
                (not (equal a 0))))
  :hints (("Goal" :use (nonzero-constraint-correct-1
                        nonzero-constraint-correct-2)
           :in-theory (disable nonzero-constraint-correct-1
                               nonzero-constraint-correct-2))))

;; TODO: How to do y = (if x!=0 then 1 else 0)?  Say that y is a bit and there is some z such that y=x*z.

;;
;; Exclusive-or constraint
;;

;; c = a+b-2ab becomes c=bitxor(a,b)
(defun xor-constraint (a b c prime)
  (declare (xargs :guard (and (rtl::primep prime)
                              ;; (fep a prime)
                              (bitp a)
                              ;; (fep b prime)
                              (bitp b)
                              (fep c prime)
                              (not (equal 2 prime)) ;ensures that the 2 below is a field element
                              )))
  (equal (mul (mul 2 a prime) b prime)
         (add a (sub b c prime) prime)))

(defthm xor-constraint-correct
  (implies (and ;; (fep a prime)
                (bitp a)
                ;; (fep b prime)
                (bitp b)
                (fep c prime)
                (not (equal 2 prime))
                (rtl::primep prime))
           (iff (xor-constraint a b c prime)
                (equal c (acl2::bitxor a b))))
  :hints (("Goal" :in-theory (e/d (bitp)
                                  (;ADD-ASSOCIATIVE ;todo: looped
                                   ;;ADD-OF-SUB-ARG2 ;todo: looped
                                   )))))

;; a+b-(a+a)b=c -> c=bitxor(a,b)
(defthm bitxor-constraint-intro
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal (add a (add b (neg (mul (add a a p) b p) p) p) p)
                         c)
                  (equal c (acl2::bitxor a b))))
  :hints (("Goal" :use (:instance xor-constraint-correct (prime p))
           :in-theory (disable xor-constraint-correct))))

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
                  (equal c (acl2::bitxor a b))))
  :hints (("Goal" :use (:instance xor-constraint-correct (prime p))
           :in-theory (disable xor-constraint-correct))))

;; This version has the equality in the LHS flipped.
(defthm bitxor-constraint-intro-b-alt
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal c
                         (add b (add a (neg (mul (add a a p) b p) p) p) p))
                  (equal c (acl2::bitxor a b))))
  :hints (("Goal" :use (:instance xor-constraint-correct (prime p))
           :in-theory (disable xor-constraint-correct))))

;; (a+a)*b=a+b-c -> x=bitxor(a,b)
(defthm bitxor-constraint-intro-2
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal (mul (add a a p) b p)
                         (add a (add b (neg c p) p) p))
                  (equal (mod (ifix c) p) ; just c, if we known (fep c p)
                         (acl2::bitxor a b))))
  :hints (("Goal" :use (:instance xor-constraint-correct (prime p) (c (mod (ifix c) p)))
           :in-theory (e/d (pfield::add-same) (xor-constraint-correct
                                               )))))

;; This version has the equality in the LHS flipped.
(defthm bitxor-constraint-intro-2-alt
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal (add a (add b (neg c p) p) p)
                         (mul (add a a p) b p))
                  (equal (mod (ifix c) p) ; just c, if we known (fep c p)
                         (acl2::bitxor a b))))
  :hints (("Goal" :use bitxor-constraint-intro-2
           :in-theory (disable bitxor-constraint-intro-2))))

;; Compared to bitxor-constraint-intro-2, this swaps a and b in the add.
(defthm bitxor-constraint-intro-2b
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal (mul (add a a p) b p)
                         (add b (add a (neg c p) p) p))
                  (equal (mod (ifix c) p) ; just c, if we known (fep c p)
                         (acl2::bitxor a b))))
  :hints (("Goal" :use (:instance xor-constraint-correct (prime p) (c (mod (ifix c) p)))
           :in-theory (e/d (pfield::add-same) (xor-constraint-correct)))))

;; This version has the equality in the LHS flipped.
(defthm bitxor-constraint-intro-2b-alt
  (implies (and (bitp a)
                (bitp b)
                (not (equal 2 p))
                (rtl::primep p))
           (equal (equal (add b (add a (neg c p) p) p)
                         (mul (add a a p) b p))
                  (equal (mod (ifix c) p) ; just c, if we known (fep c p)
                         (acl2::bitxor a b))))
  :hints (("Goal" :use bitxor-constraint-intro-2
           :in-theory (disable bitxor-constraint-intro-2))))

;; TODO: Unpacking, range check, etc.
