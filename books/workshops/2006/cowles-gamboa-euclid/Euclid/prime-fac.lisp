; Unique Prime Factorization Theorem for Positive Integers.
; Copyright (C) 2004 John R. Cowles, University of Wyoming

; This program is free software; you can redistribute it and/or
; modify it under the terms of the GNU General Public License as
; published by the Free Software Foundation; either version 2 of
; the License, or (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free
; Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139,
; USA.

; Written by:
; John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071 U.S.A.

;; The outline of Bob and J's original proof, as developed in THM,
;; is followed. Their proof is described in the book:

;; R.S. Boyer and J S. Moore, A Computational Logic, Academic Press,
;; 1979.

;; For the formal statement of the theorem, search for
;;            PRIME-FACTORIZATION-EXISTENCE and
;;            PRIME-FACTORIZATION-UNIQUENESS.

;; Modified Jan. 05
;; Modified July 05
;; Modified Nov. 05 (for ACL2 Version 2.9.3).
;; Modified July 06 (for ACL2 Version 3.0).

#|
To certify this book, first, create a world with the following package:

(defpkg "POS"
  (set-difference-eq
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)
; Subtracted 12/4/2012 by Matt K. for addition to *acl2-exports*:
   '(nat-listp acl2-number-listp)))

(certify-book "prime-fac"
	      1
	      )
|#
(in-package "POS")

(local
 (include-book "arithmetic/top-with-meta" :dir :system
; Matt K.: Commenting out use of :uncertified-okp after v4-3 in order to
; support provisional certification:
;	       :uncertified-okp nil
	       :defaxioms-okp nil
	       :skip-proofs-okp nil))

(include-book "arithmetic/mod-gcd" :dir :system
; Matt K.: Commenting out use of :uncertified-okp after v4-3 in order to
; support provisional certification:
;	      :uncertified-okp nil
	      :defaxioms-okp nil
	      :skip-proofs-okp nil)

;; The definition of nonneg-int-gcd often interacts with the rewrite rule,
;; commutativity-of-nonneg-int-gcd, to cause the rewriter to loop and stack
;; overflow.
(in-theory (disable ACL2::commutativity-of-nonneg-int-gcd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Here are the definitions of nonnegative-integer-quotient,
;;                             nonneg-int-mod, and
;;                             nonneg-int-gcd.

;; (defun
;;   nonnegative-integer-quotient (i j)
;;   (declare (xargs :guard (and (integerp i)
;;                               (not (< i 0))
;;                               (integerp j)
;;                               (< 0 j))
;;                   :mode :program))
;;   (if (or (= (nfix j) 0)
;;           (< (ifix i) j))
;;       0
;;     (+ 1 (nonnegative-integer-quotient (- i j) j))))

;; (verify-termination
;;   (nonnegative-integer-quotient (declare (xargs :mode :logic))))

;; (defun
;;   nonneg-int-mod ( n d )
;;   (declare (xargs :guard (and (integerp n)
;; 			      (>= n 0)
;; 			      (integerp d)
;; 			      (< 0 d))))
;;   (if (zp d)
;;       (nfix n)
;;       (if (< (nfix n) d)
;; 	  (nfix n)
;; 	(nonneg-int-mod (- n d) d))))

;; (defun
;;   nonneg-int-gcd ( x y )
;;   (declare (xargs :guard (and (integerp x)
;; 			      (>= x 0)
;; 			      (integerp y)
;; 			      (>= y 0))))
;;   (if (zp y)
;;       (nfix x)
;;       (nonneg-int-gcd y (nonneg-int-mod x y))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun
  dividesp (x y)
  "Return T iff x|y iff there is an integer z
   such that (equal (* x z) y)."
  (declare (xargs :guard (and (integerp x)
			      (>= x 0)
			      (integerp y)
			      (>= y 0))))
  (if (zp x)
      (= y 0)
      (= (ACL2::nonneg-int-mod y x) 0)))

(defun
  prime1p (x y)
  "Return T iff x has no divisors z with
   1 < z <= y."
  (declare (xargs :guard (and (integerp x)
			      (>= x 0)
			      (integerp y)
			      (>= y 0))))
  (if (or (zp y)(= y 1))
      t
      (and (not (dividesp y x))
	   (prime1p x (- y 1)))))

#| A positive integer is a prime iff
   it has exactly two positive integer
   divisors, namely 1 and the integer
   itself. The integer 1 is NOT a prime
   under this definition because 1 only
   has one positive integer divisor.

   The definition of primep given below
   is equivalent to the one just stated.
|#

(defun
  primep (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (> x 1)
       (prime1p x (- x 1))))

(defthm
  not-prime1p-lemma
  (implies (and (integerp y)

; Matt K. mod 5/2016 (type-set bit for {1}): Originally the following
; hypothesis was instead (dividesp z x), and was last.  After our type-set
; changes, where this lemma was applied to prove divisors-of-primep, the
; free-variable match failed for the old version of this lemma.  The problem
; was that D was on the type-alist with type *ts-integer>1*; neither (< 1 D)
; nor (< D 2) was on the type-alist.  Since dividesp is enabled, here we place
; what amounts to the expanded form of (dividesp z x).

                (equal (acl2::nonneg-int-mod x z) 0)
		(< 1 z)
		(<= z y))
	   (not (prime1p x y))))

(defun
  greatest-factor (x y)
  "Return the largest z such that z|x and
   1 < z <= y. If no such z exists return x."
  (declare (xargs :guard (and (integerp x)
			      (>= x 0)
			      (integerp y)
			      (>= y 0))))
  (cond ((or (zp y)(= y 1))
	 x)
	((dividesp y x) y)
	(t (greatest-factor x (- y 1)))))

(defthm
  x>1-forward
  (implies (and (not (equal x 1))
		(not (zp x)))
	   (> x 1))
  :rule-classes :forward-chaining)

(defthm
  greatest-factor=1
  (equal (equal (greatest-factor x y) 1)
	 (equal x 1)))

(defthm
  natp-greatest-factor
  (equal (and (integerp (greatest-factor x y))
	      (>= (greatest-factor x y) 0))
	 (or (and (integerp y)
		  (> y 1))
	     (and (integerp x)
		  (>= x 0))))
  :rule-classes ((:type-prescription
		  :corollary
		  (implies (and (integerp x)
				(>= x 0))
			   (and (integerp (greatest-factor x y))
				(>= (greatest-factor x y) 0))))
		 (:type-prescription
		  :corollary
		  (implies (and (integerp y)
				(> y 1))
			   (and (integerp (greatest-factor x y))
				(>= (greatest-factor x y) 0))))
		 (:type-prescription
		  :corollary
		  (implies (and (not (zp y))
				(not (equal y 1)))
			   (and (integerp (greatest-factor x y))
				(>= (greatest-factor x y) 0))))))

(defthm
  dividesp-greatest-factor
  (implies (and (integerp x)
		(>= x 0))
	   (dividesp (greatest-factor x y) x))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp x)
				(>= x 0))
			   (equal
			    (ACL2::nonneg-int-mod x (greatest-factor x y)) 0)))))

(defthm
  <-greatest-factor
  (implies (and (> x y)
		(not (prime1p x y)))
	   (< (greatest-factor x y) x))
  :rule-classes (:rewrite :linear))

(defthm
  greatest-factor->-1
  (implies (> i 1)
	   (> (greatest-factor i j) 1))
  :rule-classes :linear)

(defthm
  <-nonnegative-integer-quotient
  (implies (and (> i 0)
		(> j 1))
	   (< (nonnegative-integer-quotient i j) i))
  :rule-classes :linear)

(defthm
  posp-nonnegative-integer-quotient
  (implies (and (integerp i)
		(integerp j)
		(>= i j)
		(> j 0))
	   (> (nonnegative-integer-quotient i j) 0))
  :rule-classes :type-prescription)

(defthm
  *-nonnegative-integer-quotient
  (implies (and (integerp y)
		(>= y 0)
		(dividesp x y))
	   (equal (* x (nonnegative-integer-quotient y x))
		  y)))

(defun
  prime-factors (x)
  "Return a list, lst, of primes so that
   x = product of the members of lst."
  (declare (xargs :guard (and (integerp x)
			      (>= x 0))))
  (cond ((or (zp x)(= x 1)) nil)
	((primep x)(list x))
	(t (append (prime-factors (greatest-factor x (- x 1)))
		   (prime-factors (nonnegative-integer-quotient
				   x
				   (greatest-factor x (- x 1))))))))

(defun
  prime-listp (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (and (primep (car lst))
	   (prime-listp (cdr lst)))
      t))

(defthm
  prime-listp-append
  (implies (and (prime-listp lst1)
		(prime-listp lst2))
	   (prime-listp (append lst1 lst2))))

(defun
  acl2-number-listp (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (and (acl2-numberp (car lst))
	   (acl2-number-listp (cdr lst)))
      t))

(defun
  product-lst (lst)
  (declare (xargs :guard (acl2-number-listp lst)))
  (if (consp lst)
      (* (car lst)(product-lst (cdr lst)))
      1))

(defthm
  product-lst-append
  (equal (product-lst (append lst1 lst2))
	 (* (product-lst lst1)
	    (product-lst lst2))))

(defthm
  prime-listp-prime-factors
  (prime-listp (prime-factors x)))

(defthm
  product-lst-prime-factors
  (implies (and (integerp x)
		(> x 0))
	   (equal (product-lst (prime-factors x)) x)))

(defthm
  PRIME-FACTORIZATION-EXISTENCE
  (and (prime-listp (prime-factors x))
       (implies (and (integerp x)
		     (> x 0))
		(equal (product-lst (prime-factors x)) x)))
  :rule-classes nil)

(defun
  nat-listp (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (and (integerp (car lst))
	   (>= (car lst) 0)
	   (nat-listp (cdr lst)))
      t))

(defthm
  natp-product-lst
  (implies (nat-listp lst)
	   (and (integerp (product-lst lst))
		(>= (product-lst lst) 0)))
  :rule-classes :type-prescription)

(defthm
  prime-listp=>nat-listp
  (implies (prime-listp lst)
	   (nat-listp lst))
  :rule-classes :forward-chaining)

(defthm
  nonneg-int-mod-*-0-rt
  (implies (and (integerp x)
		(integerp y)
		(>= y 0)
		(equal (ACL2::nonneg-int-mod y c) 0))
	   (equal (ACL2::nonneg-int-mod (* x y) c) 0)))

(defthm
  nonneg-int-mod-product-lst
  (implies (and (nat-listp lst)
		(member-equal c lst))
	   (equal (ACL2::nonneg-int-mod (product-lst lst) c) 0)))

(defthm
  nonnegative-integer-quotient-*
  (implies (and (integerp x)
		(> x 0)
		(integerp y)
		(>= y 0))
	   (equal (nonnegative-integer-quotient (* x y) x) y))
  :hints (("goal"
	   :in-theory (disable *-nonnegative-integer-quotient)
	   :use (:instance
		 *-nonnegative-integer-quotient
		 (y (* x y))))))

(defthm
  *-nonnegative-integer-quotient-*
  (implies (and (integerp w)
		(integerp c)
		(>= c 0)
		(dividesp a w))
	   (equal (* c (nonnegative-integer-quotient w a))
		  (nonnegative-integer-quotient (* c w) a))))

(defthm
  divisors-of-primep
  (implies (and (primep p)
		(dividesp d p))
	   (or (equal d p)
	       (equal d 1)))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  ACL2::divisor-<=
		  (ACL2::n p)
		  (ACL2::d d))))))

(defthm
  nonneg-int-gcd=>nonneg-int-mod
  (implies (equal (ACL2::nonneg-int-gcd x y) y)
	   (equal (ACL2::nonneg-int-mod x y) 0)))

(defthm
  primep=>nonneg-int-gcd=1
  (implies (and (not (dividesp p x))
		(primep p))
	   (equal (ACL2::nonneg-int-gcd x p) 1))
  :hints (("Goal"
	   :use (:instance
		 divisors-of-primep
		 (d (ACL2::nonneg-int-gcd x p))))))

(defthm
  Prime-divisor-of-product-divides-factor
  (implies (and (primep p)
		(dividesp p (* x y))
		(not (dividesp p y)))
	   (dividesp p x))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (primep p)
				(equal (ACL2::nonneg-int-mod (* x y) p) 0)
				(not (dividesp p y)))
			   (equal (ACL2::nonneg-int-mod x p) 0))))
  :hints (("Goal"
	   :use (:instance
		 ACL2::Divisor-of-product-divides-factor
		 (ACL2::z p)
		 (ACL2::y y)
		 (ACL2::x x)))))

(defthm
  divides-product-lst=>member-equal
  (implies (and (primep p)
		(prime-listp lst)
		(not (member-equal p lst)))
	   (not (equal (ACL2::nonneg-int-mod (product-lst lst) p) 0)))
  :hints (("Subgoal *1/5"
	   :use (:instance
		 divisors-of-primep
		 (d p)
		 (p (car lst))))))

(defthm
  *-prime-product-lst=>member-equal
  (implies (and (equal (* p (product-lst lst1))
		       (product-lst lst2))
		(nat-listp lst1)
		(primep p)
		(prime-listp lst2))
	   (member-equal p lst2))
 :hints (("Goal"
	  :in-theory (disable divides-product-lst=>member-equal)
	  :use (:instance
		divides-product-lst=>member-equal
		(lst lst2)))))

(defun
  delete-one (x lst)
  "Return the result of deleting
   one occurrence of x from the list lst."
  (declare (xargs :guard t))
  (if (consp lst)
      (if (equal x (car lst))
	  (cdr lst)
	  (cons (car lst)(delete-one x (cdr lst))))
      lst))

(defthm
  prime-listp-delete-one
  (implies (prime-listp lst)
	   (prime-listp (delete-one x lst))))

(defthm
  product-lst-delete-one
  (implies (and (nat-listp lst)
		(member-equal c lst)
		(> c 0))
	   (equal (product-lst (delete-one c lst))
		  (nonnegative-integer-quotient (product-lst lst) c)))
  :hints (("subgoal *1/4"
	   :in-theory (disable *-nonnegative-integer-quotient-*)
	   :use (:instance
		 *-nonnegative-integer-quotient-*
		 (c (car lst))
		 (w (product-lst (cdr lst)))
		 (a c)))))

(defun
  bag-equal (lst1 lst2)
  "Return T iff lst1 and lst2 have the same
   members with the same multiplicity (but
   maybe in a different order)."
  (declare (xargs :guard (true-listp lst2)))
  (if (consp lst1)
      (and (member-equal (car lst1) lst2)
	   (bag-equal (cdr lst1)
		      (delete-one (car lst1) lst2)))
      (atom lst2)))

(defthm
  product-lst-of-prime-listp>1
  (implies (and (prime-listp lst)
		(consp lst))
	   (> (product-lst lst) 1))
  :rule-classes :linear)

(defthm
  PRIME-FACTORIZATION-UNIQUENESS
  (implies (and (prime-listp lst1)
		(prime-listp lst2)
		(equal (product-lst lst1)
		       (product-lst lst2)))
	  (bag-equal lst1 lst2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Show that bag-equal has the expected properties:

;;  Lisp objects that are bag-equal have the same length.

;;  Lisp objects that are bag-equal have the same members.

;;  Elements in Lisp objects that are bag-equal occur
;;  in each object with the same multiplicity.

(defthm
  len-delete-one
  (implies (member-equal x lst)
	   (equal (+ 1 (len (delete-one x lst)))
		  (len lst))))

(defthm
  bag-equal->equal-len
  (implies (bag-equal lst1 lst2)
	   (equal (len lst1)
		  (len lst2)))
  :rule-classes nil)

(defthm
  member-equal-delete-one
  (implies (not (equal x y))
	   (iff (member-equal x (delete-one y lst))
	        (member-equal x lst))))

(defthm
  bag-equal->iff-member-equal
  (implies (bag-equal lst1 lst2)
	   (iff (member-equal x lst1)
		(member-equal x lst2))))

(defun
  multiplicity (x lst)
  (if (consp lst)
      (if (equal x (car lst))
	  (+ 1 (multiplicity x (cdr lst)))
	  (multiplicity x (cdr lst)))
      0))

(defthm
  multiplicity-delete-one-1
  (implies (member-equal x lst)
	   (equal (+ 1 (multiplicity x (delete-one x lst)))
		  (multiplicity x lst))))

(defthm
  multiplicity-delete-one-2
  (implies (not (equal x y))
	   (equal (multiplicity x (delete-one y lst))
		  (multiplicity x lst))))

(defthm
  bag-equal->equal-multiplicity
  (implies (bag-equal lst1 lst2)
	   (equal (multiplicity x lst1)
		  (multiplicity x lst2)))
  :rule-classes nil)
