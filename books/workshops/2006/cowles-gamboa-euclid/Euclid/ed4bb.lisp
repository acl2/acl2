; ACL2 Euclidean Domain books -- Book 4bb -- Example: Integers.
;  The Integers are shown to be an Euclidean Domain with
;  unique factorization. Here Size is abs; Quotient is truncate
;  and Remainder is rem.

;  This version uses computable Skolem functions [in place of
;  quantifiers (defun-sk)] and is executable. The name of
;  each computable Skolem function, contains a $ symbol.

; Copyright (C) 2005  John R. Cowles, University of Wyoming

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:
; John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071-3682 U.S.A.

; Last modified Feb. 06.

#|
To certify this book, first, create a world with the following package:

(defpkg "INT-REM"
  (set-difference-eq (union-eq
                      *acl2-exports*
                      *common-lisp-symbols-from-main-lisp-package*)
; Subtracted 12/4/2012 by Matt K. for addition to *acl2-exports* ; ; ;
                     '(nat-listp acl2-number-listp)))

(certify-book "ed4bb"
	      1)
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The Integers are an Euclidean Doamin:

;;  integerp  ; Predicate for set of Euclidean Domain elements.
;;  equal     ; Equality predicate for Euclidean Domain elements.
;;  identity  ; Choose unique equivalence class representative for equal.
;;  +         ; Addition in Euclidean Domain.
;;  *         ; Multiplication in Euclidean Domain.
;;  -         ; Unary minus in Euclidean Domain.
;;  0         ; 0 element in Euclidean Domain.
;;  1         ; 1 element in Euclidean Domain.
;;  abs       ; Natp size of each nonzero Euclidean Domain element.
;;  truncate  ; Quotient in Euclidean Domain.
;;  rem       ; Remainder in Euclidean Domain.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; An Euclidean Domain is an integral domain, together with a Size function
;; from nonzero domain elements into the nonnegative integers, that
;; satisfies the Division Propery:
;;
;; Division Propery. For all domain elements x and all nonzero domain
;;             elements y there are domain elements q and r such that

;;        x = yq + r and either r is the domain's zero or Size(r) < Size(y)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; An Integral Domain is a commutative ring with no zero-divisors.

;; A Zero-Divisor in a commutative ring is a nonzero ring element, x, such
;; that there is a nonzero ring element y such that the product xy equals
;; the zero element of the ring.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A Commutative Ring is a nonempty set with two binary operations, addition
;; and multiplication, an unary operation, minus, and a ring element, zero,
;; such that

;; (1) the binary operations are commutative and associative,
;; (2) multiplication distributes over addition,
;; (3) zero is an identity for addition, and
;; (4) minus produces an additive inverse

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Every Euclidean Domain has a multiplicative identity.
;;   See Book 1 of ACL2 Euclidean Domain books, ed1.lisp, for a proof.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; There is no loss of generality in assuming the
;;   Multiplicative Size Property:

;;     For all nonzero domain elements x and y, Size(x) <= Size(xy).

;;     If the original Size function does not satisfy this property,
;;     then it can replaced by another that does satisfy this and the
;;     division property.
;;      See Book 2 of the ACL2 Euclidean Domain books, ed2.lisp,
;;      for a proof.

;;  In fact, for integers x and y, (abs (* x y)) = (* (abs x)(abs y)).
;;   So, if integer y differs from 0, then (<= 1 (abs y)); then for
;;   any integer x, (abs x) =  (* (abs x) 1) <= (* (abs x)(abs y))
;;                                            = (abs (* x y)).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "INT-REM")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Make temporary use of an ACL2 Arithmetic Book and a book containing facts
;  about TRUNCATE and REM to help certify this book

(local
 (include-book "arithmetic/top" :dir :system
; Matt K.: Commenting out use of :uncertified-okp after v4-3 in order to
; support provisional certification:
;	       :uncertified-okp nil
	       :defaxioms-okp nil
	       :skip-proofs-okp nil))

(local
 (include-book "ihs/quotient-remainder-lemmas" :dir :system
; Matt K.: Commenting out use of :uncertified-okp after v4-3 in order to
; support provisional certification:
;	       :uncertified-okp nil
	       :defaxioms-okp nil
	       :skip-proofs-okp nil))

(local
 (in-theory (disable acl2::quotient-remainder-functions)))

;; Make temporary use of an ACL2 Euclidean Domain Book:
(local
 (include-book "ed3"
; Matt K.: Commenting out use of :uncertified-okp after v4-3 in order to
; support provisional certification:
;	       :uncertified-okp nil
	       :defaxioms-okp nil
	       :skip-proofs-okp nil))

;; AXIOMS
;;; Integral Domain Axioms:
(defthm
  Closure-Laws
  (and (implies (integerp x)
		(and (implies (integerp y)
			      (and (integerp (+ x y))
				   (integerp (* x y))))
		     (integerp (- x))))
       (integerp 0)
       (integerp 1))
  :rule-classes nil)

(defthm
  Equivalence-Law
  (implies (integerp x)
	   (and (equal x x)
		(implies (integerp y)
			 (and (booleanp (equal x y))
			      (implies (equal x y)
				       (equal y x))
			      (implies (integerp z)
				       (implies (and (equal x y)
						     (equal y z))
						(equal x z)))))))
  :rule-classes nil)

(defthm
  Congruence-Laws
  (implies (equal y1 y2)
	   (and (iff (integerp y1)
		     (integerp y2))
		(implies (and (integerp y1)
			      (integerp y2))
			 (and (implies (integerp x)
				       (and (equal (+ x y1)
						   (+ x y2))
					    (equal (* x y1)
						   (* x y2))))
			      (implies (integerp z)
				       (and (equal (+ y1 z)
						   (+ y2 z))
					    (equal (* y1 z)
						   (* y2 z))))
			      (equal (- y1)
				     (- y2))))))
  :rule-classes nil)

(defthm
  Closure-of-identity
  (implies (integerp x)
	   (integerp (identity x)))
  :rule-classes nil)

(defthm
  Equivalence-class-Laws
  (and (implies (integerp x)
		(equal (identity x) x))
       (implies (and (integerp y1)
		     (integerp y2)
		     (equal y1 y2))
		(equal (identity y1)
		       (identity y2))))
  :rule-classes nil)

(defthm
  Commutativity-Laws
  (implies (and (integerp x)
		(integerp y))
	   (and (equal (+ x y)
		       (+ y x))
		(equal (* x y)
		       (* y x))))
  :rule-classes nil)

(defthm
  Associativity-Laws
  (implies (and (integerp x)
		(integerp y)
		(integerp z))
	   (and (equal (+ (+ x y) z)
		       (+ x (+ y z)))
		(equal (* (* x y) z)
		       (* x (* y z)))))
  :rule-classes nil)

(defthm
  Left-Distributivity-Law
  (implies (and (integerp x)
		(integerp y)
		(integerp z))
	   (equal (* x (+ y z))
		  (+ (* x y)
		       (* x z))))
  :rule-classes nil)

(defthm
  Left-Unicity-Laws
  (implies (integerp x)
	   (and (equal (+ 0 x)
		       x)
		(equal (* 1 x)
		       x)))
  :rule-classes nil)

(defthm
  Right-Inverse-Law
  (implies (integerp x)
	   (equal (+ x (- x))
		  0))
  :rule-classes nil)

(defthm
  Zero-Divisor-Law
  (implies (and (integerp x)
		(integerp y))
	   (equal (equal (* x y) 0)
		  (or (equal x 0)
		      (equal y 0))))
  :rule-classes nil)

;; Euclidean Domain Axioms:
(defthm
  Natp-abs
  (implies (and (integerp x)
		(not (equal x 0)))
	   (and (integerp (abs x))
		(>= (abs x) 0)))
  :rule-classes ((:type-prescription
		  :corollary
		  (implies (integerp x)
			   (and (integerp (abs x))
				(>= (abs x) 0))))
		 (:linear
		  :corollary
		  (implies (and (integerp x)
				(not (equal x 0)))
			   (> (abs x) 0)))))

(defthm
  Congruence-for-abs
  (implies (and (integerp y1)
		(integerp y2)
		(equal y1 y2))
	   (equal (abs y1)
		  (abs y2)))
  :rule-classes nil)

(defthm
  Closure-of-truncate-&-rem
  (implies (and (integerp x)
		(integerp y)
		(not (equal y 0)))
	   (and (integerp (truncate x y))
		(integerp (rem x y))))
  :rule-classes nil)

(defthm
  Congruence-for-truncate-&-rem
  (implies (and (integerp y1)
		(integerp y2)
		(equal y1 y2))
	   (and (implies (and (integerp x)
			      (not (equal y1 0)))
			 (and (equal (truncate x y1)
				     (truncate x y2))
			      (equal (rem x y1)
				     (rem x y2))))
		(implies (and (integerp z)
			      (not (equal z 0)))
			 (and (equal (truncate y1 z)
				     (truncate y2 z))
			      (equal (rem y1 z)
				     (rem y2 z))))))
  :rule-classes nil)

(defthm
  Division-property
  (implies (and (integerp x)
		(integerp y)
		(not (equal y 0)))
	   (and (equal x (+ (* y (truncate x y))
			    (rem x y)))
		(or (equal (rem x y) 0)
		    (< (abs (rem x y))
		       (abs y)))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (equal y 0))
				(not (equal (rem x y) 0)))
			   (< (abs (rem x y))
			      (abs y))))
		 (:linear
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (equal y 0))
				(not (equal (rem x y)0)))
			   (< (abs (rem x y))
			      (abs y))))))

(defthm
  Abs-*
  (implies (and (integerp x)
		(not (equal x 0))
		(integerp y)
		(not (equal y 0)))
	   (<= (abs x)
	       (abs (* x y))))
  :rule-classes (:linear
		 (:rewrite
		  :corollary
		  (and (implies (and (integerp x)
				     (integerp y))
				(equal (abs (* x y))
				       (* (abs x)(abs y))))
		       (implies (and (integerp x)
				     (not (equal x 0))
				     (integerp y)
				     (not (equal y 0)))
				(<= (abs x)
				    (abs (* x y)))))))
  :hints (("Goal"
	   :in-theory (disable (:definition abs))
	   :use ((:instance
		  (:theorem
		   (implies (and (integerp x)
				 (> x 0)
				 (integerp y)
				 (> y 0))
			    (<= x (* x y))))
		  (x (abs x))
		  (y (abs y)))
		 (:theorem
		  (implies (and (integerp x)
				(integerp y))
			   (equal (abs (* x y))
				  (* (abs x)(abs y)))))))
	  ("Subgoal 1"
	   :in-theory (enable (:definition abs)))))

(in-theory (disable (:definition abs)))

;;;;;;;;;;;;;;;;;;;;
;; Divides-p theory:

;; (defun-sk
;;   divides-p (x y)
;;   (exists z (and (integerp x)
;;                  (integerp z)
;;                  (equal (* x z)
;;                         y))))

;; Computable Skolem function
(defun
  Divides-p$-witness (x y)
  (declare (xargs :guard
		  (and (acl2-numberp x)
		       (acl2-numberp y))))
  (if (not (= x 0))
      (let ((q (* y (/ x))))
	   (if (integerp q)
	       q
	       0))
      0))

(defun
  Divides-p (x y)
  (declare (xargs :guard
		  (and (acl2-numberp x)
		       (acl2-numberp y))))
  (let ((z (divides-p$-witness x y)))
       (and (integerp x)
	    (integerp z)
	    (= (* x z) y))))

(defthm
  Divides-p-suff
  (implies (and (integerp x)
		(integerp z)
		(equal (* x z) y))
	   (divides-p x y))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (equal (* x z) y)
				(integerp x)
				(integerp z))
			   (divides-p x y)))))

(in-theory (disable (:definition divides-p$-witness)))

;;;;;;;;;;;;;;;;;
;; Unit-p theory:

(defun
  Unit-p (x)
  (declare (xargs :guard
		  (acl2-numberp x)))
  (divides-p x 1))

(defthm
  Abs-unit-p=1
  (implies (unit-p x)
	   (equal (abs x)
		  1))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  acl2::Size-unit-p=Size-1_e
		  (acl2::edp integerp)
		  (acl2::=_e equal)
		  (acl2::C_=_e identity)
		  (acl2::binary-+_e binary-+)
		  (acl2::binary-*_e binary-*)
		  (acl2::-_e unary--)
		  (acl2::0_e (lambda () 0))
		  (acl2::1_e (lambda () 1))
		  (acl2::size abs)
		  (acl2::q_e truncate)
		  (acl2::r_e rem)
		  (acl2::divides-p divides-p)
		  (acl2::divides-p-witness divides-p$-witness)
		  (acl2::unit-p unit-p))
		 (acl2::x x)))
	  ("Subgoal 2"
	   :by (:instance
		Divides-p-suff
		(x acl2::x)
		(y acl2::y)
		(z acl2::z)))))

(defthm
  Abs=1-implies-unit-p
  (implies (and (integerp x)
		(not (equal x 0))
		(equal (abs x)
		       1))
	   (unit-p x))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  acl2::Size=Size-1_e-implies-unit-p
		  (acl2::edp integerp)
		  (acl2::=_e equal)
		  (acl2::C_=_e identity)
		  (acl2::binary-+_e binary-+)
		  (acl2::binary-*_e binary-*)
		  (acl2::-_e unary--)
		  (acl2::0_e (lambda () 0))
		  (acl2::1_e (lambda () 1))
		  (acl2::size abs)
		  (acl2::q_e truncate)
		  (acl2::r_e rem)
		  (acl2::divides-p divides-p)
		  (acl2::divides-p-witness divides-p$-witness)
		  (acl2::unit-p unit-p))
		 (acl2::x x)))))

(defthm
  unit-p=_+1_or_-1
  (equal (unit-p x)
	 (or (equal x 1)
	     (equal x -1)))
  :hints (("Goal"
	   :in-theory (enable abs)
	   :use (Abs-unit-p=1
		 Abs=1-implies-unit-p))))

(defthm
  Abs-<-abs-*
  (implies (and (not (unit-p y))
		(integerp x)
		(not (equal x 0))
		(integerp y)
		(not (equal y 0)))
	   (< (abs x)
	      (abs (* x y))))
  :rule-classes (:linear
		 :rewrite)
  :hints (("Goal"
	   :in-theory (e/d ((:definition abs))
			   ((:definition unit-p))))))

;;;;;;;;;;;;;;;;;;;;;;;;
;; Reducible-p and
;; Irreducible-p theory:

;; (defun-sk
;;   reducible-p (x)
;;   (exists (y z)(and (integerp y)
;;                     (integerp z)
;;                     (not (unit-p y))
;;                     (not (unit-p z))
;;                     (equal (* y z) x))))

(defun
  Greatest-factor (x y)
  "Return the largest z such that z|x and
   1 < z <= y. If no such z exists return |x|."
  (declare (xargs :guard
		  (and (real/rationalp x)
		       (integerp y)
		       (>= y 0))))
  (cond ((or (zp y)(= y 1))
	 (abs x))
	((divides-p y x) y)
	(t (greatest-factor x (- y 1)))))

(defthm
  Natp-greatest-factor
  (implies (and (integerp x)
		(integerp y)
		(>= y 0))
	   (and (integerp (greatest-factor x y))
		(>= (greatest-factor x y) 0)))
  :rule-classes :type-prescription)

(defthm
  Divides-p-greatest-factor
  (implies (integerp x)
	   (divides-p (greatest-factor x y) x))
  :hints (("Goal"
	   :in-theory (enable (:definition abs)
			      (:definition divides-p$-witness)))))

(defthm
  x>1-forward
  (implies (and (not (equal x 1))
		(not (zp x)))
	   (> x 1))
  :rule-classes :forward-chaining)

(defthm
  Not-integerp-/-a
  (implies (and (rationalp y)
		(> y 1))
	   (not (integerp (/ y))))
  :hints (("Goal"
	   :use (:theorem
		 (implies (and (rationalp y)
			       (> y 1))
			  (< (/ y) 1))))))

(defthm
  Not-integerp-/-b-lemma
  (implies (and (rationalp y)
		(> y 1))
	   (> (- (/ y)) -1))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:theorem
		  (implies (< x y)
			   (> (- x)(- y))))
		 (x (/ y))
		 (y 1)))))

(defthm
  Not-integerp-/-b
  (implies (and (rationalp y)
		(> y 1))
	   (not (integerp (- (/ y)))))
  :hints (("Goal"
	   :use Not-integerp-/-b-lemma)))

(defthm
  Greatest-factor=1
  (implies (rationalp y)
	   (equal (equal (greatest-factor x y) 1)
		  (or (equal x 1)
		      (equal x -1))))
  :hints (("Goal"
	   :in-theory (enable (:definition abs)
			      (:definition divides-p$-witness)))))

(defthm
  Greatest-factor->-1
  (implies (> i 1)
	   (> (greatest-factor i j) 1))
  :rule-classes :linear
  :hints (("Goal"
	   :in-theory (enable (:definition abs)))))

(defthm
  Greatest-factor->-1-a
  (implies (< i -1)
	   (> (greatest-factor i j) 1))
  :rule-classes :linear
  :hints (("Goal"
	   :in-theory (enable (:definition abs)))))

(defthm
  Greatest-factor->=-divisor
  (implies (and (divides-p z x)
		(integerp y)
		(< 1 z)
		(<= z y))
	   (>= (greatest-factor x y) z))
  :rule-classes :linear)

(defthm
  Greatest-factor-<=-y
  (implies (and (divides-p z x)
		(integerp y)
		(< 1 z)
		(<= z y))
	   (<= (greatest-factor x y) y))
  :rule-classes :linear)

;; Computable Skolem function
(defun
  Reducible-p$-witness (x)
  (declare (xargs :guard (integerp x)))
  (let ((gf (greatest-factor x (nfix (- (abs x) 1)))))
       (mv (divides-p$-witness gf x) gf)))

(defun
  Reducible-p (x)
  (declare (xargs :guard (integerp x)))
  (mv-let (y z)
	  (reducible-p$-witness x)
	  (and (integerp y)
	       (integerp z)
	       (not (unit-p y))
	       (not (unit-p z))
	       (= (* y z) x))))

(in-theory (disable (:definition Reducible-p$-witness)))

(in-theory (enable (:definition divides-p$-witness)))

(defthm
  Subgoal-7.4
  (implies (and (integerp y)
		(integerp z)
		(not (equal y -1))
		(not (equal z -1))
		(< y 0)
		(< z 0)
		(<= 1 (* y z)))
	   (not (equal (divides-p$-witness (greatest-factor (* y z)
							    (+ -1 (* y z)))
					   (* y z))
		       1)))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Greatest-factor-<=-y
		  (x (* y z))
		  (y (+ -1 (* y z)))
		  (z (- z)))
		 (:instance
		  (:theorem
		   (implies (and (integerp b)
				 (not (equal b 0))
				 (equal (* a (/ b)) 1))
			    (equal a b)))
		  (a (* y z))
		  (b (greatest-factor (* y z) (+ -1 (* y z)))))
		 (:instance
		  (:theorem
		   (implies (and (integerp a)
				 (integerp b)
				 (>= a 2)
				 (>= b 2))
			    (>= (* (- a 1) b) 1)))
		 (a (- y))
		 (b (- z)))))))

(defthm
  Subgoal-7.3-lemma
  (implies (and (integerp a)
		(integerp b)
		(integerp y)
		(integerp z)
		(<= y a)
		(<= z b)
		(< a 0)
		(< b 0))
	   (>= (* y z)(* a b)))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:theorem
		  (implies (and (integerp a)
				(integerp y)
				(integerp z)
				(<= y a)
				(<= z b)
				(< b 0))
			   (>= (* y z)(* a z))))
		 (:theorem
		  (implies (and (integerp a)
				(integerp b)
				(integerp z)
				(<= z b)
				(< a 0))
			   (>= (* a z)(* a b))))))
	  ("Subgoal 3"
	   :in-theory (disable acl2::<-*-left-cancel
			       acl2::<-*-right-cancel))))

(defthm
  Subgoal-7.3-lemma-a
  (implies (and (integerp y)
		(integerp z)
		(<= y -2)
		(<= z -2))
	   (>= (* y z) 4))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 subgoal-7.3-lemma
		 (a -2)
		 (b -2)))))

(defthm
  Subgoal-7.3
  (implies (and (integerp y)
		(integerp z)
		(not (equal y -1))
		(not (equal z -1))
		(< y 0)
		(< z 0))
	   (not (equal (* y z) 1)))
  :rule-classes nil
  :hints (("Goal"
	   :use subgoal-7.3-lemma-a)))

(defthm
  Subgoal-7.1
  (implies (and (integerp y)
		(integerp z)
		(not (equal y -1))
		(not (equal z -1))
		(< y 0)
		(< z 0)
		(<= 1 (* y z)))
	   (equal (* (greatest-factor (* y z) (+ -1 (* y z)))
		     (divides-p$-witness (greatest-factor (* y z) (+ -1 (* y z)))
					 (* y z)))
		  (* y z)))
  :rule-classes nil
  :hints (("Subgoal 3"
	   :use (:instance
		 Greatest-factor->-1
		 (i (* y z))
		 (j (+ -1 (* y z)))))
	  ("Subgoal 1"
	   :in-theory (disable divides-p-greatest-factor)
	   :use (:instance
		 divides-p-greatest-factor
		 (x (* y z))
		 (y (+ -1 (* y z)))))))

(defthm
  Subgoal-5.3-lemma
  (implies (and (integerp a)
		(integerp b)
		(integerp y)
		(integerp z)
		(>= y a)
		(<= z b)
		(> a 0)
		(< b 0))
	   (<= (* y z)(* a b)))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:theorem
		  (implies (and (integerp a)
				(integerp y)
				(integerp z)
				(>= y a)
				(<= z b)
				(< b 0))
			   (<= (* y z)(* a z))))
		 (:theorem
		  (implies (and (integerp a)
				(integerp b)
				(integerp z)
				(<= z b)
				(> a 0))
			   (<= (* a z)(* a b))))))
	  ("Subgoal 3"
	   :in-theory (disable acl2::<-*-left-cancel
			       acl2::<-*-right-cancel))))

(defthm
  Subgoal-5.3-lemma-a
  (implies (and (integerp y)
		(integerp z)
		(>= y 2)
		(<= z -2))
	   (<= (* y z) -4))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 subgoal-5.3-lemma
		 (a 2)
		 (b -2)))))

(defthm
  Subgoal-5.3
  (implies (and (integerp y)
		(integerp z)
		(not (equal y 1))
		(not (equal z -1))
		(>= y 0)
		(< z 0))
	   (not (equal (* y z) -1)))
  :rule-classes nil
  :hints (("Goal"
	   :use subgoal-5.3-lemma-a)))

(defthm
  Subgoal-5.2
  (implies (and (integerp y)
		(integerp z)
		(not (equal y 1))
		(not (equal z -1))
		(<= 0 y)
		(< z 0)
		(<= 1 (- (* y z))))
	   (not (equal (divides-p$-witness (greatest-factor (* y z)
							    (+ -1 (- (* y z))))
					   (* y z))
		       -1)))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Greatest-factor-<=-y
		  (x (* y z))
		  (y (+ -1 (- (* y z))))
		  (z (- z)))
		 (:instance
		  (:theorem
		   (implies (and (integerp b)
				 (not (equal b 0))
				 (equal (* a (/ b)) -1))
			    (equal (- a) b)))
		  (a (* y z))
		  (b (greatest-factor (* y z) (+ -1 (- (* y z))))))
		 (:instance
		  (:theorem
		   (implies (and (integerp a)
				 (integerp b)
				 (>= a 2)
				 (>= b 2))
			    (>= (* (- a 1) b) 1)))
		 (a  y)
		 (b (- z)))))))

(defthm
  Subgoal-5.1
  (implies (and (integerp y)
		(integerp z)
		(not (equal y 1))
		(not (equal z -1))
		(<= 0 y)
		(< z 0)
		(<= 1 (- (* y z))))
	   (equal (* (greatest-factor (* y z)
				      (+ -1 (- (* y z))))
		     (divides-p$-witness (greatest-factor (* y z)
							  (+ -1 (- (* y z))))
					 (* y z)))
		  (* y z)))
  :rule-classes nil
  :hints (("Subgoal 3"
	   :use (:instance
		 Greatest-factor->-1-a
		 (i (* y z))
		 (j (+ -1 (- (* y z))))))
	  ("Subgoal 1"
	   :in-theory (disable divides-p-greatest-factor)
	   :use (:instance
		 divides-p-greatest-factor
		 (x (* y z))
		 (y (+ -1 (- (* y z))))))))

(defthm
  Subgoal-1.4
  (implies (and (integerp y)
		(integerp z)
		(not (equal y 1))
		(not (equal z 1))
		(<= 0 y)
		(<= 0 z)
		(<= 1 (* y z)))
	   (not (equal (divides-p$-witness (greatest-factor (* y z)
							    (+ -1 (* y z)))
					   (* y z))
		       1)))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Greatest-factor-<=-y
		  (x (* y z))
		  (y (+ -1 (* y z))))
		 (:instance
		  (:theorem
		   (implies (and (integerp b)
				 (not (equal b 0))
				 (equal (* a (/ b)) 1))
			    (equal a b)))
		  (a (* y z))
		  (b (greatest-factor (* y z) (+ -1 (* y z)))))
		 (:instance
		  (:theorem
		   (implies (and (integerp a)
				 (integerp b)
				 (>= a 2)
				 (>= b 2))
			    (>= (* (- a 1) b) 1)))
		 (a y)
		 (b z))))))

(defthm
  Subgoal-1.3-lemma
  (implies (and (integerp a)
		(integerp b)
		(integerp y)
		(integerp z)
		(>= y a)
		(>= z b)
		(> a 0)
		(> b 0))
	   (>= (* y z)(* a b)))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:theorem
		  (implies (and (integerp a)
				(integerp y)
				(integerp z)
				(>= y a)
				(>= z b)
				(> b 0))
			   (>= (* y z)(* a z))))
		 (:theorem
		  (implies (and (integerp a)
				(integerp b)
				(integerp z)
				(>= z b)
				(> a 0))
			   (>= (* a z)(* a b))))))
	  ("Subgoal 3"
	   :in-theory (disable acl2::<-*-left-cancel
			       acl2::<-*-right-cancel))))

(defthm
  Subgoal-1.3-lemma-a
  (implies (and (integerp y)
		(integerp z)
		(>= y 2)
		(>= z 2))
	   (>= (* y z) 4))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 subgoal-1.3-lemma
		 (a 2)
		 (b 2)))))

(defthm
  Subgoal-1.3
  (implies (and (integerp y)
		(integerp z)
		(not (equal y 1))
		(not (equal z 1))
		(>= y 0)
		(>= z 0))
	   (not (equal (* y z) 1)))
  :rule-classes nil
  :hints (("Goal"
	   :use subgoal-1.3-lemma-a)))

(in-theory (enable (:definition abs)))

(defthm
  Subgoal-1.1
  (implies (and (integerp y)
		(integerp z)
		(not (equal y 1))
		(not (equal z 1))
		(<= 0 y)
		(<= 0 z)
		(<= 1 (* y z)))
	   (equal (* (greatest-factor (* y z) (+ -1 (* y z)))
		     (divides-p$-witness (greatest-factor (* y z) (+ -1 (* y z)))
					 (* y z)))
		  (* y z)))
  :rule-classes nil
  :hints (("Subgoal 3"
	   :use (:instance
		 Greatest-factor->-1
		 (i (* y z))
		 (j (+ -1 (* y z)))))
	  ("Subgoal 1"
	   :in-theory (disable divides-p-greatest-factor)
	   :use (:instance
		 divides-p-greatest-factor
		 (x (* y z))
		 (y (+ -1 (* y z)))))))

(in-theory (disable (:definition divides-p$-witness)
		    (:definition unit-p)))

(in-theory (enable (:definition reducible-p$-witness)))

(defthm
  Reducible-p-suff
  (implies (and (integerp y)
		(integerp z)
		(not (unit-p y))
		(not (unit-p z))
		(equal (* y z) x))
	   (reducible-p x))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (equal (* y z) x)
				(integerp y)
				(integerp z)
				(not (unit-p y))
				(not (unit-p z)))
			   (reducible-p x))))
  :hints (("Subgoal 7.4"
	   :by Subgoal-7.4)
	  ("Subgoal 7.3"
	   :by Subgoal-7.3)
	  ("Subgoal 7.2"
	   :in-theory (enable (:definition divides-p$-witness)))
	  ("Subgoal 7.1"
	   :by Subgoal-7.1)
	  ("Subgoal 5.4"
	   :in-theory (enable (:definition divides-p$-witness)))
	  ("Subgoal 5.3"
	   :by Subgoal-5.3)
	  ("Subgoal 5.2"
	   :by Subgoal-5.2)
	  ("Subgoal 5.1"
	   :by Subgoal-5.1)
	  ("Subgoal 3.4"
	   :in-theory (enable (:definition divides-p$-witness)))
	  ("Subgoal 3.3"
	   :use (:instance
		 Subgoal-5.3
		 (y z)
		 (z y)))
	  ("Subgoal 3.2"
	   :use (:instance
		 Subgoal-5.2
		 (y z)
		 (z y)))
	  ("Subgoal 3.1"
	   :use (:instance
		 Subgoal-5.1
		 (y z)
		 (z y)))
; Modified by Matt K. in April 2016 due to type-set mod that added a bit for
; {1}.
	  ("Subgoal 1.3"
	   :by Subgoal-1.4)
	  ("Subgoal 1.2"
	   :by Subgoal-1.1)
	  ("Subgoal 1.1"
	   :in-theory (enable (:definition divides-p$-witness)))))

(in-theory (disable (:definition abs)
		    (:definition reducible-p$-witness)))

(defun
  Irreducible-p (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (not (unit-p x))
       (not (reducible-p x))))

(defthm
  Irreducible-p-implies-prime-property
  (implies (and (irreducible-p x)
		(integerp y)
		(integerp z)
		(divides-p x (* y z)))
	   (or (divides-p x y)
	       (divides-p x z)))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 acl2::Irreducible-p-implies-prime-property
		 (acl2::edp integerp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size abs)
		 (acl2::q_e truncate)
		 (acl2::r_e rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p$-witness)
		 (acl2::unit-p unit-p)
		 (acl2::reducible-p reducible-p)
		 (acl2::reducible-p-witness reducible-p$-witness)
		 (acl2::irreducible-p irreducible-p))
		(acl2::x x)
		(acl2::y y)
		(acl2::z z)))
	  ("Subgoal 3"
	   :in-theory (disable unit-p=_+1_or_-1
			       (:definition reducible-p)
			       (:definition divides-p)))
	  ("Subgoal 2"
	   :use (:instance
		 reducible-p-suff
		 (x acl2::x)
		 (y acl2::y)
		 (z acl2::z)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Factorization existence theory:

(defun
  Irreducible-factors (x)
  "Return a list, lst, of irreducible
   elements of integerp, so that if x is
   in integerp, x is not 0, and x is not
   an unit, then x = product of the
   members in lst."
  (declare (xargs :guard t
		  :measure (if (integerp x)
			       (abs x)
			       0)
		  :hints (("Subgoal 2"
			   :in-theory (disable (:definition mv-nth)
					       (:definition unit-p))
			   :use (:instance
				 abs-<-abs-*
				 (x (mv-nth 1 (reducible-p$-witness x)))
				 (y (mv-nth 0 (reducible-p$-witness x)))))
			  ("Subgoal 1"
			   :in-theory (disable (:definition mv-nth)
					       (:definition unit-p))
			   :use (:instance
				 abs-<-abs-*
				 (x (mv-nth 0 (reducible-p$-witness x)))
				 (y (mv-nth 1 (reducible-p$-witness x))))))))
  (cond ((or (not (integerp x))
	     (= x 0)
	     (= (abs x) 1))
	 nil)
	((reducible-p x)
	 (mv-let (y z)
		 (reducible-p$-witness x)
		 (append (irreducible-factors y)
			 (irreducible-factors z))))
	(t (list x))))

(defun
  Integerp-listp (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (and (integerp (car lst))
	   (integerp-listp (cdr lst)))
      t))

(defun
  Irreducible-listp (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (and (irreducible-p (car lst))
	   (irreducible-listp (cdr lst)))
      t))

(defun
  *-lst (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (if (integerp (car lst))
	  (* (car lst)(*-lst (cdr lst)))
	  0)
      1))

(defthm
  IRREDUCIBLE-FACTORIZATION-EXISTENCE
  (and (true-listp (irreducible-factors x))
       (integerp-listp  (irreducible-factors x))
       (irreducible-listp (irreducible-factors x))
       (implies (and (integerp x)
		     (not (equal x 0))
		     (not (unit-p x)))
		(equal (*-lst (irreducible-factors x)) x)))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 acl2::IRREDUCIBLE-FACTORIZATION-EXISTENCE
		 (acl2::edp integerp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size abs)
		 (acl2::q_e truncate)
		 (acl2::r_e rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p$-witness)
		 (acl2::unit-p unit-p)
		 (acl2::reducible-p reducible-p)
		 (acl2::reducible-p-witness reducible-p$-witness)
		 (acl2::irreducible-p irreducible-p)
		 (acl2::irreducible-factors irreducible-factors)
		 (acl2::irreducible-listp irreducible-listp)
		 (acl2::edp-listp integerp-listp)
		 (acl2::*_e-lst *-lst))
		(acl2::x x)))
	  ("Subgoal 3"
	   :in-theory (disable (:definition irreducible-p)))
	  ("Subgoal 1"
	   :in-theory (disable (:definition mv-nth)
			       (:definition reducible-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unit-associates-p theory:

;; (defun-sk
;;   unit-associates-p (x y)
;;   (exists u (if (and (integerp x)
;; 		     (integerp y))
;; 		(and (unit-p u)
;; 		     (equal (* u x)
;; 			    y))
;; 	        (equal x y))))

;; Computable Skolem function
(defun
  Unit-associates-p$-witness (x y)
  (declare (xargs :guard
		  (and (acl2-numberp x)
		       (acl2-numberp y))))
  (if (not (= x 0))
      (* y (/ x))
      1))

(defun
  Unit-associates-p (x y)
  (declare (xargs :guard
		  (and (acl2-numberp x)
		       (acl2-numberp y))))
  (let ((u (unit-associates-p$-witness x y)))
       (if (and (integerp x)
		(integerp y))
	   (and (unit-p u)
		(= (* u x) y))
	   (= x y))))

(defthm
  Unit-associates-p-suff
  (implies (if (and (integerp x)
		    (integerp y))
	       (and (unit-p u)
		    (equal (* u x) y))
	       (equal x y))
	   (unit-associates-p x y)))

(in-theory (disable (:definition Unit-associates-p$-witness)))

(defthm
  Irreducible-p-unit-associates
  (implies (and (divides-p x y)
		(not (unit-p x))
		(irreducible-p y))
	   (unit-associates-p x y))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  acl2::Irreducible-p-unit-associates
		  (acl2::edp integerp)
		  (acl2::=_e equal)
		  (acl2::C_=_e identity)
		  (acl2::binary-+_e binary-+)
		  (acl2::binary-*_e binary-*)
		  (acl2::-_e unary--)
		  (acl2::0_e (lambda () 0))
		  (acl2::1_e (lambda () 1))
		  (acl2::size abs)
		  (acl2::q_e truncate)
		  (acl2::r_e rem)
		  (acl2::divides-p divides-p)
		  (acl2::divides-p-witness divides-p$-witness)
		  (acl2::unit-p unit-p)
		  (acl2::reducible-p reducible-p)
		  (acl2::reducible-p-witness reducible-p$-witness)
		  (acl2::irreducible-p irreducible-p)
		  (acl2::unit-associates-p unit-associates-p)
		  (acl2::unit-associates-p-witness unit-associates-p$-witness))
		 (acl2::x x)
		 (acl2::y y)))
	  ("Subgoal 2"
	   :use (:instance
		 unit-associates-p-suff
		 (x acl2::x)
		 (y acl2::y)))
	  ("Subgoal 1"
	   :in-theory (disable unit-p=_+1_or_-1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unique factorization theory:

(defun
  acl2-number-listp (l)
  (declare (xargs :guard t))
  (if (consp l)
      (and (acl2-numberp (car l))
	   (acl2-number-listp (cdr l)))
      t))

(defun
  Member-unit-associate (x lst)
  "Determine if an unit-associate
   of x is a member of lst."
  (declare (xargs :guard (and (acl2-numberp x)
			      (acl2-number-listp lst))))
  (cond ((atom lst)
	 nil)
	((unit-associates-p x (car lst))
	 lst)
	(t (member-unit-associate x (cdr lst)))))

(defun
  Delete-one-unit-associate (x lst)
  "Return the result of deleting one occurrence
   of an unit-associate of x from the list lst."
  (declare (xargs :guard (and (acl2-numberp x)
			      (acl2-number-listp lst))))
  (if (consp lst)
      (if (unit-associates-p x (car lst))
	  (cdr lst)
	  (cons (car lst)(delete-one-unit-associate x (cdr lst))))
      lst))

(defun
  Bag-equal-unit-associates (lst1 lst2)
  "Return T iff lst1 and lst2 have the same
   members, up to unit-associates, with the
   same multiplicity, up to unit-associates."
  (declare (xargs :guard (and (acl2-number-listp lst1)
			      (acl2-number-listp lst2))))
  (if (consp lst1)
      (and (member-unit-associate (car lst1) lst2)
	   (bag-equal-unit-associates (cdr lst1)
				      (delete-one-unit-associate (car lst1)
								 lst2)))
      (atom lst2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Show that bag-equal-unit-associates has the expected properties:

;;  Lisp objects that are bag-equal-unit-associates have the same length.

;;  Lisp objects that are bag-equal-unit-associates have the same members.
;;       up to unit-associates.

;;  Elements in Lisp objects that are bag-equal-unit-associates occur
;;  in each object with the same multiplicity up to unit-associates.

(defthm
  Bag-equal-unit-associates->equal-len
  (implies (bag-equal-unit-associates lst1 lst2)
	   (equal (len lst1)
		  (len lst2)))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 acl2::Bag-equal-unit-associates->equal-len
		 (acl2::edp integerp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size abs)
		 (acl2::q_e truncate)
		 (acl2::r_e rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p$-witness)
		 (acl2::unit-p unit-p)
		 (acl2::unit-associates-p unit-associates-p)
		 (acl2::unit-associates-p-witness unit-associates-p$-witness)
		 (acl2::Member-unit-associate Member-unit-associate)
		 (acl2::Delete-one-unit-associate Delete-one-unit-associate)
		 (acl2::Bag-equal-unit-associates Bag-equal-unit-associates))
		(acl2::lst1 lst1)
		(acl2::lst2 lst2)))))

(defthm
  Bag-equal-unit-associates->iff-member-unit-associate
  (implies (bag-equal-unit-associates lst1 lst2)
	   (iff (member-unit-associate x lst1)
		(member-unit-associate x lst2)))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 acl2::Bag-equal-unit-associates->iff-member-unit-associate
		 (acl2::edp integerp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size abs)
		 (acl2::q_e truncate)
		 (acl2::r_e rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p$-witness)
		 (acl2::unit-p unit-p)
		 (acl2::unit-associates-p unit-associates-p)
		 (acl2::unit-associates-p-witness unit-associates-p$-witness)
		 (acl2::Member-unit-associate Member-unit-associate)
		 (acl2::Delete-one-unit-associate Delete-one-unit-associate)
		 (acl2::Bag-equal-unit-associates Bag-equal-unit-associates))
		(acl2::lst1 lst1)
		(acl2::lst2 lst2)))))

(defun
  Multiplicity-unit-associate (x lst)
  (declare (xargs :guard (and (acl2-numberp x)
			      (acl2-number-listp lst))))
  (if (consp lst)
      (if (unit-associates-p x (car lst))
	  (+ 1 (multiplicity-unit-associate x (cdr lst)))
	  (multiplicity-unit-associate x (cdr lst)))
      0))

(defthm
  Bag-equal-unit-associates->equal-multiplicity-unit-associate
  (implies (bag-equal-unit-associates lst1 lst2)
	   (equal (multiplicity-unit-associate x lst1)
		  (multiplicity-unit-associate x lst2)))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 acl2::Bag-equal-unit-associates->equal-multiplicity-unit-associate
		 (acl2::edp integerp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size abs)
		 (acl2::q_e truncate)
		 (acl2::r_e rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p$-witness)
		 (acl2::unit-p unit-p)
		 (acl2::unit-associates-p unit-associates-p)
		 (acl2::unit-associates-p-witness unit-associates-p$-witness)
		 (acl2::Member-unit-associate Member-unit-associate)
		 (acl2::Delete-one-unit-associate Delete-one-unit-associate)
		 (acl2::Bag-equal-unit-associates Bag-equal-unit-associates)
		 (acl2::Multiplicity-unit-associate Multiplicity-unit-associate))
		(acl2::x x)
		(acl2::lst1 lst1)
		(acl2::lst2 lst2)))))

(defthm
  IRREDUCIBLE-FACTORIZATION-UNIQUENESS-general
  (implies (and (irreducible-listp lst1)
		(irreducible-listp lst2)
		(unit-associates-p (*-lst lst1)
				   (*-lst lst2)))
	  (bag-equal-unit-associates lst1 lst2))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 acl2::IRREDUCIBLE-FACTORIZATION-UNIQUENESS-general
		 (acl2::edp integerp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size abs)
		 (acl2::q_e truncate)
		 (acl2::r_e rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p$-witness)
		 (acl2::unit-p unit-p)
		 (acl2::reducible-p reducible-p)
		 (acl2::reducible-p-witness reducible-p$-witness)
		 (acl2::irreducible-p irreducible-p)
		 (acl2::irreducible-listp irreducible-listp)
		 (acl2::*_e-lst *-lst)
		 (acl2::unit-associates-p unit-associates-p)
		 (acl2::unit-associates-p-witness unit-associates-p$-witness)
		 (acl2::Member-unit-associate Member-unit-associate)
		 (acl2::Delete-one-unit-associate Delete-one-unit-associate)
		 (acl2::Bag-equal-unit-associates Bag-equal-unit-associates))
		(acl2::lst1 lst1)
		(acl2::lst2 lst2)))))

(defthm
  IRREDUCIBLE-FACTORIZATION-UNIQUENESS
  (implies (and (irreducible-listp lst1)
		(irreducible-listp lst2)
		(equal (*-lst lst1)
		       (*-lst lst2)))
	  (bag-equal-unit-associates lst1 lst2))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 acl2::IRREDUCIBLE-FACTORIZATION-UNIQUENESS
		 (acl2::edp integerp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size abs)
		 (acl2::q_e truncate)
		 (acl2::r_e rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p$-witness)
		 (acl2::unit-p unit-p)
		 (acl2::reducible-p reducible-p)
		 (acl2::reducible-p-witness reducible-p$-witness)
		 (acl2::irreducible-p irreducible-p)
		 (acl2::irreducible-listp irreducible-listp)
		 (acl2::*_e-lst *-lst)
		 (acl2::unit-associates-p unit-associates-p)
		 (acl2::unit-associates-p-witness unit-associates-p$-witness)
		 (acl2::Member-unit-associate Member-unit-associate)
		 (acl2::Delete-one-unit-associate Delete-one-unit-associate)
		 (acl2::Bag-equal-unit-associates Bag-equal-unit-associates))
		(acl2::lst1 lst1)
		(acl2::lst2 lst2)))))
