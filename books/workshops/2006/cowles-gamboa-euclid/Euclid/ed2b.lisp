; ACL2 Euclidean Domain books -- Book 2b -- CounterExample.
;   The Integers (with an unusual Size function) are shown
;   to be an Euclidean Domain without the Multiplicative
;   Size Property. Here Quotient is round and Remainder is
;   rnd-rem, a version of rem using round in place of truncate.
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

#|
To certify this book:

(certify-book "ed2b")
|#
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
;; (2) multiplications distributes over addition,
;; (3) zero is an identity for addition, and
;; (4) minus produces an additive inverse

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Every Euclidean Domain has a multiplicative identity.
;;   See Book 1 of ACL2 Euclidean Domain books, ed1.lisp, for a proof.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; In the ACL2 Euclidean Book, ed2a.lisp, it is shown that there is no
;;  loss of generality in assuming Multiplicative Size Property:

;;     For all nonzero domain elements x and y, Size(x) <= Size(xy).

;;     If the original Size function does not satisfy this property,
;;     then it can replaced by another that does satisfy this and the
;;     division property.

;; Below an example is verified of an Euclidean Doamin (with multiplicative
;; identity) that does NOT satisfy the Multiplicative Size Property given
;; above.
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
;;  abs-3     ; Natp size of each nonzero Euclidean Domain element.
;;  round     ; Quotient in Euclidean Domain.
;;  rnd-rem   ; Remainder in Euclidean Domain.

;;  Here abs-3 and rnd-rem are defined for integers x and nonzero
;;    integers y by

;;    (abs-3 x) = (if (equal x 3)
;;                    2
;;                    (abs x))

;;    (rnd-rem x y) = (- x (* y (round x y)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Make temporary use of an ACL2 Arithmetic Book and a book containing facts
;  about FLOOR and MOD to help certify this book

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
 (in-theory (disable quotient-remainder-functions)))

(defthm
  Round-as-floor-&-ceiling
  (implies (and (integerp x)
		(integerp y)
		(not (equal y 0)))
	   (equal (round x y)
		  (let ((q (* x (/ y))))
		       (cond ((integerp q)
			      q)
			     ((>= q 0)
			      (cond ((> (- q (floor x y)) 1/2)
				     (ceiling x y))
				    ((< (- q (floor x y)) 1/2)
				     (floor x y))
				    (t (if (integerp (* (floor x y)(/ 2)))
					   (floor x y)
					   (ceiling x y)))))
			     (t
			      (cond ((< (- 1/2)(- q (ceiling x y)))
				     (ceiling x y))
				    ((> (- 1/2)(- q (ceiling x y)))
				     (floor x y))
				    (t (if (integerp (* (ceiling x y)(/ 2)))
					   (ceiling x y)
					   (floor x y)))))))))
  :hints (("Goal"
	   :in-theory (enable (:definition floor)))))

(in-theory (disable (:definition round)))

(defthm
  Ceiling-as-floor
  (implies (and (integerp x)
		(integerp y)
		(not (equal y 0)))
	   (equal (ceiling x y)
		  (if (integerp (* x (/ y)))
		      (floor x y)
		      (+ 1 (floor x y)))))
  :hints (("Goal"
	   :in-theory (enable (:definition floor)))))

(in-theory (disable (:definition ceiling)))

;; AXIOMS
;; Integral Domain Axioms:
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
   (implies (and (integerp y1)
		 (integerp y2)
		 (equal y1 y2))
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
			(- y2))))
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

;; Euclidean Domain Defintions and Axioms:
(defun
  abs-3 (x)
  (declare (xargs :guard
		  (real/rationalp x)))
  (if (= x 3)
      2
      (abs x)))

(defun
  rnd-rem (x y)
  (declare (xargs :guard
		  (and (real/rationalp x)
		       (real/rationalp y)
		       (not (eql y 0)))))
  (- x (* y (round x y))))

(defthm
  Natp-abs-3
  (implies (and (integerp x)
		(not (equal x 0)))
	   (and (integerp (abs-3 x))
		(>= (abs-3 x) 0)))
  :rule-classes ((:type-prescription
		  :corollary
		  (implies (integerp x)
			   (and (integerp (abs-3 x))
				(>= (abs-3 x) 0))))
		 (:linear
		  :corollary
		  (implies (and (integerp x)
				(not (equal x 0)))
			   (> (abs-3 x) 0)))))

(defthm
  Congruence-for-Abs-3
  (implies (and (integerp y1)
		(integerp y2)
		(equal y1 y2))
	   (equal (abs-3 y1)
		  (abs-3 y2)))
  :rule-classes nil)

(defthm
  Closure-of-round-&-rnd-rem
  (implies (and (integerp x)
		(integerp y)
		(not (equal y 0)))
	   (and (integerp (round x y))
		(integerp (rnd-rem x y))))
  :rule-classes nil)

(defthm
  Congruence-for-round-&-rnd-rem
  (implies (and (integerp y1)
		(integerp y2)
		(equal y1 y2))
	   (and (implies (and (integerp x)
			      (not (equal y1 0)))
			 (and (equal (round x y1)
				     (round x y2))
			      (equal (rnd-rem x y1)
				     (rnd-rem x y2))))
		(implies (and (integerp z)
			      (not (equal z 0)))
			 (and (equal (round y1 z)
				     (round y2 z))
			      (equal (rnd-rem y1 z)
				     (rnd-rem y2 z))))))
  :rule-classes nil)

(defthm
  Division-property
  (implies (and (integerp x)
		(integerp y)
		(not (equal y 0)))
	   (and (equal x (+ (* y (round x y))
			    (rnd-rem x y)))
		(or (equal (rnd-rem x y) 0)
		    (< (abs-3 (rnd-rem x y))
		       (abs-3 y)))))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Violation of Multiplicative Size Property:

;; The following is false.
;;  Multiplicative Size Property
;;   (implies (and (integerp x)
;;                 (not (equal x 0))
;;                 (integerp y)
;;                 (not (equal y 0)))
;;            (<= (abs-3 x)
;;                (abs-3 (* x y))))

;; Let x = -3 and y = -1.
;;     Then (abs-3 -3) = 3 > 2 = (abs-3 (* -3 -1)).
(defthm
  COUNTER-EXAMPLE
  (let ((x -3)
	(y -1))
       (equal (implies (and (integerp x)
			    (not (equal x 0))
			    (integerp y)
			    (not (equal y 0)))
		       (<= (abs-3 x)
			   (abs-3 (* x y))))
	      nil))
  :rule-classes nil)
