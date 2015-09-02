; ACL2 Euclidean Domain books -- Book 5aa -- Example: Gaussian Integers.
;  The Gaussian Integers, complex numbers with integer real and imaginary
;  parts, are shown to be an Euclidean Domain with unique factorization.
;  Here Size is sqr-abs, the square of complex abs; Quotient is based on
;  rounding the real and imaginary parts of the complex quotient and
;  Remainder is a version of rem using the above rounding in place of
;  truncate.

;  This version uses quantifiers (defun-sk) and is
;  non-exedutable.

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

(defpkg "GAUSS-INT"
  (set-difference-eq (union-eq
                      *acl2-exports*
                      *common-lisp-symbols-from-main-lisp-package*)
; Subtracted 12/4/2012 by Matt K. for addition to *acl2-exports* ; ; ;
                     '(nat-listp acl2-number-listp)))

   (certify-book "ed5aa"
                 1
		 nil ;;compile-flg
 		 )
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The Gaussian Integers are an Euclidean Doamin:

;;  Gauss-intp    ; Predicate for set of Euclidean Domain elements.
;;  equal         ; Equality predicate for Euclidean Domain elements.
;;  identity      ; Choose unique equivalence class representative for equal.
;;  +             ; Addition in Euclidean Domain.
;;  *             ; Multiplication in Euclidean Domain.
;;  -             ; Unary minus in Euclidean Domain.
;;  0             ; 0 element in Euclidean Domain.
;;  1             ; 1 element in Euclidean Domain.
;;  sq-abs        ; Natp size of each nonzero Euclidean Domain element.
;;  rnd-parts     ; Quotient in Euclidean Domain.
;;  rnd-parts-rem ; Remainder in Euclidean Domain.

;;   Here Gauss-intp is defined by

;; (Gauss-intp x) = (and (acl2-numberp x)
;;                       (integerp (realpart x))
;;                       (integerp (imagpart x)))

;;  Sq-abs, rnd-parts, and rnd-parts-rem are defined for Gaussian
;;   integers x and nonzero Gaussian integers y by

;; (sq-abs x) = (+ (* (realpart x)(realpart x))
;;                 (* (imagpart x)(imagpart x)))

;;  (rnd-parts x y) = (complex (round (numerator (realpart (* x (/ y))))
;;                                    (denominator (realpart (* x (/ y)))))
;;                             (round (numerator (imagpart (* x (/ y))))
;;                                    (denominator (imagpart (* x (/ y))))))

;; (rnd-parts-rem x y) = (- x (* y (rnd-parts x y)))
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

;;  In fact, for Gaussian integers x and y,
;;                (sq-abs (* x y)) = (* (sq-abs x)(sq-abs y)).
;;   So, if Gaussian integer y differs from 0, then (<= 1 (sq-abs y));
;;   then for any Gaussian integer x, (sq-abs x)  = (* (sq-abs x) 1)
;;                                               <= (* (sq-abs x)(abs y))
;;                                                = (sq-abs (* x y)).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "GAUSS-INT")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Make temporary use of an ACL2 Arithmetic Book and a book containing facts
;  about FLOOR and MOD to help certify this book

; cert_param: (non-acl2r)

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

(defthm
  Round-bounds
  (implies (and (integerp x)
		(integerp y)
		(not (equal y 0)))
	   (and (<= (round x y)(+  1/2 (* x (/ y))))
		(>= (round x y)(+ -1/2 (* x (/ y))))))
  :rule-classes ((:linear
		  :trigger-terms ((round x y)))))

(defthm
  Round-bounds-1
  (implies (rationalp r)
	   (and (<= (- r (round (numerator r)
				(denominator r)))
		    1/2)
		(>= (- r (round (numerator r)
				(denominator r)))
		    -1/2)))
  :rule-classes :linear)

(defthm
  Round-bounds-2-lemma-1
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(>= x 0)
		(> y 0)
		(<= x y))
	   (<= (* x x)(* y y)))
  :rule-classes nil)

(defthm
  Round-bounds-2-lemma-2
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(< y 0)
		(>= x y))
	   (<= (* x x)(* y y)))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:theorem
		  (implies (and (real/rationalp x)
				(real/rationalp y)
				(< x 0)
				(< y 0)
				(>= x y))
			   (<= (* x x)(* x y))))
		 (:theorem
		  (implies (and (real/rationalp x)
				(real/rationalp y)
				(< x 0)
				(< y 0)
				(>= x y))
			   (<= (* x y)(* y y))))))
	  ("subgoal 3"
	   :in-theory (disable acl2::<-*-left-cancel
			       acl2::<-*-right-cancel))))

(defthm
  Round-bounds-2-lemma-3
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(> y 0)
		(<= x y)
		(<= (- y) x))
	   (<= (* x x)(* y y)))
  :rule-classes nil
  :hints (("Goal"
	   :use (round-bounds-2-lemma-1
		 (:instance
		  round-bounds-2-lemma-2
		  (y (- y)))))))

(defthm
  Round-bounds-2
  (implies (rationalp r)
	   (<= (* (- r (round (numerator r)
			      (denominator r)))
		  (- r (round (numerator r)
			      (denominator r))))
	       1/4))
  :rule-classes :linear
  :hints (("Goal"
	   :in-theory (disable round-as-floor-&-ceiling)
	   :use (:instance
		 Round-bounds-2-lemma-3
		 (x  (- r (round (numerator r)
				 (denominator r))))
		 (y 1/2)))))

(defthm
  Minus-def-complex
  (equal (- x)
	 (complex (- (realpart x))
		  (- (imagpart x))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  complex-definition
		  (acl2::x (realpart x))
		  (acl2::y (imagpart x)))
		 (:instance
		  complex-definition
		  (acl2::x (- (realpart x)))
		  (acl2::y (- (imagpart x))))))))

(defthm
  Realpart--
  (equal (realpart (- x))
	 (- (realpart x)))
  :hints (("Goal"
	   :use minus-def-complex)))

(defthm
  Imagpart--
  (equal (imagpart (- x))
	 (- (imagpart x)))
  :hints (("Goal"
	   :use minus-def-complex)))

(defthm
  Mult-def-complex
  (equal (* x y)
         (complex (- (* (realpart x)(realpart y))
		     (*	(imagpart x)(imagpart y)))
                  (+ (* (realpart x)(imagpart y))
		     (* (imagpart x)(realpart y)))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  complex-definition
		  (acl2::x (- (* (realpart x)(realpart y))
			      (* (imagpart x)(imagpart y))))
		  (acl2::y (+ (* (realpart x)(imagpart y))
			      (* (imagpart x)(realpart y)))))
		 (:instance
		  complex-definition
		  (acl2::x (realpart x))
		  (acl2::y (imagpart x)))
		 (:instance
		  complex-definition
		  (acl2::x (realpart y))
		  (acl2::y (imagpart y)))))))

(defthm
  Realpart-*
  (equal (realpart (* x y))
	 (- (* (realpart x)(realpart y))
	    (* (imagpart x)(imagpart y))))
  :hints (("Goal"
	   :use mult-def-complex)))

(defthm
  Imagpart-*
  (equal (imagpart (* x y))
         (+ (* (realpart x)(imagpart y))
	    (* (imagpart x)(realpart y))))
  :hints (("Goal"
	   :use mult-def-complex)))

(defthm
  Simple-algebra
  (implies (and (rationalp r)
		(rationalp r0)
		(or (not (equal r 0))
		    (not (equal r0 0))))
	   (equal (+ (* r r (/ (+ (* r r) (* r0 r0))))
		     (* r0 r0 (/ (+ (* r r) (* r0 r0)))))
		  1))
  :rule-classes nil
  :hints (("goal"
	  :in-theory (disable distributivity)
	  :use (:instance
		distributivity
		(acl2::x (/ (+ (* r r) (* r0 r0))))
		(acl2::y (* r r))
		(acl2::z (* r0 r0))))))

(defthm
  Simple-algebra-1
  (implies (and (rationalp r)
		(rationalp r0)
		(or (not (equal r 0))
		    (not (equal r0 0))))
	   (equal (* (+ r (* #c(0 1) r0))
		     (+ (* r (/ (+ (* r r) (* r0 r0))))
			(- (* #c(0 1) r0 (/ (+ (* r r) (* r0 r0)))))))
		  1))
  :rule-classes nil
  :hints (("goal"
	   :use (simple-algebra
		 (:instance
		  (:theorem
		   (equal (* (+ a b)
			     (+ c d))
			  (+ (* a c)
			     (* a d)
			     (* b c)
			     (* b d))))
		  (a r)
		  (b (* #c(0 1) r0))
		  (c (* r (/ (+ (* r r) (* r0 r0)))))
		  (d (- (* #c(0 1) r0 (/ (+ (* r r) (* r0 r0)))))))))))

(defthm
  Recipical-def-complex
  (implies (not (equal x 0))
	   (equal (/ x)
		  (complex (* (realpart x)(/ (+ (* (realpart x)
						   (realpart x))
						(* (imagpart x)
						   (imagpart x)))))
			   (* (- (imagpart x))(/ (+ (* (realpart x)
						       (realpart x))
						    (* (imagpart x)
						       (imagpart x))))))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  complex-definition
		  (acl2::x (realpart x))
		  (acl2::y (imagpart x)))
		 (:instance
		  complex-definition
		  (acl2::x (* (realpart x)(/ (+ (* (realpart x)
						   (realpart x))
						(* (imagpart x)
						   (imagpart x))))))
		  (acl2::y (* (- (imagpart x))(/ (+ (* (realpart x)
						       (realpart x))
						    (* (imagpart x)
						       (imagpart x)))))))))
	  ("Subgoal 1"
	   :use simple-algebra-1)))

(defthm
  Realpart-/
  (implies (not (equal x 0))
	   (equal (realpart (/ x))
		  (* (realpart x)(/ (+ (* (realpart x)
					  (realpart x))
				       (* (imagpart x)
					  (imagpart x)))))))
  :hints (("Goal"
	   :in-theory (disable acl2::equal-/)
	   :use recipical-def-complex)))

(defthm
  Imagpart-/
  (implies (not (equal x 0))
	   (equal (imagpart (/ x))
		  (* (- (imagpart x))(/ (+ (* (realpart x)
					      (realpart x))
					   (* (imagpart x)
					      (imagpart x)))))))
  :hints (("Goal"
	   :in-theory (disable acl2::equal-/)
	   :use recipical-def-complex)))

;; AXIOMS
;;; Integral Domain Axioms:

(defun ;;===================
  Gauss-intp (x)
  (declare (xargs :guard t))
  (and (acl2-numberp x)
       (integerp (realpart x))
       (integerp (imagpart x))))

(defthm ;;===================
  Closure-Laws
  (and (implies (gauss-intp x)
		(and (implies (gauss-intp y)
			      (and (gauss-intp (+ x y))
				   (gauss-intp (* x y))))
		     (gauss-intp (- x))))
       (gauss-intp 0)
       (gauss-intp 1))
  :rule-classes nil)

(defthm ;;===================
  Equivalence-Law
  (implies (gauss-intp x)
	   (and (equal x x)
		(implies (gauss-intp y)
			 (and (booleanp (equal x y))
			      (implies (equal x y)
				       (equal y x))
			      (implies (gauss-intp z)
				       (implies (and (equal x y)
						     (equal y z))
						(equal x z)))))))
  :rule-classes nil)

(defthm ;;===================
  Congruence-Laws
  (implies (equal y1 y2)
	   (and (iff (gauss-intp y1)
		     (gauss-intp y2))
		(implies (and (gauss-intp y1)
			      (gauss-intp y2))
			 (and (implies (gauss-intp x)
				       (and (equal (+ x y1)
						   (+ x y2))
					    (equal (* x y1)
						   (* x y2))))
			      (implies (gauss-intp z)
				       (and (equal (+ y1 z)
						   (+ y2 z))
					    (equal (* y1 z)
						   (* y2 z))))
			      (equal (- y1)
				     (- y2))))))
  :rule-classes nil)

(defthm ;;=====================
  Closure-of-identity
  (implies (gauss-intp x)
	   (gauss-intp (identity x)))
  :rule-classes nil)

(defthm ;;=====================
  Equivalence-class-Laws
  (and (implies (gauss-intp x)
		(equal (identity x) x))
       (implies (and (gauss-intp y1)
		     (gauss-intp y2)
		     (equal y1 y2))
		(equal (identity y1)
		       (identity y2))))
  :rule-classes nil)

(defthm ;;=====================
  Commutativity-Laws
  (implies (and (gauss-intp x)
		(gauss-intp y))
	   (and (equal (+ x y)
		       (+ y x))
		(equal (* x y)
		       (* y x))))
  :rule-classes nil)

(defthm ;;====================
  Associativity-Laws
  (implies (and (gauss-intp x)
		(gauss-intp y)
		(gauss-intp z))
	   (and (equal (+ (+ x y) z)
		       (+ x (+ y z)))
		(equal (* (* x y) z)
		       (* x (* y z)))))
  :rule-classes nil)

(defthm ;;================
  Left-Distributivity-Law
  (implies (and (gauss-intp x)
		(gauss-intp y)
		(gauss-intp z))
	   (equal (* x (+ y z))
		  (+ (* x y)
		       (* x z))))
  :rule-classes nil)

(defthm ;;================
  Left-Unicity-Laws
  (implies (gauss-intp x)
	   (and (equal (+ 0 x)
		       x)
		(equal (* 1 x)
		       x)))
  :rule-classes nil)

(defthm ;;=================
  Right-Inverse-Law
  (implies (gauss-intp x)
	   (equal (+ x (- x))
		  0))
  :rule-classes nil)

(defthm ;;===================
  Zero-Divisor-Law
  (implies (and (gauss-intp x)
		(gauss-intp y))
	   (equal (equal (* x y) 0)
		  (or (equal x 0)
		      (equal y 0))))
  :rule-classes nil)

;; Euclidean Domain Axioms:

(defun ;;==================
  Sq-abs (x)
  (declare (xargs :guard
		  (acl2-numberp x)))
  (let ((r (realpart x))
	(i (imagpart x)))
       (+ (* r r)(* i i))))

(defthm  ;;==================
  Natp-sq-abs
  (implies (and (gauss-intp x)
		(not (equal x 0)))
	   (and (integerp (sq-abs x))
		(>= (sq-abs x) 0)))
  :rule-classes ((:type-prescription
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (imagpart x)))
			   (and (integerp (sq-abs x))
				(>= (sq-abs x) 0))))
		 (:linear
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (imagpart x))
				(not (equal x 0)))
			   (> (sq-abs x) 0)))))

(defthm ;;==================
  Congruence-for-abs
  (implies (and (gauss-intp y1)
		(gauss-intp y2)
		(equal y1 y2))
	   (equal (sq-abs y1)
		  (sq-abs y2)))
  :rule-classes nil)

(defthm
  Sq-abs-*-equality
  (equal (sq-abs (* x y))
	 (* (sq-abs x)
	    (sq-abs y))))

(defun ;;======================
  Rnd-parts (x y)
  (declare (xargs :guard
		  (and (acl2-numberp x)
		       (acl2-numberp y)
		       (not (equal y 0)))))
  (let* ((q (* x (/ y)))
	 (r (realpart q))
	 (i (imagpart q)))
        (if (and (integerp r)
		 (integerp i))
	    q
	    (complex (round (numerator r)
			    (denominator r))
		     (round (numerator i)
			    (denominator i))))))

(defun ;;=========================
  Rnd-parts-rem (x y)
  (declare (xargs :guard
		  (and (acl2-numberp x)
		       (acl2-numberp y)
		       (not (equal y 0)))))
  (- x (* y (rnd-parts x y))))

(defthm
  Closure-of-rnd-parts
  (implies (and (gauss-intp x)
		(gauss-intp y)
		(not (equal y 0)))
	   (gauss-intp (rnd-parts x y)))
  :rule-classes ((:type-prescription
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (imagpart x))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (imagpart y))
				(not (equal y 0)))
			   (integerp (realpart (rnd-parts x y))))
		  :hints (("Goal"
			   :in-theory (disable (:definition rnd-parts)))))
		 (:type-prescription
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (imagpart x))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (imagpart y))
				(not (equal y 0)))
			   (integerp (imagpart (rnd-parts x y))))
		  :hints (("Goal"
			   :in-theory (disable (:definition rnd-parts)))))))

(defthm
  Closure-of-rnd-parts-rem
  (implies (and (gauss-intp x)
		(gauss-intp y)
		(not (equal y 0)))
	   (gauss-intp (rnd-parts-rem x y)))
  :rule-classes ((:type-prescription
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (imagpart x))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (imagpart y))
				(not (equal y 0)))
			   (integerp (realpart (rnd-parts-rem x y))))
		  :hints (("Goal"
			   :in-theory (disable (:definition rnd-parts-rem)))))
		 (:type-prescription
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (imagpart x))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (imagpart y))
				(not (equal y 0)))
			   (integerp (imagpart (rnd-parts-rem x y))))
		  :hints (("Goal"
			   :in-theory (disable (:definition rnd-parts-rem))))))
  :hints (("Goal"
	   :in-theory (disable (:definition rnd-parts)))))

(defthm ;;===========================
  Closure-of-rnd-parts-&-rnd-parts-rem
  (implies (and (gauss-intp x)
		(gauss-intp y)
		(not (equal y 0)))
	   (and (gauss-intp (rnd-parts x y))
		(gauss-intp (rnd-parts-rem x y))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition rnd-parts)
			       (:definition rnd-parts-rem)))))

(defthm ;;===========================
  Congruence-for-rnd-parts-&-rnd-parts-rem
  (implies (and (gauss-intp y1)
		(gauss-intp y2)
		(equal y1 y2))
	   (and (implies (and (gauss-intp x)
			      (not (equal y1 0)))
			 (and (equal (rnd-parts x y1)
				     (rnd-parts x y2))
			      (equal (rnd-parts-rem x y1)
				     (rnd-parts-rem x y2))))
		(implies (and (gauss-intp z)
			      (not (equal z 0)))
			 (and (equal (rnd-parts y1 z)
				     (rnd-parts y2 z))
			      (equal (rnd-parts-rem y1 z)
				     (rnd-parts-rem y2 z))))))
  :rule-classes nil)

(defthm
  Division-property-equation
  (implies (and (gauss-intp x)
		(gauss-intp y)
		(not (equal y 0)))
	   (equal x (+ (* y (rnd-parts x y))
		       (rnd-parts-rem x y))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (imagpart x))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (imagpart y))
				(not (equal y 0)))
			   (equal (+ (rnd-parts-rem x y)
				     (* y (rnd-parts x y)))
				  x))
		  :hints (("Goal"
			   :in-theory (disable (:definition rnd-parts)
					       (:definition rnd-parts-rem))))))
  :hints (("Goal"
	   :in-theory (disable (:definition rnd-parts)))))

(defthm
  Rnd-parts-rem-equality
  (implies (and (acl2-numberp y)
		(not (equal y 0)))
	   (equal (rnd-parts-rem x y)
		  (* y (- (* x (/ y))
			  (rnd-parts x y)))))
  :rule-classes nil)

(defthm
  Sq-abs-rnd-parts-rem-equality
  (implies (and (acl2-numberp y)
		(not (equal y 0)))
	   (equal (sq-abs (rnd-parts-rem x y))
		  (* (sq-abs y)
		     (sq-abs (- (* x (/ y))
				(rnd-parts x y))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition sq-abs)
			       (:definition rnd-parts)
			       (:definition rnd-parts-rem)
			       Sq-abs-*-equality)
	   :use (rnd-parts-rem-equality
		 (:instance
		  Sq-abs-*-equality
		  (x y)
		  (y (- (* x (/ y))
			(rnd-parts x y))))))))

(defthm
  Realpart-rnd-parts-inequality
  (<= (* (realpart (- (* x (/ y))
		      (rnd-parts x y)))
	 (realpart (- (* x (/ y))
		      (rnd-parts x y))))
      1/4)
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable round-as-floor-&-ceiling)
	   :use (:instance
		 Round-bounds-2
		 (r (realpart (* x (/ y))))))))

(defthm
  Imagpart-rnd-parts-inequality
  (<= (* (imagpart (- (* x (/ y))
		      (rnd-parts x y)))
	 (imagpart (- (* x (/ y))
		      (rnd-parts x y))))
      1/4)
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable round-as-floor-&-ceiling)
	   :use (:instance
		 Round-bounds-2
		 (r (imagpart (* x (/ y))))))))

(defthm
  Sq-abs-rnd-parts-inequality
  (<= (sq-abs (- (* x (/ y))
		 (rnd-parts x y)))
      1/2)
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition rnd-parts))
	   :use (realpart-rnd-parts-inequality
		 imagpart-rnd-parts-inequality))))

(defthm
  Sq-abs-rnd-parts-rem-inequality
  (implies (and (acl2-numberp y)
		(not (equal y 0)))
	   (<= (sq-abs (rnd-parts-rem x y))
	       (* 1/2 (sq-abs y))))
  :rule-classes :linear
  :hints (("Goal"
	   :in-theory (disable (:definition sq-abs)
			       (:definition rnd-parts)
			       (:definition rnd-parts-rem))
	   :use (Sq-abs-rnd-parts-rem-equality
		 Sq-abs-rnd-parts-inequality
		 (:instance
		  (:theorem
		   (implies (and (rationalp x)
				 (rationalp y)
				 (rationalp z)
				 (<= x y)
				 (>= z 0))
			    (<= (* x z)(* y z))))
		  (x (sq-abs (- (* x (/ y))
				(rnd-parts x y))))
		  (y 1/2)
		  (z (sq-abs y)))))))

(defthm
  Sq-abs-=-0
  (implies (acl2-numberp y)
	   (equal (equal (sq-abs y) 0)
		  (equal y 0))))

(defthm
  Division-property-inequality
  (implies (and (acl2-numberp y)
		(not (equal y 0)))
	   (< (sq-abs (rnd-parts-rem x y))
	      (sq-abs y)))
  :rule-classes :linear
  :hints (("Goal"
	   :in-theory (disable (:definition sq-abs)
			       (:definition rnd-parts)
			       (:definition rnd-parts-rem)))))

(defthm ;;==================
  Division-property
  (implies (and (gauss-intp x)
		(gauss-intp y)
		(not (equal y 0)))
	   (and (equal x (+ (* y (rnd-parts x y))
			    (rnd-parts-rem x y)))
		(or (equal (rnd-parts-rem x y) 0)
		    (< (sq-abs (rnd-parts-rem x y))
		       (sq-abs y)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition sq-abs)
			       (:definition rnd-parts)
			       (:definition rnd-parts-rem)))))

(defthm ;;==========================
  Sq-abs-*
  (implies (and (gauss-intp x)
		(not (equal x 0))
		(gauss-intp y)
		(not (equal y 0)))
	   (<= (sq-abs x)
	       (sq-abs (* x y))))
  :rule-classes ((:linear
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (imagpart x))
				(not (equal x 0))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (imagpart y))
				(not (equal y 0)))
			   (<= (sq-abs x)
			       (sq-abs (* x y))))
		  :hints (("Goal"
			   :in-theory (disable (:definition sq-abs)))))
		 (:rewrite
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (imagpart x))
				(not (equal x 0))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (imagpart y))
				(not (equal y 0)))
			   (<= (sq-abs x)
			       (sq-abs (* x y))))
		  :hints (("Goal"
			   :in-theory (disable (:definition sq-abs))))))
  :hints (("Goal"
	   :in-theory (disable (:definition sq-abs))
	   :use ((:instance
		  (:theorem
		   (implies (and (integerp x)
				 (> x 0)
				 (integerp y)
				 (> y 0))
			    (<= x (* x y))))
		  (x (sq-abs x))
		  (y (sq-abs y)))))))

(in-theory (disable (:definition sq-abs)
		    (:definition rnd-parts)
		    (:definition rnd-parts-rem)))

;;;;;;;;;;;;;;;;;;;;
;; Divides-p theory:

(defun-sk
  Divides-p (x y)
  (exists z (and (gauss-intp x)
		 (gauss-intp z)
		 (equal (* x z)
			y))))

(defthm
  Divides-p-suff-rewrite
  (implies (and (acl2-numberp x)
		(integerp (realpart x))
		(integerp (imagpart x))
		(acl2-numberp z)
		(integerp (realpart z))
		(integerp (imagpart z))
		(equal (* x z) y))
	   (divides-p x y))
  :hints (("goal"
	   :use divides-p-suff)))

;;;;;;;;;;;;;;;;;
;; Unit-p theory:

(defun
  unit-p (x)
  (divides-p x 1))

(defthm
  Sq-abs-unit-p=1
  (implies (unit-p x)
	   (equal (sq-abs x)
		  1))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable sq-abs-*-equality
			       realpart-imagpart-elim)
	   :use (:instance
		 (:functional-instance
		  acl2::Size-unit-p=Size-1_e
		  (acl2::edp gauss-intp)
		  (acl2::=_e equal)
		  (acl2::C_=_e identity)
		  (acl2::binary-+_e binary-+)
		  (acl2::binary-*_e binary-*)
		  (acl2::-_e unary--)
		  (acl2::0_e (lambda () 0))
		  (acl2::1_e (lambda () 1))
		  (acl2::size sq-abs)
		  (acl2::q_e rnd-parts)
		  (acl2::r_e rnd-parts-rem)
		  (acl2::divides-p divides-p)
		  (acl2::divides-p-witness divides-p-witness)
		  (acl2::unit-p unit-p))
		 (acl2::x x)))))

(defthm
  Sq-abs=1-implies-unit-p
  (implies (and (gauss-intp x)
		(not (equal x 0))
		(equal (sq-abs x)
		       1))
	   (unit-p x))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  acl2::Size=Size-1_e-implies-unit-p
		  (acl2::edp gauss-intp)
		  (acl2::=_e equal)
		  (acl2::C_=_e identity)
		  (acl2::binary-+_e binary-+)
		  (acl2::binary-*_e binary-*)
		  (acl2::-_e unary--)
		  (acl2::0_e (lambda () 0))
		  (acl2::1_e (lambda () 1))
		  (acl2::size sq-abs)
		  (acl2::q_e rnd-parts)
		  (acl2::r_e rnd-parts-rem)
		  (acl2::divides-p divides-p)
		  (acl2::divides-p-witness divides-p-witness)
		  (acl2::unit-p unit-p))
		 (acl2::x x)))))

(defthm
  Sq-abs->-1
  (implies (and (integerp (realpart x))
		(not (equal (realpart x) 0))
		(integerp (imagpart x))
		(not (equal (imagpart x) 0)))
	  (> (sq-abs x) 1))
  :rule-classes :linear
  :hints (("Goal"
	   :in-theory (enable sq-abs))))

(defthm
  Sq-abs->-1-a
  (and (implies (> (realpart x) 1)
		(> (sq-abs x) 1))
       (implies (> (imagpart x) 1)
		(> (sq-abs x) 1)))
  :rule-classes :linear
  :hints (("Goal"
	   :in-theory (enable sq-abs))))

(defthm
  Sq-abs->-1-b-lemma
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x y)
		(< y 0))
	   (> (* x x)(* y y)))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:theorem
		  (implies (and (rationalp x)
				(rationalp y)
				(< 0 x)
				(< x y))
			   (< (* x x)(* y y))))
		 (x (- y))
		 (y (- x))))))

(defthm
  Sq-abs->-1-b-lemma-1
  (implies (and (real/rationalp x)
		(< x -1))
	   (< 1 (* x x)))
  :rule-classes :linear
  :hints (("Goal"
	   :use (:instance
		 Sq-abs->-1-b-lemma
		 (y -1)))))

(defthm
  Sq-abs->-1-b
  (and (implies (< (realpart x) -1)
		(> (sq-abs x) 1))
       (implies (< (imagpart x) -1)
		(> (sq-abs x) 1)))
  :rule-classes :linear
  :hints (("Goal"
	   :in-theory (enable sq-abs))))

(defthm
  Sq-abs-=-1
  (implies (equal (sq-abs x) 1)
	   (and (<= -1 (realpart x))
		(<= (realpart x) 1)
		(<= -1 (imagpart x))
		(<= (imagpart x) 1)))
  :rule-classes :linear)

(defthm
  Sq-abs-=-1-a
  (implies (and (acl2-numberp x)
		(integerp (realpart x))
		(integerp (imagpart x))
		(equal (sq-abs x) 1))
	   (or (and (equal (realpart x) 0)
		    (or (equal (imagpart x) 1)
			(equal (imagpart x) -1)))
	       (and (equal (imagpart x) 0)
		    (or (equal (realpart x) 1)
			(equal (realpart x) -1)))))
  :rule-classes nil)

(defthm
  Unit-p=_+1_or_-1_or_i_or_-i
  (equal (unit-p x)
	 (or (equal x 1)
	     (equal x -1)
	     (equal x #c(0 1))
	     (equal x #c(0 -1))))
  :hints (("Goal"
	   :use (Sq-abs-=-1-a
		 Sq-abs-unit-p=1
		 Sq-abs=1-implies-unit-p))))

(defthm
  not-unit-p-sq-abs->-1
  (implies (and (gauss-intp x)
		(not (unit-p x))
		(not (equal x 0)))
	   (> (sq-abs x) 1))
  :rule-classes :linear
  :hints (("Goal"
	   :use Sq-abs=1-implies-unit-p)))

(defthm
  Sq-abs-<-Sq-abs-*
  (implies (and (not (unit-p y))
		(gauss-intp x)
		(not (equal x 0))
		(gauss-intp y)
		(not (equal y 0)))
	   (< (sq-abs x)
	      (sq-abs (* x y))))
  :rule-classes (:linear :rewrite)
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;
;; Reducible-p and
;; Irreducible-p theory:

(defun-sk
  Reducible-p (x)
  (exists (y z)(and (gauss-intp y)
		    (gauss-intp z)
		    (not (unit-p y))
		    (not (unit-p z))
		    (equal (* y z) x))))

(defun
  Irreducible-p (x)
  (and (gauss-intp x)
       (not (unit-p x))
       (not (reducible-p x))))

(defthm
  Irreducible-p-implies-prime-property
  (implies (and (irreducible-p x)
		(gauss-intp y)
		(gauss-intp z)
		(divides-p x (* y z)))
	   (or (divides-p x y)
	       (divides-p x z)))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 acl2::Irreducible-p-implies-prime-property
		 (acl2::edp gauss-intp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size sq-abs)
		 (acl2::q_e rnd-parts)
		 (acl2::r_e rnd-parts-rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p-witness)
		 (acl2::unit-p unit-p)
		 (acl2::reducible-p reducible-p)
		 (acl2::reducible-p-witness reducible-p-witness)
		 (acl2::irreducible-p irreducible-p))
		(acl2::x x)
		(acl2::y y)
		(acl2::z z)))
	  ("Subgoal 3"
	   :in-theory (disable unit-p=_+1_or_-1_or_i_or_-i
			       (:definition reducible-p)
			       (:definition divides-p)))
	  ("Subgoal 2"
	   :in-theory (disable unit-p=_+1_or_-1_or_i_or_-i
			       (:definition divides-p))
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
   elements of gauss-intp, so that if x is
   in gauss-intp, x is not 0, and x is not
   an unit, then x = product of the
   members in lst."
  (declare (xargs :measure (if (gauss-intp x)
			       (sq-abs x)
			       0)
		  :hints (("Subgoal 2"
			   :in-theory (disable (:definition mv-nth)
					       (:definition unit-p))
			   :use (:instance
				 Sq-abs-<-Sq-abs-*
				 (x (mv-nth 1 (reducible-p-witness x)))
				 (y (mv-nth 0 (reducible-p-witness x)))))
			  ("Subgoal 1"
			   :in-theory (disable (:definition mv-nth)
					       (:definition unit-p))
			   :use (:instance
				 Sq-abs-<-Sq-abs-*
				 (x (mv-nth 0 (reducible-p-witness x)))
				 (y (mv-nth 1 (reducible-p-witness x))))))))
  (cond ((or (not (gauss-intp x))
	     (equal x 0)
	     (equal (sq-abs x) 1))
	 nil)
	((reducible-p x)
	 (mv-let (y z)
		 (reducible-p-witness x)
		 (append (irreducible-factors y)
			 (irreducible-factors z))))
	(t (list x))))

(defun
  Gauss-intp-listp (lst)
  (if (consp lst)
      (and (gauss-intp (car lst))
	   (gauss-intp-listp (cdr lst)))
      t))

(defun
  Irreducible-listp (lst)
  (if (consp lst)
      (and (irreducible-p (car lst))
	   (irreducible-listp (cdr lst)))
      t))

(defun
  *-lst (lst)
  (if (consp lst)
      (if (gauss-intp (car lst))
	  (* (car lst)(*-lst (cdr lst)))
	  0)
      1))

(defthm
  IRREDUCIBLE-FACTORIZATION-EXISTENCE
  (and (true-listp (irreducible-factors x))
       (gauss-intp-listp  (irreducible-factors x))
       (irreducible-listp (irreducible-factors x))
       (implies (and (gauss-intp x)
		     (not (equal x 0))
		     (not (unit-p x)))
		(equal (*-lst (irreducible-factors x)) x)))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 acl2::IRREDUCIBLE-FACTORIZATION-EXISTENCE
		 (acl2::edp gauss-intp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size sq-abs)
		 (acl2::q_e rnd-parts)
		 (acl2::r_e rnd-parts-rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p-witness)
		 (acl2::unit-p unit-p)
		 (acl2::reducible-p reducible-p)
		 (acl2::reducible-p-witness reducible-p-witness)
		 (acl2::irreducible-p irreducible-p)
		 (acl2::irreducible-factors irreducible-factors)
		 (acl2::irreducible-listp irreducible-listp)
		 (acl2::edp-listp gauss-intp-listp)
		 (acl2::*_e-lst *-lst))
		(acl2::x x)))
	  ("Subgoal 3"
	   :in-theory (disable (:definition irreducible-p)))
	  ("Subgoal 1"
	   :in-theory (disable (:definition mv-nth)
			       (:definition reducible-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unit-associates-p theory:

(defun-sk
  Unit-associates-p (x y)
  (exists u (if (and (gauss-intp x)
		     (gauss-intp y))
		(and (unit-p u)
		     (equal (* u x)
			    y))
	        (equal x y))))

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
		  (acl2::edp gauss-intp)
		  (acl2::=_e equal)
		  (acl2::C_=_e identity)
		  (acl2::binary-+_e binary-+)
		  (acl2::binary-*_e binary-*)
		  (acl2::-_e unary--)
		  (acl2::0_e (lambda () 0))
		  (acl2::1_e (lambda () 1))
		  (acl2::size sq-abs)
		  (acl2::q_e rnd-parts)
		  (acl2::r_e rnd-parts-rem)
		  (acl2::divides-p divides-p)
		  (acl2::divides-p-witness divides-p-witness)
		  (acl2::unit-p unit-p)
		  (acl2::reducible-p reducible-p)
		  (acl2::reducible-p-witness reducible-p-witness)
		  (acl2::irreducible-p irreducible-p)
		  (acl2::unit-associates-p unit-associates-p)
		  (acl2::unit-associates-p-witness unit-associates-p-witness))
		 (acl2::x x)
		 (acl2::y y)))
	  ("Subgoal 3"
	   :in-theory (disable (:definition irreducible-p)))
	  ("Subgoal 2"
	   :use (:instance
		 unit-associates-p-suff
		 (x acl2::x)
		 (y acl2::y)))
	  ("Subgoal 1"
	   :in-theory (disable unit-p=_+1_or_-1_or_i_or_-i))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unique factorization theory:

(defun
  Member-unit-associate (x lst)
  "Determine if an unit-associate
   of x is a member of lst."
  (cond ((atom lst)
	 nil)
	((unit-associates-p x (car lst))
	 lst)
	(t (member-unit-associate x (cdr lst)))))

(defun
  Delete-one-unit-associate (x lst)
  "Return the result of deleting one occurrence
   of an unit-associate of x from the list lst."
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
		 (acl2::edp gauss-intp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size sq-abs)
		 (acl2::q_e rnd-parts)
		 (acl2::r_e rnd-parts-rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p-witness)
		 (acl2::unit-p unit-p)
		 (acl2::unit-associates-p unit-associates-p)
		 (acl2::unit-associates-p-witness unit-associates-p-witness)
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
		 (acl2::edp gauss-intp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size sq-abs)
		 (acl2::q_e rnd-parts)
		 (acl2::r_e rnd-parts-rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p-witness)
		 (acl2::unit-p unit-p)
		 (acl2::unit-associates-p unit-associates-p)
		 (acl2::unit-associates-p-witness unit-associates-p-witness)
		 (acl2::Member-unit-associate Member-unit-associate)
		 (acl2::Delete-one-unit-associate Delete-one-unit-associate)
		 (acl2::Bag-equal-unit-associates Bag-equal-unit-associates))
		(acl2::lst1 lst1)
		(acl2::lst2 lst2)))))

(defun
  Multiplicity-unit-associate (x lst)
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
		 (acl2::edp gauss-intp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size sq-abs)
		 (acl2::q_e rnd-parts)
		 (acl2::r_e rnd-parts-rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p-witness)
		 (acl2::unit-p unit-p)
		 (acl2::unit-associates-p unit-associates-p)
		 (acl2::unit-associates-p-witness unit-associates-p-witness)
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
		 (acl2::edp gauss-intp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size sq-abs)
		 (acl2::q_e rnd-parts)
		 (acl2::r_e rnd-parts-rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p-witness)
		 (acl2::unit-p unit-p)
		 (acl2::reducible-p reducible-p)
		 (acl2::reducible-p-witness reducible-p-witness)
		 (acl2::irreducible-p irreducible-p)
		 (acl2::irreducible-listp irreducible-listp)
		 (acl2::*_e-lst *-lst)
		 (acl2::unit-associates-p unit-associates-p)
		 (acl2::unit-associates-p-witness unit-associates-p-witness)
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
		 (acl2::edp gauss-intp)
		 (acl2::=_e equal)
		 (acl2::C_=_e identity)
		 (acl2::binary-+_e binary-+)
		 (acl2::binary-*_e binary-*)
		 (acl2::-_e unary--)
		 (acl2::0_e (lambda () 0))
		 (acl2::1_e (lambda () 1))
		 (acl2::size sq-abs)
		 (acl2::q_e rnd-parts)
		 (acl2::r_e rnd-parts-rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p-witness)
		 (acl2::unit-p unit-p)
		 (acl2::reducible-p reducible-p)
		 (acl2::reducible-p-witness reducible-p-witness)
		 (acl2::irreducible-p irreducible-p)
		 (acl2::irreducible-listp irreducible-listp)
		 (acl2::*_e-lst *-lst)
		 (acl2::unit-associates-p unit-associates-p)
		 (acl2::unit-associates-p-witness unit-associates-p-witness)
		 (acl2::Member-unit-associate Member-unit-associate)
		 (acl2::Delete-one-unit-associate Delete-one-unit-associate)
		 (acl2::Bag-equal-unit-associates Bag-equal-unit-associates))
		(acl2::lst1 lst1)
		(acl2::lst2 lst2)))))
