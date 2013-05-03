; ACL2 Euclidean Domain books -- Book 5ba -- Example: Complex numbers of
; the form a+b(sqrt 2)i where a and b are integers are shown to be an
; Euclidean domain.

;  This version uses ACL2r.

;  This version uses quantifiers (defun-sk) and is
;  non-exedutable.

; Copyright (C) 2005  Ruben Gamboa and John R. Cowles, University of Wyoming

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
; Ruben Gamboa and John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071-3682 U.S.A.

; Last modified Mar. 23.

#|
To certify this book, first, create a world with the following package:

(defpkg "SQRT2I-INT"
         (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

    (certify-book "ed5ba"
                  1
		 nil ;;compile-flg
		 )
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; These complex numbers are an Euclidean Doamin:

;;  Sqrt2i-intp   ; Predicate for set of Euclidean Domain elements.
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

;;   Here Sqrt2i-intp is defined by

;; (Sqrt2i-intp x) = (and (acl2-numberp x)
;;                        (integerp (realpart x))
;;                        (integerp (/ (imagpart x) (acl2-sqrt 2))))

;;  Sq-abs, rnd-parts, and rnd-parts-rem are defined for sqrt2i
;;   integers x and nonzero sqrt2i integers y by

;; (sq-abs x) = (+ (* (realpart x)(realpart x))
;;                 (* (imagpart x)(imagpart x)))

;;  (rnd-parts x y) = (complex (round (realpart (* x (/ y))) 1)
;;                             (* (acl2-sqrt 2)
;;                                (round (/ (imagpart (* x (/ y)))
;;                                          (acl2-sqrt 2))
;;                                       1)))

;; (rnd-parts-rem x y) = (- x (* y (rnd-parts x y)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
;;;
;; An Euclidean Domain is an integral domain, together with a Size function
;; from nonzero domain elements into the nonnegative integers, that
;; satisfies the Division Propery:
;;
;; Division Propery. For all domain elements x and all nonzero domain
;;             elements y there are domain elements q and r such that

;;        x = yq + r and either r is the domain's zero or Size(r) < Size(y)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
;;
;; An Integral Domain is a commutative ring with no zero-divisors.

;; A Zero-Divisor in a commutative ring is a nonzero ring element, x, such
;; that there is a nonzero ring element y such that the product xy  equals
;; the zero element of the ring.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
;;;;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
;
;; There is no loss of generality in assuming the
;;   Multiplicative Size Property:

;;     For all nonzero domain elements x and y, Size(x) <= Size(xy).

;;     If the original Size function does not satisfy this property,
;;     then it can replaced by another that does satisfy this and the
;;     division property.
;;      See Book 2 of the ACL2 Euclidean Domain books, ed2.lisp,
;;      for a proof.

;;  In fact, for complex numbers x and y,
;;                (sq-abs (* x y)) = (* (sq-abs x)(sq-abs y)).
;;   So, if Sqrt2i-intp y differs from 0, then (<= 1 (sq-abs y));
;;   then for any Sqrt2i-intp x, (sq-abs x)  = (* (sq-abs x) 1)
;;                                          <= (* (sq-abs x)(abs y))
;;                                           = (sq-abs (* x y)).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "SQRT2I-INT")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
;;;
; Make temporary use of an ACL2 Arithmetic Book and a book containing  
; facts about FLOOR and MOD to help certify this book

(local
(include-book "nonstd/arithmetic/top" :dir :system
; Matt K.: Commenting out use of :uncertified-okp after v4-3 in order to
; support provisional certification:
;	       :uncertified-okp nil
	       :defaxioms-okp nil
	       :skip-proofs-okp nil))

(local
(include-book "nonstd/ihs/quotient-remainder-lemmas" :dir :system
; Matt K.: Commenting out use of :uncertified-okp after v4-3 in order to
; support provisional certification:
;	       :uncertified-okp nil
	       :defaxioms-okp nil
	       :skip-proofs-okp nil))

(local
(include-book "nonstd/nsa/sqrt" :dir :system
; Matt K.: Commenting out use of :uncertified-okp after v4-3 in order to
; support provisional certification:
;	       :uncertified-okp nil
	       :defaxioms-okp nil
	       :skip-proofs-okp nil))

(verify-guards acl2::acl2-sqrt)
(local (in-theory (disable acl2::acl2-sqrt)))

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
   (implies (and (real/rationalp x)
		(real/rationalp y)
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
   (implies (and (real/rationalp x)
		(real/rationalp y)
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
   (implies (and (real/rationalp x)
		(real/rationalp y)
		(not (equal y 0)))
	   (and (<= (round x y)(+  1/2 (* x (/ y))))
		(>= (round x y)(+ -1/2 (* x (/ y))))))
   :rule-classes ((:linear
		  :trigger-terms ((round x y)))))

(defthm
   Round-bounds-1
   (implies (real/rationalp r)
	   (and (<= (- r (round r 1))
		    1/2)
		(>= (- r (round r 1))
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
   (implies (real/rationalp r)
	   (<= (* (- r (round r 1))
		  (- r (round r 1)))
	       1/4))
   :rule-classes :linear
   :hints (("Goal"
	   :in-theory (disable round-as-floor-&-ceiling)
	   :use (:instance
		 Round-bounds-2-lemma-3
		 (x  (- r (round r 1)))
		 (y 1/2)))))

(defthm
   Round-bounds-3
   (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y))
	   (and (<= (- x (* y (round (* x (/ y)) 1)))
		    (* 1/2 y))
		(<= (* -1/2 y)
		    (- x (* y (round (* x (/ y)) 1))))))
   :rule-classes :linear
   :hints (("Goal"
	   :in-theory (disable round-as-floor-&-ceiling Round-bounds-1)
	   :use ((:instance Round-bounds-1
			    (r (* x (/ y))))
		 (:instance acl2::<-*-right-cancel
			    (acl2::x 1/2)
			    (acl2::y (- (* x (/ y)) (round (* x (/ y)) 1)))
			    (acl2::z y))
		 (:instance acl2::<-*-right-cancel
			    (acl2::x (- (* x (/ y)) (round (* x (/ y)) 1)))
			    (acl2::y -1/2)
			    (acl2::z y))
		 ))))

(defthm
   Round-bounds-4
   (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y))
	   (<= (* (- x (* y (round (* x (/ y)) 1)))
		  (- x (* y (round (* x (/ y)) 1))))
	       (* 1/4 y y)))
   :rule-classes :linear
   :hints (("Goal"
	   :in-theory (disable round-as-floor-&-ceiling)
	   :use (:instance
		 Round-bounds-2-lemma-3
		 (x  (- x (* y (round (* x (/ y)) 1))))
		 (y (* 1/2 y))))))


(defthm
   Round-bounds-3-specialized
   (implies (real/rationalp x)
	   (and (<= (- x (* (acl2::acl2-sqrt 2)
			    (round (* (/ (acl2::acl2-sqrt 2)) x) 1)))
		    (* 1/2 (acl2::acl2-sqrt 2)))
		(<= (* -1/2 (acl2::acl2-sqrt 2))
		    (- x (* (acl2::acl2-sqrt 2)
			    (round (* (/ (acl2::acl2-sqrt 2)) x) 1))))))
   :rule-classes :linear
   :hints (("Goal"
	   :in-theory (disable ROUND-AS-FLOOR-&-CEILING)
	   :use ((:instance Round-bounds-3
			    (y (acl2::acl2-sqrt 2)))))))

(defthm
   Round-bounds-4-specialized
   (implies (real/rationalp x)
	   (<= (* (- x (* (acl2::acl2-sqrt 2)
			  (round (* x (/ (acl2::acl2-sqrt 2))) 1)))
		  (- x (* (acl2::acl2-sqrt 2)
			  (round (* x (/ (acl2::acl2-sqrt 2))) 1))))
	       1/2))
   :rule-classes :linear
   :hints (("Goal"
	   :in-theory (disable round-as-floor-&-ceiling)
	   :use (:instance
		 Round-bounds-4
		 (y (acl2::acl2-sqrt 2))
		 ))))
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
   (implies (and (real/rationalp r)
		(real/rationalp r0)
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
   (implies (and (real/rationalp r)
		(real/rationalp r0)
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
	   :use ((:instance simple-algebra-1 (r r) (r0 r0))))))

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
   sqrt2i-intp (x)
   (declare (xargs :guard t))
   (and (acl2-numberp x)
        (integerp (realpart x))
        (integerp (/ (imagpart x) (acl2::acl2-sqrt 2)))))

(local (in-theory (disable (sqrt2i-intp))))

(defthm inv-sqrt-2*sqrt-2
   (equal (* (/ (acl2::acl2-sqrt 2)) (/ (acl2::acl2-sqrt 2))) 1/2)
   :hints (("Goal"
	   :use ((:instance acl2::distributivity-of-/-over-*
			    (acl2::x (acl2::acl2-sqrt 2))
			    (acl2::y (acl2::acl2-sqrt 2))))
	   :in-theory (disable acl2::distributivity-of-/-over-*))))

(defthm sqrt-2*sqrt-2*x
   (equal (* (ACL2::ACL2-SQRT 2) (ACL2::ACL2-SQRT 2) x)
	 (* 2 x))
   :hints (("Goal"
	   :use ((:instance (:theorem (implies (equal (* x1 x2) x)
					       (equal (* x1 x2 y) (* x y))))
			    (x1 (acl2::acl2-sqrt 2))
			    (x2 (acl2::acl2-sqrt 2))
			    (x 2)
			    (y x))))))

(defthm inv-sqrt-2*sqrt-2*x
   (equal (* (/ (acl2::acl2-sqrt 2)) (/ (acl2::acl2-sqrt 2)) x)
	 (* 1/2 x))
   )

(defthm sqrt-int-*-sqrt-int
   (implies (and (integerp (* (/ (acl2::acl2-sqrt 2)) x))
		(integerp (* (/ (acl2::acl2-sqrt 2)) y)))
	   (integerp (* x y)))
   :hints (("Goal"
	   :use ((:instance (:theorem (implies (and (acl2-numberp x)
						    (integerp (/ x 2)))
					       (integerp x)))
			    (x (* x y)))
		 (:instance (:theorem (implies (and (integerp (* (/ (acl2::acl2- 
sqrt 2)) x))
						    (integerp (* (/ (acl2::acl2-sqrt 2)) y)))
					       (integerp (/ (* x y) 2)))))))
	  ("Subgoal 1"
	   :use ((:instance (:theorem (implies (and (integerp x)
						    (integerp y))
					       (integerp (* x y))))
			    (x (* (/ (acl2::acl2-sqrt 2)) x))
			    (y (* (/ (acl2::acl2-sqrt 2)) y)))))
	  ))


(defthm Closure-Laws-Product
   (implies (and (sqrt2i-intp x)
		(sqrt2i-intp y))
	   (sqrt2i-intp (* x y)))
   :hints (("Subgoal 2"
	   :use ((:instance sqrt-int-*-sqrt-int
			    (x (imagpart x))
			    (y (imagpart y))))
	   :in-theory (disable sqrt-int-*-sqrt-int))
	  ("Subgoal 1"
	   :use ((:instance (:theorem (implies (and (integerp i) (integerp j))
					       (integerp (* i j))))
			    (i (* (/ (ACL2::ACL2-SQRT 2))
				  (IMAGPART X)))
			    (j (REALPART Y)))
		 (:instance (:theorem (implies (and (integerp i) (integerp j))
					       (integerp (* i j))))
			    (i (* (/ (ACL2::ACL2-SQRT 2))
				  (IMAGPART y)))
			    (j (REALPART x)))))
	  )
   :rule-classes nil)

(defthm ;;===================
   Closure-Laws
   (and (implies (sqrt2i-intp x)
		(and (implies (sqrt2i-intp y)
			      (and (sqrt2i-intp (+ x y))
				   (sqrt2i-intp (* x y))))
		     (sqrt2i-intp (- x))))
        (sqrt2i-intp 0)
        (sqrt2i-intp 1))
   :hints (("Goal"
	   :use ((:instance Closure-Laws-Product))))
   :rule-classes nil)

(defthm ;;===================
   Equivalence-Law
   (implies (sqrt2i-intp x)
	   (and (equal x x)
		(implies (sqrt2i-intp y)
			 (and (booleanp (equal x y))
			      (implies (equal x y)
				       (equal y x))
			      (implies (sqrt2i-intp z)
				       (implies (and (equal x y)
						     (equal y z))
						(equal x z)))))))
   :rule-classes nil)

(defthm ;;===================
   Congruence-Laws
   (implies (equal y1 y2)
	   (and (iff (sqrt2i-intp y1)
		     (sqrt2i-intp y2))
		(implies (and (sqrt2i-intp y1)
			      (sqrt2i-intp y2))
			 (and (implies (sqrt2i-intp x)
				       (and (equal (+ x y1)
						   (+ x y2))
					    (equal (* x y1)
						   (* x y2))))
			      (implies (sqrt2i-intp z)
				       (and (equal (+ y1 z)
						   (+ y2 z))
					    (equal (* y1 z)
						   (* y2 z))))
			      (equal (- y1)
				     (- y2))))))
   :rule-classes nil)

(defthm ;;=====================
   Closure-of-identity
   (implies (sqrt2i-intp x)
	   (sqrt2i-intp (identity x)))
   :rule-classes nil)

(defthm ;;=====================
   Equivalence-class-Laws
   (and (implies (sqrt2i-intp x)
		(equal (identity x) x))
        (implies (and (sqrt2i-intp y1)
		     (sqrt2i-intp y2)
		     (equal y1 y2))
		(equal (identity y1)
		       (identity y2))))
   :rule-classes nil)

(defthm ;;=====================
   Commutativity-Laws
   (implies (and (sqrt2i-intp x)
		(sqrt2i-intp y))
	   (and (equal (+ x y)
		       (+ y x))
		(equal (* x y)
		       (* y x))))
   :rule-classes nil)

(defthm ;;====================
   Associativity-Laws
   (implies (and (sqrt2i-intp x)
		(sqrt2i-intp y)
		(sqrt2i-intp z))
	   (and (equal (+ (+ x y) z)
		       (+ x (+ y z)))
		(equal (* (* x y) z)
		       (* x (* y z)))))
   :rule-classes nil)

(defthm ;;================
   Left-Distributivity-Law
   (implies (and (sqrt2i-intp x)
		(sqrt2i-intp y)
		(sqrt2i-intp z))
	   (equal (* x (+ y z))
		  (+ (* x y)
		       (* x z))))
   :rule-classes nil)

(defthm ;;================
   Left-Unicity-Laws
   (implies (sqrt2i-intp x)
	   (and (equal (+ 0 x)
		       x)
		(equal (* 1 x)
		       x)))
   :rule-classes nil)

(defthm ;;=================
   Right-Inverse-Law
   (implies (sqrt2i-intp x)
	   (equal (+ x (- x))
		  0))
   :rule-classes nil)

(defthm ;;===================
   Zero-Divisor-Law
   (implies (and (sqrt2i-intp x)
		(sqrt2i-intp y))
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

(local
(defthm Natp-sq-abs-lemma
    (implies (and (realp r)
		 (integerp (* (/ (acl2::acl2-sqrt 2)) r)))
	    (integerp (* r r)))
    :hints (("Goal"
	    :use ((:instance (:theorem (implies (and (realp x)
						     (integerp (* 1/2 x)))
						(integerp x)))
			     (x (* r r))))))))

(defthm  ;;==================
   Natp-sq-abs
   (implies (and (sqrt2i-intp x)
		(not (equal x 0)))
	   (and (integerp (sq-abs x))
		(>= (sq-abs x) 0)))
   :hints (("Goal"
	   :use ((:instance Natp-sq-abs-lemma
			    (r (imagpart x))))))
   :rule-classes ((:type-prescription
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart x))))
			   (and (integerp (sq-abs x))
				(>= (sq-abs x) 0))))
		 (:linear
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart x)))
				(integerp (imagpart x))
				(not (equal x 0)))
			   (> (sq-abs x) 0)))))

(defthm ;;==================
   Congruence-for-abs
   (implies (and (sqrt2i-intp y1)
		(sqrt2i-intp y2)
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
		 (integerp (/ i (acl2::acl2-sqrt 2))))
	    q
	    (complex (round r 1)
		     (* (acl2::acl2-sqrt 2)
			(round (/ i (acl2::acl2-sqrt 2))
			       1))))))

(defun ;;=========================
   Rnd-parts-rem (x y)
   (declare (xargs :guard
		  (and (acl2-numberp x)
		       (acl2-numberp y)
		       (not (equal y 0)))))
   (- x (* y (rnd-parts x y))))

(defthm
   Closure-of-rnd-parts
   (implies (and (sqrt2i-intp x)
		(sqrt2i-intp y)
		(not (equal y 0)))
	   (sqrt2i-intp (rnd-parts x y)))
   :rule-classes ((:type-prescription
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (* (/ (acl2::acl2-sqrt 2))
					     (imagpart x)))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (* (/ (acl2::acl2-sqrt 2))
					     (imagpart y)))
				(not (equal y 0)))
			   (integerp (realpart (rnd-parts x y))))
		  :hints (("Goal"
			   :in-theory (disable (:definition rnd-parts)))))
		 (:type-prescription
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (* (/ (acl2::acl2-sqrt 2))
					     (imagpart x)))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (* (/ (acl2::acl2-sqrt 2))
					     (imagpart y)))
				(not (equal y 0)))
			   (integerp (* (/ (acl2::acl2-sqrt 2))
					(imagpart (rnd-parts x y)))))
		  :hints (("Goal"
			   :in-theory (disable (:definition rnd-parts)))))))

(local
(defthm Closure-of-rnd-parts-rem-lemma
    (implies (and (sqrt2i-intp x)
		 (sqrt2i-intp y))
	    (integerp (* (imagpart y)
			 (imagpart x))))
    ))


(local
(defthm Closure-of-rnd-parts-rem-lemma-2
    (implies (sqrt2i-intp x)
	    (integerp (* (/ (acl2::acl2-sqrt 2))
			 (imagpart x))))
    ))

(defthm
   Closure-of-rnd-parts-rem
   (implies (and (sqrt2i-intp x)
		(sqrt2i-intp y)
		(not (equal y 0)))
	   (sqrt2i-intp (rnd-parts-rem x y)))
   :rule-classes ((:type-prescription
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (* (/ (acl2::acl2-sqrt 2))
					     (imagpart x)))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (* (/ (acl2::acl2-sqrt 2))
					     (imagpart y)))
				(not (equal y 0)))
			   (integerp (realpart (rnd-parts-rem x y))))
		  :hints (("Goal"
			   :in-theory (disable (:definition rnd-parts-rem)))))
		 (:type-prescription
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (* (/ (acl2::acl2-sqrt 2))
					     (imagpart x)))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (* (/ (acl2::acl2-sqrt 2))
					     (imagpart y)))
				(not (equal y 0)))
			   (integerp (* (/ (acl2::acl2-sqrt 2))
					(imagpart (rnd-parts-rem x y)))))
		  :hints (("Goal"
			   :in-theory (disable (:definition rnd-parts-rem))))))
   :hints (("Goal"
	   :in-theory (disable (:definition rnd-parts)))
	  ("Subgoal 2"
	   :use ((:instance Closure-of-rnd-parts-rem-lemma
			    (x y)
			    (y (rnd-parts x y))))
	   :in-theory (disable Closure-of-rnd-parts-rem-lemma
			       sqrt-int-*-sqrt-int
			       rnd-parts))
	  ("Subgoal 1"
	   :use ((:instance Closure-of-rnd-parts-rem-lemma-2
			    (x x))
		 (:instance Closure-of-rnd-parts-rem-lemma-2
			    (x y))
		 (:instance Closure-of-rnd-parts-rem-lemma-2
			    (x (rnd-parts x y)))
		 (:instance (:theorem (implies (and (integerp x)
						    (integerp y))
					       (integerp (* x y))))
			    (x (* (/ (ACL2::ACL2-SQRT 2))
				  (IMAGPART Y)))
			    (y (REALPART (RND-PARTS X Y))))
		 (:instance (:theorem (implies (and (integerp x)
						    (integerp y))
					       (integerp (* x y))))
			    (x (* (/ (ACL2::ACL2-SQRT 2))
				  (IMAGPART (RND-PARTS X Y))))
			    (y (REALPART y)))		
		 )
	   :in-theory (disable Closure-of-rnd-parts-rem-lemma-2
			       sqrt-int-*-sqrt-int
			       rnd-parts))))

(defthm ;;===========================
   Closure-of-rnd-parts-&-rnd-parts-rem
   (implies (and (sqrt2i-intp x)
		(sqrt2i-intp y)
		(not (equal y 0)))
	   (and (sqrt2i-intp (rnd-parts x y))
		(sqrt2i-intp (rnd-parts-rem x y))))
   :rule-classes nil
   :hints (("Goal"
	   :in-theory (disable (:definition rnd-parts)
			       (:definition rnd-parts-rem)))))

(defthm ;;===========================
   Congruence-for-rnd-parts-&-rnd-parts-rem
   (implies (and (sqrt2i-intp y1)
		(sqrt2i-intp y2)
		(equal y1 y2))
	   (and (implies (and (sqrt2i-intp x)
			      (not (equal y1 0)))
			 (and (equal (rnd-parts x y1)
				     (rnd-parts x y2))
			      (equal (rnd-parts-rem x y1)
				     (rnd-parts-rem x y2))))
		(implies (and (sqrt2i-intp z)
			      (not (equal z 0)))
			 (and (equal (rnd-parts y1 z)
				     (rnd-parts y2 z))
			      (equal (rnd-parts-rem y1 z)
				     (rnd-parts-rem y2 z))))))
   :rule-classes nil)

(defthm
   Division-property-equation
   (implies (and (sqrt2i-intp x)
		(sqrt2i-intp y)
		(not (equal y 0)))
	   (equal x (+ (* y (rnd-parts x y))
		       (rnd-parts-rem x y))))
   :rule-classes ((:rewrite
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (* (/ (acl2::acl2-sqrt 2))
					     (imagpart x)))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (* (/ (acl2::acl2-sqrt 2))
					     (imagpart y)))
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
       1/2)
   :rule-classes nil
   :hints (("Goal"
	   :in-theory (disable round-as-floor-&-ceiling)
	   :use (:instance
		 Round-bounds-4-specialized
		 (x (imagpart (* x (/ y))))))))

(defthm
   Sq-abs-rnd-parts-inequality
   (<= (sq-abs (- (* x (/ y))
		 (rnd-parts x y)))
       3/4)
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
	       (* 3/4 (sq-abs y))))
   :rule-classes :linear
   :hints (("Goal"
	   :in-theory (disable (:definition sq-abs)
			       (:definition rnd-parts)
			       (:definition rnd-parts-rem))
	   :use (Sq-abs-rnd-parts-rem-equality
		 Sq-abs-rnd-parts-inequality
		 (:instance
		  (:theorem
		   (implies (and (real/rationalp x)
				 (real/rationalp y)
				 (real/rationalp z)
				 (<= x y)
				 (>= z 0))
			    (<= (* x z)(* y z))))
		  (x (sq-abs (- (* x (/ y))
				(rnd-parts x y))))
		  (y 3/4)
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
   (implies (and (sqrt2i-intp x)
		(sqrt2i-intp y)
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
   (implies (and (sqrt2i-intp x)
		(not (equal x 0))
		(sqrt2i-intp y)
		(not (equal y 0)))
	   (<= (sq-abs x)
	       (sq-abs (* x y))))
   :rule-classes ((:linear
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart x)))
				(not (equal x 0))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart y)))
				(not (equal y 0)))
			   (<= (sq-abs x)
			       (sq-abs (* x y))))
		  :hints (("Goal"
			   :in-theory (disable (:definition sq-abs)))))
		 (:rewrite
		  :corollary
		  (implies (and (acl2-numberp x)
				(integerp (realpart x))
				(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart x)))				(not  
(equal x 0))
				(acl2-numberp y)
				(integerp (realpart y))
				(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart y)))
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
   (exists z (and (sqrt2i-intp x)
		 (sqrt2i-intp z)
		 (equal (* x z)
			y))))

(defthm
   Divides-p-suff-rewrite
   (implies (and (acl2-numberp x)
		(integerp (realpart x))
		(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart x)))
		(acl2-numberp z)
		(integerp (realpart z))
		(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart z)))
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
		  (acl2::edp sqrt2i-intp)
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
		 (acl2::x x)))
	  ("Subgoal 3"
	   :use ((:instance Closure-Laws (x acl2::x) (y acl2::y))))
	  ))

(defthm
   Sq-abs=1-implies-unit-p
   (implies (and (sqrt2i-intp x)
		(not (equal x 0))
		(equal (sq-abs x)
		       1))
	   (unit-p x))
   :rule-classes nil
   :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  acl2::Size=Size-1_e-implies-unit-p
		  (acl2::edp sqrt2i-intp)
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
		(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart x)))
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
		  (implies (and (real/rationalp x)
				(real/rationalp y)
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
   sq-abs-sqrt2i-int
   (implies (and (acl2-numberp x)
		(integerp (realpart x))
		(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart x))))
	   (equal (sq-abs x)
		  (+ (* (realpart x) (realpart x))
		     (* 2
			(* (/ (acl2::acl2-sqrt 2)) (imagpart x))
			(* (/ (acl2::acl2-sqrt 2)) (imagpart x))))))
   :rule-classes nil
   :hints (("Goal"
	   :in-theory (enable sq-abs))))

(defthm
   algebra-of-sq-abs
   (implies (and (integerp r)
		(integerp i)
		(not (equal i 0)))
	   (< 1 (+ (* r r) (* 2 i i)))))
		
(defthm
   sq-abs-=-1-a-lemma
   (implies (and (acl2-numberp x)
		(integerp (realpart x))
		(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart x)))
		(equal (sq-abs x) 1))
	   (equal (imagpart x) 0))
   :hints (("Goal"
	   :use ((:instance sq-abs-sqrt2i-int)
		 (:instance algebra-of-sq-abs
			    (r (realpart x))
			    (i (* (/ (acl2::acl2-sqrt 2)) (imagpart x)))))
	   )))

(defthm
   sq-abs-=-1-a-lemma-2
   (implies (and (acl2-numberp x)
		(equal (realpart x) 0)
		(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart x))))
	   (not (equal (sq-abs x) 1)))
   :hints (("Goal"
	   :use ((:instance sq-abs-=-1-a-lemma)
		 (:instance sq-abs-sqrt2i-int)))))

(defthm
   Sq-abs-=-1-a
   (implies (and (acl2-numberp x)
		(integerp (realpart x))
		(integerp (* (/ (acl2::acl2-sqrt 2)) (imagpart x)))
		(equal (sq-abs x) 1))
	   (and (equal (imagpart x) 0)
		(or (equal (realpart x) 1)
		    (equal (realpart x) -1))))
   :rule-classes nil)

(defthm
   Unit-p=_+1_or_-1
   (equal (unit-p x)
	 (or (equal x 1)
	     (equal x -1)))
   :hints (("Goal"
	   :use (Sq-abs-=-1-a
		 Sq-abs-unit-p=1
		 Sq-abs=1-implies-unit-p))))

(defthm
   not-unit-p-sq-abs->-1
   (implies (and (sqrt2i-intp x)
		(not (unit-p x))
		(not (equal x 0)))
	   (> (sq-abs x) 1))
   :rule-classes :linear
   :hints (("Goal"
	   :use Sq-abs=1-implies-unit-p)))

(defthm
   Sq-abs-<-Sq-abs-*
   (implies (and (not (unit-p y))
		(sqrt2i-intp x)
		(not (equal x 0))
		(sqrt2i-intp y)
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
   (exists (y z)(and (sqrt2i-intp y)
		    (sqrt2i-intp z)
		    (not (unit-p y))
		    (not (unit-p z))
		    (equal (* y z) x))))

(defun
   Irreducible-p (x)
   (and (sqrt2i-intp x)
        (not (unit-p x))
        (not (reducible-p x))))

(defthm
   Irreducible-p-implies-prime-property
   (implies (and (irreducible-p x)
		(sqrt2i-intp y)
		(sqrt2i-intp z)
		(divides-p x (* y z)))
	   (or (divides-p x y)
	       (divides-p x z)))
   :rule-classes nil
   :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 acl2::Irreducible-p-implies-prime-property
		 (acl2::edp sqrt2i-intp)
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
	   :in-theory (disable unit-p=_+1_or_-1
			       (:definition reducible-p)
			       (:definition divides-p)))
	  ("Subgoal 2"
	   :in-theory (disable unit-p=_+1_or_-1
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
    elements of sqrt2i-intp, so that if x is
    in sqrt2i-intp, x is not 0, and x is not
    an unit, then x = product of the
    members in lst."
   (declare (xargs :measure (if (sqrt2i-intp x)
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
   (cond ((or (not (sqrt2i-intp x))
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
   Sqrt2i-intp-listp (lst)
   (if (consp lst)
       (and (sqrt2i-intp (car lst))
	   (sqrt2i-intp-listp (cdr lst)))
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
       (if (sqrt2i-intp (car lst))
	  (* (car lst)(*-lst (cdr lst)))
	  0)
       1))

(defthm
   IRREDUCIBLE-FACTORIZATION-EXISTENCE
   (and (true-listp (irreducible-factors x))
        (sqrt2i-intp-listp  (irreducible-factors x))
        (irreducible-listp (irreducible-factors x))
        (implies (and (sqrt2i-intp x)
		     (not (equal x 0))
		     (not (unit-p x)))
		(equal (*-lst (irreducible-factors x)) x)))
   :rule-classes nil
   :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 acl2::IRREDUCIBLE-FACTORIZATION-EXISTENCE
		 (acl2::edp sqrt2i-intp)
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
		 (acl2::edp-listp sqrt2i-intp-listp)
		 (acl2::*_e-lst *-lst))
		(acl2::x x)))
	  ("Subgoal 3"
	   :in-theory (disable (:definition irreducible-p)))
	  ("Subgoal 1"
	   :in-theory (disable (:definition mv-nth)
			       (:definition reducible-p)
			       (:executable-counterpart irreducible-factors)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unit-associates-p theory:

(defun-sk
   Unit-associates-p (x y)
   (exists u (if (and (sqrt2i-intp x)
		     (sqrt2i-intp y))
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
		  (acl2::edp sqrt2i-intp)
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
	   :in-theory (disable unit-p=_+1_or_-1))))

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
		 (acl2::edp sqrt2i-intp)
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
		 (acl2::edp sqrt2i-intp)
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
		 (acl2::edp sqrt2i-intp)
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
		 (acl2::edp sqrt2i-intp)
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
		 (acl2::edp sqrt2i-intp)
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
