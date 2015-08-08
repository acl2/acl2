; ACL2 Euclidean Domain books -- Book 6a -- Example: Polynomials.
;  Normalized Univariate Polynomials with Coefficents from an arbitrary
;  Field are shown to be an Euclidean Domain with with Unique
;  Factorization. Here Size is the degree of a polynomial; Quotient
;  and Remainder are defined as expected for polynomials.

;  This version uses quantifiers (defun-sk) and is
;  non-exedutable.

; Copyright (C) 2006 John R. Cowles and Ruben A. Gamboa, University of
; Wyoming

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

; Modified by Matt Kaufmann for ACL2 Version 3.1 because
; SBCL complains about LISP::.

#|
To certify this book, first, create a world with the following packages:

(defconst *import-symbols*
  (set-difference-eq
   (union-eq *acl2-exports*
	     *common-lisp-symbols-from-main-lisp-package*)
     '(null + * - < = / commutativity-of-* associativity-of-*
	    commutativity-of-+ associativity-of-+ distributivity)))

(defpkg "FLD"
  *import-symbols*)

(defpkg "FUTER"
  *import-symbols*)

(defpkg "FUMON"
  (union-eq *import-symbols*
	    '(FLD::fdp FUTER::terminop)))

(defpkg "FUPOL"
  (union-eq *import-symbols*
	    '(FUTER::naturalp FUTER::terminop FUMON::monomio FUMON::coeficiente
			    FUMON::termino FUMON::monomiop)))

(defpkg "FUNPOL"
  (set-difference-eq *import-symbols*
		     '(rem)))

(certify-book "ed6a"
	      6
	      nil ;;compile-flg
	      )
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Univariate Polynomials with Coefficents from an arbitrary
;   Field Euclidean Doamin:

;;  Polinomiop  ; Predicate for set of Euclidean Domain elements.
;;  =           ; (Polynomial) Equality predicate for Euclidean Domain elements.
;;  C_=         ; Choose unique equivalence class representative for equal.
;;  +           ; (Polynomial) Addition in Euclidean Domain.
;;  *           ; (Polynomial) Multiplication in Euclidean Domain.
;;  -           ; (Polynomial) Unary minus in Euclidean Domain.
;;  nulo        ; 0 (Polynomial) element in Euclidean Domain.
;;  identidad   ; 1 (Polynomial) element in Euclidean Domain.
;;  Deg         ; Natp size of each nonzero Euclidean Domain element.
;;  quot        ; (Polynomial) Quotient in Euclidean Domain.
;;  rem         ; (Polynomial) Remainder in Euclidean Domain.
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
(in-package "FUNPOL")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Include ACL2 Book for Normalized Univariate Polynomials over a Field.
(include-book "fld-u-poly/fuquot-rem"
	      :load-compiled-file nil)

;; Make temporary use of an ACL2 Euclidean Domain Book:
(local
 (include-book "ed3"
; Matt K.: Commenting out use of :uncertified-okp after v4-3 in order to
; support provisional certification:
;	       :uncertified-okp nil
	       :defaxioms-okp nil
	       :skip-proofs-okp nil
	       :load-compiled-file nil))

;; AXIOMS
;;; Integral Domain Axioms:

(defthm
  Closure-Laws
  (and (implies (polinomiop x)
		(and (implies (polinomiop y)
			      (and (polinomiop (+ x y))
				   (polinomiop (* x y))))
		     (polinomiop (- x))))
       (polinomiop (nulo))
       (polinomiop (identidad)))
  :rule-classes nil)

(defthm
  Equivalence-Law
  (implies (polinomiop x)
	   (and (= x x)
		(implies (polinomiop y)
			 (and (booleanp (= x y))
			      (implies (= x y)
				       (= y x))
			      (implies (polinomiop z)
				       (implies (and (= x y)
						     (= y z))
						(= x z)))))))
  :rule-classes nil)

(defthm
  Congruence-Laws
  (implies (= y1 y2)
	   (and (iff (polinomiop y1)
		     (polinomiop y2))
		(implies (and (polinomiop y1)
			      (polinomiop y2))
			 (and (implies (polinomiop x)
				       (and (= (+ x y1)
					       (+ x y2))
					    (= (* x y1)
					       (* x y2))))
			      (implies (polinomiop z)
				       (and (= (+ y1 z)
					       (+ y2 z))
					    (= (* y1 z)
					       (* y2 z))))
			      (= (- y1)
				 (- y2))))))
  :rule-classes nil)

(in-theory (disable C_=))

(defthm
  Closure-of-C_=
  (implies (polinomiop x)
	   (polinomiop (C_= x)))
  :rule-classes nil)

(defthm
  Equivalence-class-Laws
  (and (implies (polinomiop x)
		(= (C_= x) x))
       (implies (and (polinomiop y1)
		     (polinomiop y2)
		     (= y1 y2))
		(equal (C_= y1)
		       (C_= y2))))
  :rule-classes nil)

(defthm
  Commutativity-Laws
  (implies (and (polinomiop x)
		(polinomiop y))
	   (and (= (+ x y)
		   (+ y x))
		(= (* x y)
		   (* y x))))
  :rule-classes nil)

(defthm
  Associativity-Laws
  (implies (and (polinomiop x)
		(polinomiop y)
		(polinomiop z))
	   (and (= (+ (+ x y) z)
		   (+ x (+ y z)))
		(= (* (* x y) z)
		   (* x (* y z)))))
  :rule-classes nil)

(defthm
  Left-Distributivity-Law
  (implies (and (polinomiop x)
		(polinomiop y)
		(polinomiop z))
	   (= (* x (+ y z))
	      (+ (* x y)
		 (* x z))))
  :rule-classes nil)

(defthm
  Left-Unicity-Laws
  (implies (polinomiop x)
	   (and (= (+ (nulo) x)
		   x)
		(= (* (identidad) x)
		   x)))
  :rule-classes nil)

(defthm
  Right-Inverse-Law
  (implies (polinomiop x)
	   (= (+ x (- x))
	      (nulo)))
  :rule-classes nil)

(defthm
  Zero-Divisor-Law
  (implies (and (polinomiop x)
		(polinomiop y))
	   (equal (= (* x y)(nulo))
		  (or (= x (nulo))
		      (= y (nulo)))))
  :rule-classes nil)

;; Euclidean Domain Axioms:

(defthm
  Natp-deg-size
  (implies (and (polinomiop x)
		(not (= x (nulo))))
	   (and (integerp (deg x))
		 (>= (deg x) 0)))
  :rule-classes nil)

(defthm
  Congruence-for-deg
  (implies (and (polinomiop y1)
		(polinomiop y2)
		(= y1 y2))
	   (equal (deg y1)
		  (deg y2)))
  :rule-classes nil)

(defthm
  Closure-of-quot-&-rem
  (implies (and (polinomiop x)
		(polinomiop y)
		(not (= y (nulo))))
	   (and (polinomiop (quot x y))
		(polinomiop (rem x y))))
  :rule-classes nil)

(defthm
  Congruence-for-quot-&-rem
  (implies (and (polinomiop y1)
		(polinomiop y2)
		(= y1 y2))
	   (and (implies (and (polinomiop x)
			      (not (= y1 (nulo))))
			 (and (= (quot x y1)
				 (quot x y2))
			      (= (rem x y1)
				 (rem x y2))))
		(implies (and (polinomiop z)
			      (not (= z (nulo))))
			 (and (= (quot y1 z)
				 (quot y2 z))
			      (= (rem y1 z)
				 (rem y2 z))))))
  :rule-classes nil)

(defthm
  Division-property
  (implies (and (polinomiop x)
		(polinomiop y)
		(not (= y (nulo))))
	   (and (= x (+ (* y (quot x y))
			(rem x y)))
		(or (= (rem x y)(nulo))
		    (ACL2::< (deg (rem x y))
			     (deg y)))))
  :rule-classes nil)

(defthm
  Deg-*
  (implies (and (polinomiop x)
		(not (= x (nulo)))
		(polinomiop y)
		(not (= y (nulo))))
	   (<= (deg x)
	       (deg (* x y))))
   :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;
;; Divides-p theory:

;;  Divides-p is defined using quantifiers (defun-sk) and
;;   is non-executable

(defun-sk
  Divides-p (x y)
  (exists z (and (polinomiop x)
		 (polinomiop z)
		 (= (* x z)
		    y))))

;;;;;;;;;;;;;;;;;
;; Unit-p theory:

(defun
  Unit-p (x)
  (divides-p x (identidad)))

(defthm
  |deg identidad =e 0|
  (equal (deg (identidad))
	 0)
  :hints (("Goal"
	   :expand (hide 0)
	   :in-theory (enable deg identidad
			      FUPOL::+M
			      FUMON::monomio
			      FUMON::identidad
			      FUMON::termino
			      FUTER::uno))))

(defthm
  Deg-unit-p=0
  (implies (unit-p x)
	   (equal (deg x)
		  0))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  ACL2::Size-unit-p=Size-1_e
		  (acl2::edp FUPOL::ordenadop)
		  (acl2::=_e =)
		  (acl2::C_=_e C_=)
		  (acl2::binary-+_e +)
		  (acl2::binary-*_e *)
		  (acl2::-_e -)
		  (acl2::0_e nulo)
		  (acl2::1_e identidad)
		  (acl2::size deg)
		  (acl2::q_e quot)
		  (acl2::r_e rem)
		  (acl2::divides-p divides-p)
		  (acl2::divides-p-witness divides-p-witness)
		  (acl2::unit-p unit-p))
		 (acl2::x x)))))

(defthm
  Deg=0-implies-unit-p
  (implies (and (polinomiop x)
		(not (= x (nulo)))
		(equal (deg x)
		       0))
	   (unit-p x))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  ACL2::Size=Size-1_e-implies-unit-p
		  (acl2::edp FUPOL::ordenadop)
		  (acl2::=_e =)
		  (acl2::C_=_e C_=)
		  (acl2::binary-+_e +)
		  (acl2::binary-*_e *)
		  (acl2::-_e -)
		  (acl2::0_e nulo)
		  (acl2::1_e identidad)
		  (acl2::size deg)
		  (acl2::q_e quot)
		  (acl2::r_e rem)
		  (acl2::divides-p divides-p)
		  (acl2::divides-p-witness divides-p-witness)
		  (acl2::unit-p unit-p))
		 (acl2::x x)))))

(defthm
  Deg-<-deg-*
  (implies (and (not (unit-p y))
		(polinomiop x)
		(not (= x (nulo)))
		(polinomiop y)
		(not (= y (nulo))))
	   (ACL2::< (deg x) (deg (* x y))))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 Deg=0-implies-unit-p
		 (x y)))))

;;;;;;;;;;;;;;;;;;;;;;;;
;; Reducible-p and
;; Irreducible-p theory:

;;  Reducible-p is defined using quantifiers (defun-sk) and
;;   is non-executable

(defun-sk
  Reducible-p (x)
  (exists (y z)(and (polinomiop y)
		    (polinomiop z)
		    (not (unit-p y))
		    (not (unit-p z))
		    (= (* y z) x))))

(defun
  Irreducible-p (x)
  (and (polinomiop x)
       (not (unit-p x))
       (not (reducible-p x))))

(defthm
  Irreducible-p-implies-prime-property
  (implies (and (irreducible-p x)
		(polinomiop y)
		(polinomiop z)
		(divides-p x (* y z)))
	   (or (divides-p x y)
	       (divides-p x z)))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 ACL2::Irreducible-p-implies-prime-property
		 (acl2::edp FUPOL::ordenadop)
		 (acl2::=_e =)
		 (acl2::C_=_e C_=)
		 (acl2::binary-+_e +)
		 (acl2::binary-*_e *)
		 (acl2::-_e -)
		 (acl2::0_e nulo)
		 (acl2::1_e identidad)
		 (acl2::size deg)
		 (acl2::q_e quot)
		 (acl2::r_e rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p-witness)
		 (acl2::unit-p unit-p)
		 (acl2::reducible-p reducible-p)
		 (acl2::reducible-p-witness reducible-p-witness)
		 (acl2::irreducible-p irreducible-p))
		(acl2::x x)
		(acl2::y y)
		(acl2::z z)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Factorization existence theory:

(defun
  Irreducible-factors (x)
  "Return a list, lst, of irreducible
   elements of polinomiop, so that if x is
   in polinomiop, x is not (nulo), and x is not
   an unit, then x = product of the
   members in lst."
  (declare (xargs :measure (if (and (polinomiop x)
				    (not (= x (nulo))))
			       (deg x)
			       0)
		  :hints (("subgoal 2"
			   :in-theory (disable (:definition mv-nth)
					       (:definition unit-p)
					       =-implies-equal-deg-a
					       =-implies-equal-deg-b)
			   :use ((:instance
				  Deg-<-deg-*
				  (x (mv-nth 1 (reducible-p-witness x)))
				  (y (mv-nth 0 (reducible-p-witness x))))
				 (:instance
				  =-implies-equal-deg-b
				  (p1 (* (mv-nth 1 (reducible-p-witness x))
					 (mv-nth 0 (reducible-p-witness x))))
				  (p2 x))))
			  ("subgoal 1"
			   :in-theory (disable (:definition mv-nth)
					       (:definition unit-p)
					       =-implies-equal-deg-a
					       =-implies-equal-deg-b)
			   :use ((:instance
				  Deg-<-deg-*
				  (x (mv-nth 0 (reducible-p-witness x)))
				  (y (mv-nth 1 (reducible-p-witness x))))
				 (:instance
				  =-implies-equal-deg-b
				  (p1 (* (mv-nth 0 (reducible-p-witness x))
					 (mv-nth 1 (reducible-p-witness x))))
				  (p2 x)))))))
  (cond ((or (not (polinomiop x))
	     (= x (nulo))
	     (equal (deg x) 0))
	 nil)
	((reducible-p x)
	 (mv-let (y z)
		 (reducible-p-witness x)
		 (append (irreducible-factors y)
			 (irreducible-factors z))))
	(t (list x))))

(defun
  Polinomiop-listp (lst)
  (if (consp lst)
      (and (polinomiop (car lst))
	   (polinomiop-listp (cdr lst)))
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
      (if (polinomiop (car lst))
	  (* (car lst)(*-lst (cdr lst)))
	  (nulo))
      (identidad)))

(defthm
  IRREDUCIBLE-FACTORIZATION-EXISTENCE
  (and (true-listp (irreducible-factors x))
       (polinomiop-listp (irreducible-factors x))
       (irreducible-listp (irreducible-factors x))
       (implies (and (polinomiop x)
		     (not (= x (nulo)))
		     (not (unit-p x)))
		(= (*-lst (irreducible-factors x)) x)))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 ACL2::IRREDUCIBLE-FACTORIZATION-EXISTENCE
		 (acl2::edp FUPOL::ordenadop)
		 (acl2::=_e =)
		 (acl2::C_=_e C_=)
		 (acl2::binary-+_e +)
		 (acl2::binary-*_e *)
		 (acl2::-_e -)
		 (acl2::0_e nulo)
		 (acl2::1_e identidad)
		 (acl2::size deg)
		 (acl2::q_e quot)
		 (acl2::r_e rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p-witness)
		 (acl2::unit-p unit-p)
		 (acl2::reducible-p reducible-p)
		 (acl2::reducible-p-witness reducible-p-witness)
		 (acl2::irreducible-p irreducible-p)
		 (acl2::irreducible-factors irreducible-factors)
		 (acl2::irreducible-listp irreducible-listp)
		 (acl2::edp-listp polinomiop-listp)
		 (acl2::*_e-lst *-lst))
		(acl2::x x)))
	  ("Subgoal 3"
	   :in-theory (disable (:definition irreducible-p)))
	  ("Subgoal 1"
	   :in-theory (e/d (nulo)
			   ((:definition mv-nth)
			    (:definition reducible-p))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unit-associates-p theory:

;;  Unit-associates-p is defined using quantifiers (defun-sk) and
;;   is non-executable

(defun-sk
  Unit-associates-p (x y)
  (exists u (if (and (polinomiop x)
		     (polinomiop y))
		(and (unit-p u)
		     (= (* u x)
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
	   :by (:instance
		(:functional-instance
		 ACL2::Irreducible-p-unit-associates
		 (acl2::edp FUPOL::ordenadop)
		 (acl2::=_e =)
		 (acl2::C_=_e C_=)
		 (acl2::binary-+_e +)
		 (acl2::binary-*_e *)
		 (acl2::-_e -)
		 (acl2::0_e nulo)
		 (acl2::1_e identidad)
		 (acl2::size deg)
		 (acl2::q_e quot)
		 (acl2::r_e rem)
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
	  ("Subgoal 2"
	   :use (:instance
		 unit-associates-p-suff
		 (x acl2::x)
		 (y acl2::y)))))

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

;;  Lisp objects that are bag-equal-unit-associates have the same members
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
		 (acl2::edp FUPOL::ordenadop)
		 (acl2::=_e =)
		 (acl2::C_=_e C_=)
		 (acl2::binary-+_e +)
		 (acl2::binary-*_e *)
		 (acl2::-_e -)
		 (acl2::0_e nulo)
		 (acl2::1_e identidad)
		 (acl2::size deg)
		 (acl2::q_e quot)
		 (acl2::r_e rem)
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
		 (acl2::edp FUPOL::ordenadop)
		 (acl2::=_e =)
		 (acl2::C_=_e C_=)
		 (acl2::binary-+_e +)
		 (acl2::binary-*_e *)
		 (acl2::-_e -)
		 (acl2::0_e nulo)
		 (acl2::1_e identidad)
		 (acl2::size deg)
		 (acl2::q_e quot)
		 (acl2::r_e rem)
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
	  (ACL2::+ 1 (multiplicity-unit-associate x (cdr lst)))
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
		 (acl2::edp FUPOL::ordenadop)
		 (acl2::=_e =)
		 (acl2::C_=_e C_=)
		 (acl2::binary-+_e +)
		 (acl2::binary-*_e *)
		 (acl2::-_e -)
		 (acl2::0_e nulo)
		 (acl2::1_e identidad)
		 (acl2::size deg)
		 (acl2::q_e quot)
		 (acl2::r_e rem)
		 (acl2::divides-p divides-p)
		 (acl2::divides-p-witness divides-p-witness)
		 (acl2::unit-p unit-p)
		 (acl2::unit-associates-p unit-associates-p)
		 (acl2::unit-associates-p-witness unit-associates-p-witness)
		 (acl2::Member-unit-associate Member-unit-associate)
		 (acl2::Delete-one-unit-associate Delete-one-unit-associate)
		 (acl2::Bag-equal-unit-associates Bag-equal-unit-associates)
		 (acl2::multiplicity-unit-associate multiplicity-unit-associate))
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
		 ACL2::IRREDUCIBLE-FACTORIZATION-UNIQUENESS-general
		 (acl2::edp FUPOL::ordenadop)
		 (acl2::=_e =)
		 (acl2::C_=_e C_=)
		 (acl2::binary-+_e +)
		 (acl2::binary-*_e *)
		 (acl2::-_e -)
		 (acl2::0_e nulo)
		 (acl2::1_e identidad)
		 (acl2::size deg)
		 (acl2::q_e quot)
		 (acl2::r_e rem)
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
		(= (*-lst lst1)
		   (*-lst lst2)))
	   (bag-equal-unit-associates lst1 lst2))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		(:functional-instance
		 ACL2::IRREDUCIBLE-FACTORIZATION-UNIQUENESS
		 (acl2::edp FUPOL::ordenadop)
		 (acl2::=_e =)
		 (acl2::C_=_e C_=)
		 (acl2::binary-+_e +)
		 (acl2::binary-*_e *)
		 (acl2::-_e -)
		 (acl2::0_e nulo)
		 (acl2::1_e identidad)
		 (acl2::size deg)
		 (acl2::q_e quot)
		 (acl2::r_e rem)
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
