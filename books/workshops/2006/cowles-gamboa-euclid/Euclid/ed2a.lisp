; ACL2 Euclidean Domain books -- Book 2a -- Multiplicative Size Property
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

(certify-book "ed2a"
	      0
	      nil ;;compile-flg
	      )
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
;; This book assumes the result reported in ed1.lisp which is Book 1 of
;; ACL2 Euclidean Domain books

;;                  Multiplicative Identity Existence

;; That is, every Euclidean Domain has a multiplicative identity.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Below it is shown that there is no loss of generality in assuming
;;  Multiplicative Size Property:

;;     For all nonzero domain elements x and y, Size(x) <= Size(xy).

;;     If the original Size function does not satisfy this property,
;;     then it (and the original quotient and remainder) can replaced
;;     by ``new'' operations that do satisfy this and the division property.

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Make temporary use of an ACL2 Arithmetic Book to help certify this book,

(local
 (include-book "arithmetic/top" :dir :system
; Matt K.: Commenting out use of :uncertified-okp after v4-3 in order to
; support provisional certification:
;	       :uncertified-okp nil
	       :defaxioms-okp nil
	       :skip-proofs-okp nil))

(encapsulate
 ; Signatures
 (((edp *) => *)          ; x is in Euclidean Domain iff (NOT (EQUAL (edp x) NIL)).
  ((=_e * *) => *)        ; Equality predicate for Euclidean Domain elements.
  ((C_=_e *) => *)        ; Choose unique equivalence class representative for =_e.
  ((+_e * *) => *)        ; Addition in Euclidean Domain.
  ((*_e * *) => *)        ; Multiplication in Euclidean Domain.
  ((-_e *) => *)          ; Unary minus in Euclidean Domain.
  ((0_e) => *)            ; 0 element in Euclidean Domain.
  ((1_e) => *)            ; 1 element in Euclidean Domain.
  ((size1 *) => *)        ; Natp size of each nonzero Euclidean Domain element.
  ((q1_e * *) => *)       ; Quotient in Euclidean Domain.
  ((r1_e * *) => *))      ; Remainder in Euclidean Domain.

 ; Witnesses:
 (local (defun
	  edp (x)
	  (rationalp x)))

 (local (defun
	  =_e (x y)
	  (equal x y)))

 (local (defun
	  C_=_e (x)
	  (identity x)))

 (local (defun
	  +_e (x y)
	  (+ x y)))

 (local (defun
	  *_e (x y)
	  (* x y)))

 (local (defun
	  -_e (x)
	  (- x)))

 (local (defun
	  0_e ()
	  0))

 (local (defun
	  1_e ()
	  1))

 (local (defun
	  size1 (x)
	  (declare (ignore x))
	  0))

 (local (defun
	  q1_e (x y)
	  (/ x y)))

 (local (defun
	  r1_e (x y)
	  (declare (ignore x y))
	  0))

 ; AXIOMS
 ; Integral Domain Axioms:
 (defthm
   Closure-Laws
   (and (implies (edp x)
		 (and (implies (edp y)
			       (and (edp (+_e x y))
				    (edp (*_e x y))))
		      (edp (-_e x))))
	(edp (0_e))
	(edp (1_e))))

 (defthm
    Equivalence-Law
    (implies (edp x)
	     (and (=_e x x)
		  (implies (edp y)
			   (and (booleanp (=_e x y))
				(implies (=_e x y)
					 (=_e y x))
				(implies (edp z)
					 (implies (and (=_e x y)
						       (=_e y z))
						  (=_e x z))))))))

 (defthm
   Congruence-Laws
   (implies (and (edp y1)
		 (edp y2)
		 (=_e y1 y2))
	    (and (implies (edp x)
			  (and (=_e (+_e x y1)
				    (+_e x y2))
			       (=_e (*_e x y1)
				    (*_e x y2))))
		 (implies (edp z)
			  (and (=_e (+_e y1 z)
				    (+_e y2 z))
			       (=_e (*_e y1 z)
				    (*_e y2 z))))
		 (=_e (-_e y1)
		      (-_e y2))))
   :rule-classes nil)

 (defthm
   Closure-of-C_=_e
   (implies (edp x)
	    (edp (C_=_e x))))

 (defthm
   Equivalence-class-Laws
   (and (implies (edp x)
		 (=_e (C_=_e x) x))
	(implies (and (edp y1)
		      (edp y2)
		      (=_e y1 y2))
		 (equal (C_=_e y1)
			(C_=_e y2))))
   :rule-classes nil)

 (defthm
   Commutativity-Laws
   (implies (and (edp x)
		 (edp y))
	    (and (=_e (+_e x y)
		      (+_e y x))
		 (=_e (*_e x y)
		      (*_e y x)))))

 (defthm
   Associativity-Laws
   (implies (and (edp x)
		 (edp y)
		 (edp z))
	    (and (=_e (+_e (+_e x y) z)
		      (+_e x (+_e y z)))
		 (=_e (*_e (*_e x y) z)
		      (*_e x (*_e y z))))))

 (defthm
   Left-Distributivity-Law
   (implies (and (edp x)
		 (edp y)
		 (edp z))
	    (=_e (*_e x (+_e y z))
		 (+_e (*_e x y)
		      (*_e x z)))))

 (defthm
   Left-Unicity-Laws
   (implies (edp x)
	    (and (=_e (+_e (0_e) x)
		      x)
		 (=_e (*_e (1_e) x)
		      x))))

 (defthm
   Right-Inverse-Law
   (implies (edp x)
	    (=_e (+_e x (-_e x))
		 (0_e))))

 (defthm
   Zero-Divisor-Law
   (implies (and (edp x)
		 (edp y))
	    (equal (=_e (*_e x y)(0_e))
		   (or (=_e x (0_e))
		       (=_e y (0_e))))))

 ; Euclidean Domain Axioms:
 (defthm
   Natp-size1
   (implies (and (edp x)
		 (not (=_e x (0_e))))
	    (and (integerp (size1 x))
		 (>= (size1 x) 0)))
   :rule-classes (:type-prescription
		  :rewrite))

 (defthm
   Congruence-for-Size1
   (implies (and (edp y1)
		 (edp y2)
		 (=_e y1 y2))
	    (equal (size1 y1)
		   (size1 y2)))
   :rule-classes nil)

 (defthm
   Closure-of-q1_e-&-r1_e
   (implies (and (edp x)
		 (edp y)
		 (not (=_e y (0_e))))
	    (and (edp (q1_e x y))
		 (edp (r1_e x y)))))

 (defthm
   Congruence-for-q1_e-&-r1_e
   (implies (and (edp y1)
		 (edp y2)
		 (=_e y1 y2))
	    (and (implies (and (edp x)
			       (not (=_e y1 (0_e))))
			  (and (=_e (q1_e x y1)
				    (q1_e x y2))
			       (=_e (r1_e x y1)
				    (r1_e x y2))))
		 (implies (and (edp z)
			       (not (=_e z (0_e))))
			  (and (=_e (q1_e y1 z)
				    (q1_e y2 z))
			       (=_e (r1_e y1 z)
				    (r1_e y2 z))))))
   :rule-classes nil)

 (defthm
   Division-property
   (implies (and (edp x)
                 (edp y)
                 (not (=_e y (0_e))))
            (and (=_e x (+_e (*_e y (q1_e x y))
			     (r1_e x y)))
                 (or (=_e (r1_e x y)(0_e))
                     (< (size1 (r1_e x y))
                        (size1 y)))))
   :rule-classes nil)
 ) ; end encapsulate

(defun
  ==_e (x1 x2)
  "==_e nicely extends =_e
   to entire ACL2 universe."
  (if (edp x1)
      (if (edp x2)
	  (=_e x1 x2)
	  nil)
      (if (edp x2)
	  nil
	  (equal x1 x2))))

(defun
  ++_e (x y)
  "++_e nicely extends +_e
   to entire ACL2 universe."
  (if (and (edp x)
	   (edp y))
      (+_e x y)
      x))

(defun
  **_e (x y)
  "**_e nicely extends *_e
   to entire ACL2 universe."
  (if (and (edp x)
	   (edp y))
      (*_e x y)
      x))

;; Restate Euclidean Domain Laws in
;;  terms of ==_e, C_==_e, ++_e, and **_e
;;  in place of =_e, C_=_e, +_e, +_e, and *_e.

(defthm
  Closure-Laws-for-++_e-&-**_e
  (implies (and (edp x)
		(edp y))
	   (and (edp (++_e x y))
		(edp (**_e x y)))))

(defthm
  ==_e-Equivalence-Law
  (and (booleanp (==_e x y))
       (==_e x x)
       (implies (==_e x y)
		(==_e y x))
       (implies (and (==_e x y)
		     (==_e y z))
		(==_e x z)))
  :rule-classes :equivalence)

(defthm
   ==_e-implies-iff-edp
   (implies (==_e y1 y2)
	    (iff (edp y1)
		 (edp y2)))
   :rule-classes :congruence)

(defthm
   ==_e-implies-==_e-++_e-1
   (implies (==_e y1 y2)
	    (==_e (++_e y1 z)
		  (++_e y2 z)))
   :rule-classes :congruence
   :hints (("Goal"
	    :use congruence-laws)))

(defthm
   ==_e-implies-==_e-++_e-2
   (implies (==_e y1 y2)
	    (==_e (++_e x y1)
		  (++_e x y2)))
   :rule-classes :congruence
   :hints (("Goal"
	    :use congruence-laws)))

(defthm
   ==_e-implies-==_e-**_e-1
   (implies (==_e y1 y2)
	    (==_e (**_e y1 z)
		  (**_e y2 z)))
   :rule-classes :congruence
   :hints (("Goal"
	    :use congruence-laws)))

(defthm
   ==_e-implies-==_e-**_e-2
   (implies (==_e y1 y2)
	    (==_e (**_e x y1)
		  (**_e x y2)))
   :rule-classes :congruence
   :hints (("Goal"
	    :use congruence-laws)))

(defun
  C_==_e (x)
  "C_==_e nicely extends C_=_e
   to entire ACL2 universe."
  (if (edp x)
      (C_=_e x)
      x))

(defthm
  ==_e-C_==_e
  (==_e (C_==_e x) x)
  :hints (("Goal"
	   :use Equivalence-class-Laws)))

(defthm
  ==_e-implies-equal-C_==_e
  (implies (==_e y1 y2)
	   (equal (C_==_e y1)
		  (C_==_e y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Equivalence-class-Laws)))

(defthm
  Commutativity-Laws-for-++_e-&-**_e
  (implies (and (edp x)
		(edp y))
	   (and (==_e (++_e x y)
		      (++_e y x))
		(==_e (**_e x y)
		      (**_e y x)))))

(defthm
  Associativity-Laws-for-++_e-&-**_e
  (implies (and (edp x)
		(edp y)
		(edp z))
	   (and (==_e (++_e (++_e x y) z)
		      (++_e x (++_e y z)))
		(==_e (**_e (**_e x y) z)
		      (**_e x (**_e y z)))))
  :hints (("Goal"
	   :in-theory (disable Commutativity-Laws-for-++_e-&-**_e))))

(defthm
  Left-Distributivity-Law-for-++_e-&-**_e
  (implies (and (edp x)
		(edp y)
		(edp z))
	   (==_e (**_e x (++_e y z))
		 (++_e (**_e x y)
		       (**_e x z)))))

(defthm
   Left-Unicity-Laws-for-++_e-&-**_e
   (implies (edp x)
	    (and (==_e (++_e (0_e) x)
		       x)
		 (==_e (**_e (1_e) x)
		       x))))

(defthm
  Right-Inverse-Law-for-++_e
  (implies (edp x)
	   (==_e (++_e x (-_e x))
		 (0_e))))

(defthm
  Zero-Divisor-Law-for-**_e
  (implies (and (edp x)
		(edp y))
	   (equal (==_e (**_e x y)(0_e))
		  (or (==_e x (0_e))
		      (==_e y (0_e))))))

(defthm
  Natp-size1-==_e
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (integerp (size1 x))
		(>= (size1 x) 0)))
  :rule-classes (:type-prescription
		 :rewrite))

(defthm
  ==_e-implies-equal-size1
  (implies (==_e y1 y2)
	   (equal (size1 y1)
		  (size1 y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-for-Size1)))

(defun
  qq_e (x y)
  "qq_e nicely extends q1_e
   to entire ACL2 universe."
  (if (and (edp x)
	   (edp y)
	   (not (==_e y (0_e))))
      (q1_e x y)
      x))

(defun
  rr_e (x y)
  "rr_e nicely extends r1_e
   to entire ACL2 universe."
  (if (and (edp x)
	   (edp y)
	   (not (==_e y (0_e))))
      (r1_e x y)
      x))

(defthm
  Closure-of-qq_e-&-rr_e
  (implies (and (edp x)
		(edp y)
		(not (==_e y (0_e))))
	   (and (edp (qq_e x y))
		(edp (rr_e x y)))))

(defthm
  ==_e-implies-==_e-qq_e-1
  (implies (==_e y1 y2)
	   (==_e (qq_e y1 z)
		 (qq_e y2 z)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-for-q1_e-&-r1_e)))

(defthm
  ==_e-implies-==_e-qq_e-2
  (implies (==_e y1 y2)
	   (==_e (qq_e x y1)
		 (qq_e x y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-for-q1_e-&-r1_e)))

(defthm
  ==_e-implies-==_e-rr_e-1
  (implies (==_e y1 y2)
	   (==_e (rr_e y1 z)
		 (rr_e y2 z)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-for-q1_e-&-r1_e)))

(defthm
  ==_e-implies-==_e-rr_e-2
  (implies (==_e y1 y2)
	   (==_e (rr_e x y1)
		 (rr_e x y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-for-q1_e-&-r1_e)))

(defthm
  Division-property-for-qq_e-&-rr_e
  (implies (and (edp x)
		(edp y)
		(not (==_e y (0_e))))
	   (and (==_e x (++_e (**_e y (qq_e x y))
			      (rr_e x y)))
		(or (==_e (rr_e x y)(0_e))
		    (< (size1 (rr_e x y))
		       (size1 y)))))
   :rule-classes nil
   :hints (("Goal"
	    :in-theory (disable commutativity-laws-for-++_e-&-**_e)
	    :use Division-property)))

(in-theory (disable (:definition ==_e)
		    (:definition ++_e)
		    (:definition **_e)
		    (:definition C_==_e)
		    (:definition qq_e)
		    (:definition rr_e)))

(defthm
  Equal-C_==_e-implies-==_e
  (implies (equal (C_==_e y1)
		  (C_==_e y2))
	   (==_e y1 y2))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable ==_e-C_==_e)
	   :use ((:instance
		  ==_e-C_==_e
		  (x y1))
		 (:instance
		  ==_e-C_==_e
		  (x y2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This book constucts, for any Euclidean domain,
;;                <edp, =_e, C_=_e, +_e, *_e, -_e, 0_e, size1, q1_e, r1_e>,
;; functions size, q_e, and r_e such that

;;    (implies (and (edp x)
;;                  (not (=_e x (0_e))))
;;             (and (integerp (size x))
;;                  (>= (size x) 0)))

;;    (implies (and (edp y1)
;;                  (edp y2)
;;                  (=_e y1 y2))
;;             (equal (size y1)
;;                    (size y2)))

;;    (implies (and (edp x)
;;                  (edp y)
;;                  (not (=_e y (0_e))))
;;             (and (edp (q_e x y))
;;                  (edp (r_e x y)))))

;;    (implies (and (edp y1)
;;                  (edp y2)
;;                  (=_e y1 y2))
;;             (and (implies (and (edp x)
;;                                (not (=_e y1 (0_e))))
;;                           (and (=_e (q_e x y1)
;;                                     (q_e x y2))
;;                                (=_e (r_e x y1)
;;                                     (r_e x y2))))
;;                  (implies (and (edp z)
;;                                (not (=_e z (0_e))))
;;                           (and (=_e (q_e y1 z)
;;                                     (q_e y2 z))
;;                                (=_e (r_e y1 z)
;;                                     (r_e y2 z))))))

;;    (implies (and (edp x)
;;                  (edp y)
;;                  (not (=_e y (0_e))))
;;             (and (=_e x (+_e (*_e y (q_e x y))
;;                              (r_e x y)))
;;                  (or (=_e (r_e x y)(0_e))
;;                      (< (size (r_e x y))
;;                         (size y)))))

;;    (implies (and (edp x)
;; 	       (not (=_e x (0_e)))
;; 	       (edp y)
;; 	       (not (=_e y (0_e))))
;; 	    (<= (size x)
;; 		(size (*_e x y))))

;; Outline of a proof.

;; Simplify the argument by taking =_e to be equality (and =_e-cl
;;  to be the identity function.

;; If the domain contains only one element (0_e), then the above
;; properties vacuously hold.

;; Otherwise the domain contains a nonzero element.
;;  For each nonzero domain element, x, choose a nonzero domain
;;  element c(x) such that (size1 (*_e x (c x))) is as small as possible.

;;  Let (size x) = (size1 (*_e x (c x))),
;;      (q_e x y) = (*_e (c y)
;;                       (q1_e x (*_e y (c y))))
;;      (r_e x y) = (r1_e x (*_e y (c y)))

;;  Then x = (+_e (*_e (*_e (*_e y (c y))
;;                          (q1_e x (*_e y (c y)))))
;;                (r1_e x (*_e y (cy))))
;;         = (+_e (*_e y
;;                     (*_e (c y)
;;                          (q1_e x (*_e y (c y)))))
;;                (r1_e x (*_e y (cy))))
;;         = (+_e (*_e y
;;                     (q_e x y))
;;                (r_e x y)).
;;   and (r_e x y) = (r1_e x (*_e y (cy))) = (0_e)
;;    or (size (r_e x y)) = (size1 (*_e (r_e x y)(c (r_e x y))))
;;                       <= (size1 (*_e (r_e x y)(1_e)))
;;                        = (size1 (r_e x y))
;;                        = (size1 (r1_e x (*_e y (c y))))
;;                        < (size1 (*_e y (c y)))
;;                        = (size y)

;;    Also (size x) = (size1 (*_e x (c x)))
;;                 <= (size1 (*_e x (*_e y (c (*_e x y)))))
;;                  = (size1 (*_e (*_e x y)(c (*_e x y))))
;;                  = (size (*_e x y))

;;For each nonzero element x, choose a nonzero element c of edp
;; so that the product (**_e x c) has Size1 n (if it exists).
(defchoose
  c_e (y)(x n)
  (and (edp x)
       (not (==_e x (0_e)))
       (edp y)
       (not (==_e y (0_e)))
       (equal (Size1 (**_e x y))(nfix n))))

(defthm
  c_e-property
  (implies (and (integerp n)
		(>= n 0)
		(edp x)
		(not (==_e x (0_e)))
		(edp y)
		(not (==_e y (0_e)))
		(equal (size1 (**_e x y)) n))
	   (and (edp (c_e x n))
		(not (==_e (c_e x n)(0_e)))
		(equal (size1 (**_e x (c_e x n))) n)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp n)
				(>= n 0)
				(edp x)
				(not (==_e x (0_e)))
				(equal (size1 (**_e x y)) n)
				(not (==_e y (0_e)))
				(edp y))
			   (and (edp (c_e x n))
				(not (==_e (c_e x n)(0_e)))
				(equal (size1 (**_e x (c_e x n))) n)))))
  :hints (("Goal"
	   :use c_e)))

(defthm
  C_e-properties-Size1
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y)
		(not (==_e y (0_e))))
	   (and (edp (c_e x (size1 (**_e x y))))
		(not (==_e (c_e x (size1 (**_e x y)))(0_e)))
		(equal (size1 (**_e x
				    (c_e x (size1 (**_e x y)))))
		       (size1 (**_e x y)))))
  :hints (("Goal"
	   :use (:instance
		 c_e-property
		 (n (size1 (**_e x y)))))))

(defthm
  Nullity-Laws
  (implies (edp x)
	   (and (==_e (**_e (0_e) x)
		      (0_e))
		(==_e (**_e x (0_e))
		      (0_e)))))

(defthm
  1_e-0_e
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (not (==_e (1_e)(0_e))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (not (==_e x (0_e)))
				(edp x))
			   (not (==_e (1_e)(0_e))))))
  :hints (("Goal"
	   :use left-unicity-laws-for-++_e-&-**_e)))

(defthm
  C_e-properties-Size1-1_e
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (edp (c_e x (Size1 x)))
		(not (==_e (c_e x (size1 x))(0_e)))
		(equal (size1 (**_e x
				    (c_e x (size1 x))))
		       (size1 x))))
  :hints (("Goal"
	   :use (:instance
		 C_e-properties-Size1
		 (y (1_e))))))

(defun
  Find-smallest-n (x n)
  "Find smallest natp n such that (c_e x n) is a nonzero element
   of edp and (Size1 (**_e x (c_e x n))=n (if it exists)."
  (declare (xargs :measure (let ((n (nfix n)))
			            (nfix (- (Size1 x) n)))))
  (if (and (edp x)
	   (not (==_e x (0_e))))
      (let ((n (nfix n)))
	   (if (and (< n (size1 x))
		    (not (and (edp (c_e x n))
			      (not (==_e (c_e x n)(0_e)))
			      (equal (size1 (**_e x (c_e x n)))
				     n))))
	       (Find-smallest-n x (+ n 1))
	       n))
      n))

(in-theory (disable (:executable-counterpart Find-smallest-n)))

(defthm
  Integerp-Find-smallest-n
  (implies (integerp n)
	   (integerp (Find-smallest-n x n)))
  :rule-classes :type-prescription)

(defthm
  Natp-Find-smallest-n
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (integerp (Find-smallest-n x n))
		(>= (Find-smallest-n x n) 0)))
  :rule-classes :type-prescription)

(defthm
  Find-smallest-n-Size1-x
  (implies (<= n (Size1 x))
	   (<= (Find-smallest-n x n)
	       (Size1 x))))

(defthm
  C_e-Find-smallest-n
  (implies (and (integerp n)
		(<= 0 n)
		(<= n (Size1 x))
		(edp x)
		(not (==_e x (0_e))))
	   (and (edp (c_e x (Find-smallest-n x n)))
		(not (==_e (c_e x (Find-smallest-n x n))(0_e)))
		(equal (Size1 (**_e x (c_e x (Find-smallest-n x n))))
		       (Find-smallest-n x n)))))

(defthm
  Not-Size1-c_e-n-=-n
  (implies (and (integerp k)
		(integerp n)
		(<= 0 k)
		(<= k n)
		(< n (Find-smallest-n x k))
		(edp x)
		(not (==_e x (0_e))))
	   (not (and (edp (c_e x n))
		     (not (==_e (c_e x n)(0_e)))
		     (equal (Size1 (**_e x (c_e x n)))
			    n))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (< n (Find-smallest-n x k))
				(integerp k)
				(integerp n)
				(<= 0 k)
				(<= k n)
				(edp x)
				(not (==_e x (0_e)))
				(edp (c_e x n))
				(not (==_e (c_e x n)(0_e))))
			   (not (equal (Size1 (**_e x (c_e x n)))
				       n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (Find-smallest-n x 0)
;;   finds the smallest natp n such that (Size1 (*_e x (c_e x n))=n
;;   (if it exists).

;; Thus if there are nonzero elements in edp, then some nonzero element,
;;  namely (c_e x (Find-smallest-n x 0)), has the property that
;;  (Size1 (*_e x (c_e x (Find-smallest-n x n))))=(Find-smallest-n x n)
;;  and for any nonzero element, y, of edp,
;;  (Size1 (*_e x y)) >= (Find-smallest-n x n).

(defthm
  Natp-Find-smallest-n-0
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (integerp (Find-smallest-n x 0))
		(>= (Find-smallest-n x 0) 0)))
  :rule-classes nil)

(defthm
  C_e-Find-smallest-n-0
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (edp (c_e x (Find-smallest-n x 0)))
		(not (==_e (c_e x (Find-smallest-n x 0))(0_e)))
		(equal (Size1 (**_e x (c_e x (Find-smallest-n x 0))))
		       (Find-smallest-n x 0)))))

(defthm
  Not-Size1-c_e-n-=-n-1
  (implies (and (integerp n)
		(<= 0 n)
		(< n (Find-smallest-n x 0))
		(edp x)
		(not (==_e x (0_e))))
	   (not (and (edp (c_e x n))
		     (not (==_e (c_e x n)(0_e)))
		     (equal (Size1 (**_e x (c_e x n)))
			    n))))
  :rule-classes nil)

(defthm
  Size1->=-Find-smallest-n-0
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y)
		(not (==_e y (0_e))))
	   (>= (Size1 (**_e x y))(Find-smallest-n x 0)))
  :rule-classes (:rewrite
		 :linear)
  :hints (("Goal"
	   :use (:instance
		 Not-Size1-c_e-n-=-n-1
		 (n (Size1 (**_e x y)))))))

(defthm
  ==_e-implies-<=-Size1-**_e-c-e-find-smallest-n
  (implies (and (edp x1)
		(not (==_e x1 (0_e)))
		(==_e x1 x2))
	   (<= (Size1 (**_e x1 (c_e x1 (Find-smallest-n x1 0))))
	       (Size1 (**_e x2 (c_e x2 (Find-smallest-n x2 0))))))
  :rule-classes nil)

(defthm
  ==_e-implies-equal-Size1-**_e-c-e-find-smallest-n
  (implies (and (edp x1)
		(not (==_e x1 (0_e)))
		(==_e x1 x2))
	   (equal (Size1 (**_e x1 (c_e x1 (Find-smallest-n x1 0))))
		  (Size1 (**_e x2 (c_e x2 (Find-smallest-n x2 0))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (==_e-implies-<=-Size1-**_e-c-e-find-smallest-n
		 (:instance
		  ==_e-implies-<=-Size1-**_e-c-e-find-smallest-n
		  (x1 x2)
		  (x2 x1))))
	  ("[1]Goal"
	   :use (:theorem
		 (implies (and (edp x1)
			       (not (==_e x1 (0_e)))
			       (==_e x2 x1))
			  (integerp (Size1 (**_e x1
						(c_e x2
						     (Find-smallest-n x2 0))))))))))

(defthm
  ==_e-implies-equal-Find-smallest-n-0
  (implies (and (edp x1)
		(not (==_e x1 (0_e)))
		(==_e x1 x2))
	   (equal (Find-smallest-n x1 0)
		  (Find-smallest-n x2 0)))
  :rule-classes nil
  :hints (("goal"
	   :in-theory (disable c_e-find-smallest-n-0
			       c_e-find-smallest-n)
	   :use (==_e-implies-equal-size1-**_e-c-e-find-smallest-n
		 (:instance
		   c_e-find-smallest-n-0
		   (x x1))
		 (:instance
		   c_e-find-smallest-n-0
		   (x x2))))))

(defthm
  ==_e-implies-equal-Size1-**_e-c-e-find-smallest-n-a
  (implies (and (edp x1)
		(not (==_e x1 (0_e)))
		(==_e x1 x2))
	   (equal (Size1 (**_e x1 (c_e x2 (Find-smallest-n x2 0))))
		  (Size1 (**_e x1 (c_e x1 (Find-smallest-n x1 0))))))
  :rule-classes nil
  :hints (("Goal"
	   :use ==_e-implies-equal-Size1-**_e-c-e-find-smallest-n)))

(defthm
  ==_e-implies-equal-Size1-**_e-c-e-find-smallest-n-b
  (implies (and (edp x1)
		(not (==_e x1 (0_e)))
		(==_e x1 x2)
		(==_e x1 x3))
	   (equal (Size1 (**_e x1 (c_e x2 (Find-smallest-n x3 0))))
		  (Size1 (**_e x1 (c_e x1 (Find-smallest-n x1 0))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (==_e-implies-equal-Size1-**_e-c-e-find-smallest-n-a
		 (:instance
		  ==_e-implies-equal-Find-smallest-n-0
		  (x1 x2)
		  (x2 x3))))))

(defthm
  C_e-Find-smallest-n-0-C_=_e
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (edp (c_e (C_==_e x)(Find-smallest-n (C_==_e x) 0)))
		(not (==_e (c_e (C_==_e x)(Find-smallest-n (C_==_e x) 0))(0_e)))
		(equal (Size1 (**_e x (c_e (C_==_e x)(Find-smallest-n (C_==_e x)
								      0))))
		       (Find-smallest-n (C_==_e x) 0))))
  :hints (("Goal"
	   :in-theory (disable C_e-Find-smallest-n-0)
	   :use (:instance
		 C_e-Find-smallest-n-0
		 (x (C_==_e x))))))

(defun
  Size (x)
  (Size1 (**_e x
	       (c_e (C_==_e x)(Find-smallest-n (C_==_e x) 0)))))

(in-theory (disable (:executable-counterpart Size)))

(defun
  q_e (x y)
  (**_e (c_e (C_==_e y)(Find-smallest-n (C_==_e y) 0))
	(qq_e x (**_e y
		      (c_e (C_==_e y)(Find-smallest-n (C_==_e y) 0))))))

(in-theory (disable (:executable-counterpart q_e)))

(defun
  r_e (x y)
  (rr_e x (**_e y
		(c_e (C_==_e y)(Find-smallest-n (C_==_e y) 0)))))

(in-theory (disable (:executable-counterpart r_e)))

(defthm
  Natp-size-==_e
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (integerp (size x))
		(>= (size x) 0)))
  :rule-classes nil)

(defthm
  Congruence-for-Size-==_e
  (implies (and (edp y1)
		(edp y2)
		(==_e y1 y2))
	   (equal (size y1)
		  (size y2)))
  :rule-classes nil)

(defthm
  Closure-of-q_e-&-r_e-==_e
  (implies (and (edp x)
		(edp y)
		(not (==_e y (0_e))))
	   (and (edp (q_e x y))
		(edp (r_e x y))))
  :rule-classes nil)

(defthm
  Congruence-for-q_e-&-r_e-==_e
  (implies (and (edp y1)
		(edp y2)
		(==_e y1 y2))
	   (and (implies (edp x)
			 (and (==_e (q_e x y1)
				    (q_e x y2))
			      (==_e (r_e x y1)
				    (r_e x y2))))
		(implies (edp z)
			 (and (==_e (q_e y1 z)
				    (q_e y2 z))
			      (==_e (r_e y1 z)
				    (r_e y2 z))))))
  :rule-classes nil)

(defthm
  Division-property-q_e-&-r_e-==_e
  (implies (and (edp x)
		(edp y)
		(not (==_e y (0_e))))
	   (and (==_e x (++_e (**_e y (q_e x y))
			      (r_e x y)))
		(or (==_e (r_e x y)(0_e))
		    (< (size (r_e x y))
		       (size y)))))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 Division-property-for-qq_e-&-rr_e
		 (y (**_e y
			  (c_e (C_==_e y)(Find-smallest-n (C_==_e y) 0))))))
	  ("Subgoal 1"
	   :in-theory (disable Find-smallest-n-Size1-x)
	   :use ((:instance
		  Find-smallest-n-Size1-x
		  (n 0)
		  (x (rr_e x
			   (**_e y (c_e (C_==_e y)
					(find-smallest-n (C_==_e y) 0))))))
		 (:instance
		  ==_e-implies-equal-Find-smallest-n-0
		  (x2 (C_==_e
		       (rr_e x
			     (**_e y (c_e (C_==_e y)
					  (find-smallest-n (C_==_e y) 0))))))
		  (x1 (rr_e x
			    (**_e y (c_e (C_==_e y)
					 (find-smallest-n (C_==_e y) 0))))))))))

(defthm
  Size-**_e-property-==_e
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y)
		(not (==_e y (0_e))))
	   (<= (size x)
	       (size (**_e x y))))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 ==_e-implies-equal-Find-smallest-n-0
		 (x1 x)
		 (x2 (C_==_e x))))))

(in-theory (e/d ((:definition ==_e)
		 (:definition ++_e)
		 (:definition **_e))
		((:definition size)
		 (:definition q_e)
		 (:definition r_e))))

; Euclidean Domain Axioms:

(defthm
  Natp-size
  (implies (and (edp x)
		(not (=_e x (0_e))))
	   (and (integerp (size x))
		(>= (size x) 0)))
  :rule-classes nil
  :hints (("Goal"
	   :use Natp-size-==_e)))

(defthm
  Congruence-for-Size
  (implies (and (edp y1)
		(edp y2)
		(=_e y1 y2))
	   (equal (size y1)
		  (size y2)))
  :rule-classes nil
  :hints (("Goal"
	   :use Congruence-for-Size-==_e)))

(defthm
  Closure-of-q_e-&-r_e
  (implies (and (edp x)
		(edp y)
		(not (=_e y (0_e))))
	   (and (edp (q_e x y))
		(edp (r_e x y))))
  :hints (("Goal"
	   :use Closure-of-q_e-&-r_e-==_e)))

(defthm
  Congruence-for-q_e-&-r_e
  (implies (and (edp y1)
		(edp y2)
		(=_e y1 y2))
	   (and (implies (and (edp x)
			      (not (=_e y1 (0_e))))
			 (and (=_e (q_e x y1)
				   (q_e x y2))
			      (=_e (r_e x y1)
				   (r_e x y2))))
		(implies (and (edp z)
			      (not (=_e z (0_e))))
			 (and (=_e (q_e y1 z)
				   (q_e y2 z))
			      (=_e (r_e y1 z)
				   (r_e y2 z))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (Congruence-for-q_e-&-r_e-==_e))))

(defthm
  Division-property-q_e-&-r_e
  (implies (and (edp x)
		(edp y)
		(not (=_e y (0_e))))
	   (and (=_e x (+_e (*_e y (q_e x y))
			    (r_e x y)))
		(or (=_e (r_e x y)(0_e))
		    (< (size (r_e x y))
		       (size y)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable commutativity-laws-for-++_e-&-**_e)
	   :use Division-property-q_e-&-r_e-==_e)))

(defthm
  Size-*_e-property
  (implies (and (edp x)
		(not (=_e x (0_e)))
		(edp y)
		(not (=_e y (0_e))))
	   (<= (size x)
	       (size (*_e x y))))
  :rule-classes nil
  :hints (("Goal"
	   :use Size-**_e-property-==_e)))
