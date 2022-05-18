; ACL2 Euclidean Domain books -- Book 1 -- Multiplicative Identity Existence
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
To certify this book, first, create a world with the following package:

(DEFPKG "ACL2-ASG"
  (SET-DIFFERENCE-EQUAL
   (UNION-EQ *ACL2-EXPORTS*
	     *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*)
   '(ZERO)))

(certify-book "ed1"
	      1
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
;; This book shows that:

;;  Every Euclidean Domain has a multiplicative identity.

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

(local (include-book "cowles/acl2-crg" :dir :system))

(encapsulate
 ; Signatures
 (((edp *) => *)          ; x is in Euclidean Domain iff (NOT (EQUAL (edp x) NIL)).
  ((=_e * *) => *)        ; Equality predicate for Euclidean Domain elements.
  ((+_e * *) => *)        ; Addition in Euclidean Domain.
  ((*_e * *) => *)        ; Multiplication in Euclidean Domain.
  ((-_e *) => *)          ; Unary minus in Euclidean Domain.
  ((0_e) => *)            ; 0 element in Euclidean Domain.
  ((size *) => *)         ; Natp size of each nonzero Euclidean Domain element.
  ((q_e * *) => *)        ; Quotient in Euclidean Domain.
  ((r_e * *) => *))       ; Remainder in Euclidean Domain.

 ; Witnesses:
 (local (defun
	  edp (x)
	  (rationalp x)))

 (local (defun
	  =_e (x y)
	  (equal x y)))

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
	  size (x)
	  (declare (ignore x))
	  0))

 (local (defun
	  q_e (x y)
	  (/ x y)))

 (local (defun
	  r_e (x y)
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
	(edp (0_e))))

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
   Left-Unicity-Law
   (implies (edp x)
	    (=_e (+_e (0_e) x)
		 x)))

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
   Natp-size
   (implies (and (edp x)
		 (not (=_e x (0_e))))
	    (and (integerp (size x))
		 (>= (size x) 0)))
   :rule-classes :type-prescription)

 (defthm
   Congruence-for-Size
   (implies (and (edp y1)
		 (edp y2)
		 (=_e y1 y2))
	    (equal (size y1)
		   (size y2)))
   :rule-classes nil)

 (defthm
   Closure-of-q_e-&-r_e
   (implies (and (edp x)
		 (edp y)
		 (not (=_e y (0_e))))
	    (and (edp (q_e x y))
		 (edp (r_e x y)))))

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
   :rule-classes nil)

 (defthm
   Division-property
   (implies (and (edp x)
                 (edp y)
                 (not (=_e y (0_e))))
            (and (=_e x (+_e (*_e y (q_e x y))
			     (r_e x y)))
                 (or (=_e (r_e x y)(0_e))
                     (< (size (r_e x y))
                        (size y)))))
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
;;  terms of ==_e, ++_e, and **_e
;;  in place of +_e, +_e, and *_e.

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
  Left-Unicity-Law-for-++_e
  (implies (edp x)
	   (==_e (++_e (0_e) x)
		 x)))

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
  Natp-size-for-==_e
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (integerp (size x))
		(>= (size x) 0)))
  :rule-classes :type-prescription)

(defthm
  Congruence-for-Size-&-==_e
  (implies (==_e y1 y2)
	   (equal (size y1)
		  (size y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-for-Size)))

(defthm
  Closure-of-q_e-&-r_e-for-==_e
  (implies (and (edp x)
		(edp y)
		(not (==_e y (0_e))))
	   (and (edp (q_e x y))
		(edp (r_e x y)))))

(defthm
  Division-property-for-==_e
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
	    :in-theory (disable Commutativity-Laws-for-++_e-&-**_e)
	    :use Division-property)))

(in-theory (disable (:definition ==_e)
		    (:definition ++_e)
		    (:definition **_e)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This book constucts, for any Euclidean domain,
;;                    <edp, =_e, +_e, *_e, -_e, 0_e, size, q_e, r_e>,
;; a constant, (1_e), such that

;;          (and (edp (1_e))
;; 	         (implies (edp x)
;; 		          (=_e (*_e (1_e) x)
;; 			       x)))

;; Outline of a proof.

;; If the domain contains only one element (0_e), then let (1_e) be (0_e).

;; Otherwise the domain contains a nonzero element.
;;  Choose a nonzero domain element, b, of smallest possible size.

;;  By the Division property, b divides every domain element [because the
;;  remainder must be (0_e)].

;;  Let (1_e) be the quotient (q_e b b). Then (*_e b (1_e)) is
;;  (*_e b (q_e b b)) which is b [ since the remainder is (0_e)].

;;  For any element x of the domain, (*_e b (q_e x b)) = x. Therefore
;;  (*_e (1_e) x) = (*_e (1_e)(*_e  b (q_e x b)))
;;                = (*_e (*_e (1_e) b)(q_e x b)))
;;                = (*_e b (q_e x b))
;;                = x.

;;Choose a nonzero element of edp (if it exists).
(defchoose
  a_e (x)()
  (and (edp x)
       (not (==_e x (0_e)))))

(defthm
  a_e-property
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (edp (a_e))
		(not (==_e (a_e)(0_e)))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (not (==_e x (0_e)))
				(edp x))
			   (and (edp (a_e))
				(not (==_e (a_e)(0_e)))))))
  :hints (("Goal"
	   :by a_e)))

(defthm
  a_e-property-1
  (implies (edp x)
	   (and (implies (not (edp (a_e)))
			 (==_e x (0_e)))
		(implies (==_e (a_e)(0_e))
			 (==_e x (0_e)))))
  :rule-classes nil)

(defthm
  Natp-Size-a_e
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (integerp (Size (a_e)))
		(>= (Size (a_e)) 0)))
  :rule-classes ((:type-prescription
		  :corollary
		  (implies (and (not (==_e x (0_e)))
				(edp x))
			   (and (integerp (Size (a_e)))
				(>= (Size (a_e)) 0))))
		 (:rewrite
		  :corollary
		  (implies (and (not (==_e x (0_e)))
				(edp x))
			   (and (integerp (Size (a_e)))
				(>= (Size (a_e)) 0)))))
  :hints (("Goal"
	   :in-theory (disable a_e-property)
	   :use a_e)))

;;Choose a nonzero element of edp with Size n (if it exists).
(defchoose
  b_e (x)(n)
  (and (edp x)
       (not (==_e x (0_e)))
       (equal (Size x)(nfix n))))

(defthm
  b_e-property
  (implies (and (integerp n)
		(>= n 0)
		(equal (size x) n)
		(edp x)
		(not (==_e x (0_e))))
	   (and (edp (b_e n))
		(not (==_e (b_e n) (0_e)))
		(equal (size (b_e n)) n)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp n)
				(>= n 0)
				(equal (size x) n)
				(not (==_e x (0_e)))
				(edp x))
			   (and (edp (b_e n))
				(not (==_e (b_e n) (0_e)))
				(equal (size (b_e n)) n)))))
  :hints (("Goal"
	   :use b_e)))

(defthm
  B_e-properties-Size
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (edp (b_e (size x)))
		(not (==_e (b_e (size x))(0_e)))
		(equal (size (b_e (size x)))
		       (size x))))
  :hints (("Goal"
	   :use (:instance
		 b_e
		 (n (size x))))))

(defun
  Find-smallest-n (n)
  "Find smallest natp n such that (b_e n) is a nonzero element
   of edp and (Size (b_e n))=n (if it exists)."
  (declare (xargs :measure (let ((n (nfix n)))
			            (nfix (- (Size (a_e)) n)))))
  (if (and (edp (a_e))
	       (not (==_e (a_e)(0_e))))
      (let ((n (nfix n)))
	   (if (and (< n (size (a_e)))
		    (not (and (edp (b_e n))
			      (not (==_e (b_e n)(0_e)))
			      (equal (size (b_e n))
				     n))))
	       (Find-smallest-n (+ n 1))
	       n))
      n))

(in-theory (disable (:executable-counterpart Find-smallest-n)))

(defthm
  Integerp-Find-smallest-n
  (implies (integerp n)
	   (integerp (Find-smallest-n n)))
  :rule-classes :type-prescription)

(defthm
  Natp-Find-smallest-n
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (integerp (Find-smallest-n n))
		(>= (Find-smallest-n n) 0)))
  :rule-classes ((:type-prescription
		  :corollary
		  (implies (and (not (==_e x (0_e)))
				(edp x))
			   (and (integerp (Find-smallest-n n))
				(>= (Find-smallest-n n) 0))))))

(defthm
  Find-smallest-n-Size-a_e
  (implies (<= n (Size (a_e)))
	   (<= (Find-smallest-n n)
	       (Size (a_e)))))

(defthm
  B_e-Find-smallest-n
  (implies (and (integerp n)
		(<= 0 n)
		(<= n (Size (a_e)))
		(edp x)
		(not (==_e x (0_e))))
	   (and (edp (b_e (Find-smallest-n n)))
		(not (==_e (b_e (Find-smallest-n n))(0_e)))
		(equal (Size (b_e (Find-smallest-n n)))
		       (Find-smallest-n n))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp n)
				(<= 0 n)
				(<= n (Size (a_e)))
				(not (==_e x (0_e)))
				(edp x))
			   (and (edp (b_e (Find-smallest-n n)))
				(not (==_e (b_e (Find-smallest-n n))(0_e)))
				(equal (Size (b_e (Find-smallest-n n)))
				       (Find-smallest-n n)))))))

(defthm
  Not-Size-b_e-n-=-n
  (implies (and (integerp k)
		(integerp n)
		(<= 0 k)
		(<= k n)
		(< n (Find-smallest-n k))
		(edp x)
		(not (==_e x (0_e))))
	   (not (and (edp (b_e n))
		     (not (==_e (b_e n)(0_e)))
		     (equal (Size (b_e n)) n))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (< n (Find-smallest-n k))
				(integerp k)
				(integerp n)
				(<= 0 k)
				(<= k n)
				(not (==_e x (0_e)))
				(edp x)
				(edp (b_e n))
				(not (==_e (b_e n)(0_e))))
			   (not (equal (Size (b_e n)) n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (Find-smallest-n 0)
;;   finds the smallest natp n such that (Size (b_e n))=n (if it exists).

;; Thus if there are nonzero elements in edp, then some nonzero element,
;;  namely (b_e (Find-smallest-n 0)), has size (Find-smallest-n 0) and
;;  every nonzero element of edp has size greater than or equal to
;;  (Find-smallest-n 0).

(defthm
  Natp-Find-smallest-n-0
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (integerp (Find-smallest-n 0))
		(>= (Find-smallest-n 0) 0)))
  :rule-classes nil)

(defthm
  B_e-Find-smallest-n-0
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (edp (b_e (Find-smallest-n 0)))
		(not (==_e (b_e (Find-smallest-n 0))(0_e)))
		(equal (Size (b_e (Find-smallest-n 0)))
		       (Find-smallest-n 0))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (not (==_e x (0_e)))
				(edp x))
			   (and (edp (b_e (Find-smallest-n 0)))
				(not (==_e (b_e (Find-smallest-n 0))(0_e)))
				(equal (Size (b_e (Find-smallest-n 0)))
				       (Find-smallest-n 0)))))))

(defthm
  Not-Size-b_e-n-=-n-1
  (implies (and (integerp n)
		(<= 0 n)
		(< n (Find-smallest-n 0))
		(edp x)
		(not (==_e x (0_e))))
	   (not (and (edp (b_e n))
		     (not (==_e (b_e n)(0_e)))
		     (equal (Size (b_e n)) n))))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 Not-Size-b_e-n-=-n
		 (k 0)))))

(defthm
  Size->=-Find-smallest-n-0
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (>= (Size x)(Find-smallest-n 0)))
  :rule-classes (:rewrite
		 (:linear
		  :corollary
		  (implies (and (not (==_e x (0_e)))
				(edp x))
			   (>= (Size x)(Find-smallest-n 0)))))
  :hints (("Goal"
	   :use (:instance
		 Not-Size-b_e-n-=-n-1
		 (n (size x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; If there is a nonzero element of edp, then
;;  (b_e (Find-smallest-n 0)) divides every element of edp.

(defthm
  b_e-Find-smallest-n-0-divides-y
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (and (==_e (**_e (b_e (Find-smallest-n 0))
			    (q_e y
				 (b_e (Find-smallest-n 0))))
		      y)
		(==_e (r_e y
			   (b_e (Find-smallest-n 0)))
		      (0_e))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (not (==_e x (0_e)))
				(edp x)
				(edp y))
			   (and (==_e (**_e (b_e (Find-smallest-n 0))
					    (q_e y
						 (b_e (Find-smallest-n 0))))
				      y)
				(==_e (r_e y
					   (b_e (Find-smallest-n 0)))
				      (0_e))))))
  :hints (("Goal"
	   :use (:instance
		 Division-property-for-==_e
		 (x y)
		 (y (b_e (Find-smallest-n 0)))))))

(defun
  1_e ()
  (if (and (edp (a_e))
	   (not (==_e (a_e)(0_e))))
      (q_e (b_e (Find-smallest-n 0))
	   (b_e (Find-smallest-n 0)))
      (0_e)))

(in-theory (disable (:executable-counterpart 1_e)))

(defthm
  Closure-law-for-1-e
  (edp (1_e)))

(defthm
  Commutativity-2-Laws
  (implies (and (edp x)
		(edp y)
		(edp z))
	   (and (==_e (++_e x (++_e y z))
		      (++_e y (++_e x z)))
		(==_e (**_e x (**_e y z))
		      (**_e y (**_e x z)))))
  :hints (("Goal"
	   :use ((:functional-instance
                  acl2-asg::commutativity-2-of-op
                  (acl2-asg::equiv ==_e)
                  (acl2-asg::pred edp)
                  (acl2-asg::op ++_e))
		 (:functional-instance
                  acl2-asg::commutativity-2-of-op
                  (acl2-asg::equiv ==_e)
                  (acl2-asg::pred edp)
                  (acl2-asg::op **_e))))))

(defthm
  Nullity-Laws
  (implies (edp x)
	   (and (==_e (**_e (0_e) x)
		      (0_e))
		(==_e (**_e x (0_e))
		      (0_e)))))

(defthm
  Associativity-special-case
  (implies (and (edp (a_e))
		(not (==_e (a_e)(0_e)))
		(edp x))
	   (==_e (**_e (q_e (b_e (find-smallest-n 0))
			    (b_e (find-smallest-n 0)))
		       (**_e (b_e (find-smallest-n 0))
			     (q_e x (b_e (find-smallest-n 0)))))
		 (**_e (**_e (q_e (b_e (find-smallest-n 0))
				  (b_e (find-smallest-n 0)))
			     (b_e (find-smallest-n 0)))
		       (q_e x (b_e (find-smallest-n 0))))))
  :rule-classes nil
  :hints (("goal"
	   :in-theory (disable b_e-find-smallest-n-0-divides-y))))

(defthm
  Left-Unicity-Law-for-1_e-==_e
  (implies (edp x)
	   (==_e (**_e (1_e) x)
		 x))
  :rule-classes nil
  :hints (("Subgoal 2"
	   :use associativity-special-case)))

(in-theory (e/d ((:definition ==_e)
		 (:definition **_e))
		((:definition 1_e))))

(defthm
  Left-Unicity-Law-for-1_e
  (implies (edp x)
	   (=_e (*_e (1_e) x)
		x))
  :hints (("Goal"
	   :use Left-Unicity-Law-for-1_e-==_e)))
