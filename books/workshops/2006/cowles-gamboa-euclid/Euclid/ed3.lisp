; ACL2 Euclidean Domain books -- Book 3 -- Algebraic Theory
;  Convenient notation and events for using the theory of an
;  Euclidean Domain.
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

; Last modified Feb. 2006.

#|
To certify this book, first, create a world with the following packages:

(DEFPKG "ACL2-ASG"
  (SET-DIFFERENCE-EQUAL
   (UNION-EQ *ACL2-EXPORTS*
	     *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*)
   '(ZERO)))

(DEFPKG "ACL2-AGP"
  (SET-DIFFERENCE-EQUAL
   (UNION-EQ *ACL2-EXPORTS*
	     *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*)
   '(ZERO)))

(DEFPKG "ACL2-CRG"
  (SET-DIFFERENCE-EQUAL
   (UNION-EQ *ACL2-EXPORTS*
	     *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*)
   '(ZERO)))

(certify-book "ed3"
	      3
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
;; (2) multiplication distributes over addition,
;; (3) zero is an identity for addition, and
;; (4) minus produces an additive inverse

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This book assumes the result reported in ed1.lisp which is Book 1 of
;; ACL2 Euclidean Domain books

;;                  Multiplicative Identity Existence

;; That is, every Euclidean Domain has a multiplicative identity.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This book also assumes the result reported in ed2.lisp which is Book 2
;; of the ACL2 Euclidean Domain books.

;; There is no loss of generality in assuming the
;;   Multiplicative Size Property:

;;     For all nonzero domain elements x and y, Size(x) <= Size(xy).

;;     If the original Size function does not satisfy this property,
;;     then it can replaced by another that does satisfy this and the
;;     division property.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Brief Contents of This Book

;;  Axioms and convenient notation for
;;   the theory of an Euclidean Domain.

;;  Integral Domain Theory.

;;  Divides-p Theory.

;; ;; (defun-sk
;; ;;   Divides-p (x y)
;; ;;   (exists z (and (edp x)
;; ;;                  (edp z)
;; ;;                  (=_e (*_e x z)
;; ;;                       y))))

;; Associates-p Theory.

;; ;; (defun
;; ;;   Associates-p (x y)
;; ;;   (if (and (edp x)
;; ;;            (edp y))
;; ;;       (and (divides-p x y)
;; ;;            (divides-p y x))
;; ;;       (equal x y)))

;; Unit-p Theory.

;; ;; (defun
;; ;;   Unit-p (x)
;; ;;   (divides-p x (1_e)))

;; Reducible-p and
;;  Irreducible-p Theory.

;; ;; (defun-sk
;; ;;   Reducible-p (x)
;; ;;   (exists (y z)(and (edp y)
;; ;;                     (edp z)
;; ;;                     (not (unit-p y))
;; ;;                     (not (unit-p z))
;; ;;                     (=_e (*_e y z) x))))

;; ;; (defun
;; ;;   Irreducible-p (x)
;; ;;   (and (edp x)
;; ;;        (not (unit-p x))
;; ;;        (not (reducible-p x))))

;; Factorization Existence Theory.

;; ;; (defthm
;; ;;   IRREDUCIBLE-FACTORIZATION-EXISTENCE
;; ;;   (and (true-listp (irreducible-factors x))
;; ;;        (edp-listp  (irreducible-factors x))
;; ;;        (irreducible-listp (irreducible-factors x))
;; ;;        (implies (and (edp x)
;; ;;                      (not (=_e x (0_e)))
;; ;;                      (not (unit-p x)))
;; ;;                 (=_e (*_e-lst (irreducible-factors x)) x)))
;; ;;   :rule-classes nil)

;; GCD Theory.

;; ;; Determine if g is a gcd of x and y.
;; ;; (defun-sk
;; ;;   gcd-p (x y g)
;; ;;   (forall d (and (divides-p g x)
;; ;;                  (divides-p g y)
;; ;;                  (implies (and (divides-p d x)
;; ;;                                (divides-p d y))
;; ;;                           (divides-p d g)))))

;; Unit-associates-p Theory.

;; ;; (defun-sk
;; ;;   unit-associates-p (x y)
;; ;;   (exists u (if (and (edp x)
;; ;;                      (edp y))
;; ;;                 (and (unit-p u)
;; ;;                      (=_e (*_e u x)
;; ;;                           y))
;; ;;                 (equal x y))))
;; ;; Unit-associates-p is equivalent to Associates-p.

;; Unique Factorization Theory.

;; ;; (defthm
;; ;;   IRREDUCIBLE-FACTORIZATION-UNIQUENESS-general
;; ;;   (implies (and (irreducible-listp lst1)
;; ;;                 (irreducible-listp lst2)
;; ;;                 (unit-associates-p (*_e-lst lst1)
;; ;;                                    (*_e-lst lst2)))
;; ;;           (bag-equal-unit-associates lst1 lst2))
;; ;;   :hints (("Goal"
;; ;;            ...)))

;; ;; (defthm
;; ;;   IRREDUCIBLE-FACTORIZATION-UNIQUENESS
;; ;;   (implies (and (irreducible-listp lst1)
;; ;;                 (irreducible-listp lst2)
;; ;;                 (=_e (*_e-lst lst1)
;; ;;                      (*_e-lst lst2)))
;; ;;           (bag-equal-unit-associates lst1 lst2))
;; ;;   :hints (("Goal"
;; ;;            ...)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Axioms and convenient notation for
;;  the theory of an Euclidean Domain.

(encapsulate
 ; Signatures
 (((edp *) => *)          ; x is in Euclidean Domain iff (NOT (EQUAL (edp x) NIL)).
  ((=_e * *) => *)        ; Equality predicate for Euclidean Domain elements.
  ((C_=_e *) => *)        ; Choose unique equivalence class representative for =_e.
  ((binary-+_e * *) => *) ; Addition in Euclidean Domain.
  ((binary-*_e * *) => *) ; Multiplication in Euclidean Domain.
  ((-_e *) => *)          ; Unary minus in Euclidean Domain.
  ((0_e) => *)            ; 0 element in Euclidean Domain.
  ((1_e) => *)            ; 1 element in Euclidean Domain.
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
	  C_=_e (x)
	  (identity x)))

 (local (defun
	  binary-+_e (x y)
	  (+ x y)))

 (local (defun
	  binary-*_e (x y)
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

 ; Convenient Notation:
 (defmacro
   +_e (&rest rst)
   (if rst
       (if (cdr rst)
	   (xxxjoin 'binary-+_e rst)
	   (list 'binary-+_e '(0_e)(car rst)))
       '(0_e)))

 (defmacro
   *_e (&rest rst)
   (if rst
       (if (cdr rst)
	   (xxxjoin 'binary-*_e rst)
	   (list 'binary-*_e '(1_e)(car rst)))
       '(1_e)))

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
   (implies (=_e y1 y2)
	    (and (iff (edp y1)
		      (edp y2))
		 (implies (and (edp y1)
			       (edp y2))
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
				    (-_e y2))))))
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
   Natp-size
   (implies (and (edp x)
		 (not (=_e x (0_e))))
	    (and (integerp (size x))
		 (>= (size x) 0)))
   :rule-classes (:type-prescription
		  :rewrite))

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

 (defthm
   Size-*_e
   (implies (and (edp x)
		 (not (=_e x (0_e)))
		 (edp y)
		 (not (=_e y (0_e))))
	    (<= (size x)
		(size (*_e x y))))
   :rule-classes (:linear :rewrite))
 ) ; end encapsulate

(add-invisible-fns binary-+_e -_e)
(add-invisible-fns -_e -_e)

(add-binop +_e binary-+_e)
(add-binop *_e binary-*_e)

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
  binary-++_e (x y)
  "binary-++_e nicely extends +_e
   to entire ACL2 universe."
  (if (and (edp x)
	   (edp y))
      (+_e x y)
      x))

(defun
  binary-**_e (x y)
  "binary-**_e nicely extends *_e
   to entire ACL2 universe."
  (if (and (edp x)
	   (edp y))
      (*_e x y)
      x))

; Convenient Notation:
(defmacro
  ++_e (&rest rst)
  (if rst
      (if (cdr rst)
	  (xxxjoin 'binary-++_e rst)
	  (list 'binary-++_e '(0_e)(car rst)))
      '(0_e)))

(defmacro
  **_e (&rest rst)
  (if rst
      (if (cdr rst)
	  (xxxjoin 'binary-**_e rst)
	  (list 'binary-**_e '(1_e)(car rst)))
      '(1_e)))

(add-invisible-fns binary-++_e -_e)

(add-binop ++_e binary-++_e)
(add-binop **_e binary-**_e)

;; Restate Integral Domain Axioms in
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

(defthm
  ==_e-implies-==_e_-_e
  (implies (==_e y1 y2)
	   (==_e (-_e y1)
		 (-_e y2)))
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

;; Restate Euclidean Domain Axioms in
;;  terms of ==_e, ++_e, **_e, qq_e, and rr_e
;;  in place of =_e, +_e, +_e, and *_e, q_e, and r_e.

(defthm
  Natp-size-==_e
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (and (integerp (size x))
		(>= (size x) 0)))
  :rule-classes (:type-prescription
		 :rewrite))

(defthm
  ==_e-implies-equal-size
  (implies (==_e y1 y2)
	   (equal (size y1)
		  (size y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-for-Size)))

(defun
  qq_e (x y)
  "qq_e nicely extends q_e
   to entire ACL2 universe."
  (if (and (edp x)
	   (edp y)
	   (not (==_e y (0_e))))
      (q_e x y)
      x))

(defun
  rr_e (x y)
  "rr_e nicely extends r_e
   to entire ACL2 universe."
  (if (and (edp x)
	   (edp y)
	   (not (==_e y (0_e))))
      (r_e x y)
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
	   :use Congruence-for-q_e-&-r_e)))

(defthm
  ==_e-implies-==_e-qq_e-2
  (implies (==_e y1 y2)
	   (==_e (qq_e x y1)
		 (qq_e x y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-for-q_e-&-r_e)))

(defthm
  ==_e-implies-==_e-rr_e-1
  (implies (==_e y1 y2)
	   (==_e (rr_e y1 z)
		 (rr_e y2 z)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-for-q_e-&-r_e)))

(defthm
  ==_e-implies-==_e-rr_e-2
  (implies (==_e y1 y2)
	   (==_e (rr_e x y1)
		 (rr_e x y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-for-q_e-&-r_e)))

(defthm
  Division-property-for-qq_e-&-rr_e
  (implies (and (edp x)
		(edp y)
		(not (==_e y (0_e))))
	   (and (==_e x (++_e (**_e y (qq_e x y))
			      (rr_e x y)))
		(or (==_e (rr_e x y)(0_e))
		    (< (size (rr_e x y))
		       (size y)))))
  :rule-classes ((:elim
		  :corollary
		  (implies (and (edp x)
				(edp y)
				(not (==_e y (0_e))))
			   (==_e (++_e (rr_e x y)
				       (**_e y (qq_e x y)))
				 x)))
		 (:rewrite
		  :corollary
		  (implies (and (edp x)
				(edp y)
				(not (==_e y (0_e))))
			   (and (==_e (++_e (rr_e x y)
					    (**_e y (qq_e x y)))
				      x)
				(implies (not (==_e (rr_e x y) (0_e)))
					 (< (size (rr_e x y))
					    (size y))))))
		 (:linear
		  :corollary
		  (implies (and (edp x)
				(edp y)
				(not (==_e y (0_e)))
				(not (==_e (rr_e x y)(0_e))))
			   (< (size (rr_e x y))
			      (size y)))))
   :hints (("Goal"
	    :in-theory (disable commutativity-laws-for-++_e-&-**_e)
	    :use Division-property)))

(defthm
  Size-**_e
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y)
		(not (==_e y (0_e))))
	   (<= (size x)
	       (size (**_e x y))))
  :rule-classes (:linear :rewrite))

(in-theory (disable (:definition ==_e)
		    (:definition C_==_e)
		    (:definition binary-++_e)
		    (:definition binary-**_e)
		    (:definition qq_e)
		    (:definition rr_e)))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Integral Domain Theory:

(defthm
  Right-Unicity-Laws
  (implies (edp x)
	   (and (==_e (++_e x (0_e))
		      x)
		(==_e (**_e x (1_e))
		      x))))

(defthm
  Right-Distributivity-Law
  (implies (and (edp x)
		(edp y)
		(edp z))
	   (==_e (**_e (++_e x y) z)
		 (++_e (**_e x z)
		       (**_e y z)))))

(defthm
  Commutativity-2-Laws
  (implies (and (edp x)
		(edp y)
		(edp z))
	   (and (==_e (++_e x y z)
		      (++_e y x z))
		(==_e (**_e x y z)
		      (**_e y x z))))
  :hints (("Goal"
	   :use ((:functional-instance
                  acl2-asg::commutativity-2-of-op
                  (acl2-asg::equiv ==_e)
                  (acl2-asg::pred edp)
                  (acl2-asg::op binary-++_e))
		 (:functional-instance
                  acl2-asg::commutativity-2-of-op
                  (acl2-asg::equiv ==_e)
                  (acl2-asg::pred edp)
                  (acl2-asg::op binary-**_e))))))

(defthm
  Nullity-Laws
  (implies (edp x)
	   (and (==_e (**_e (0_e) x)
		      (0_e))
		(==_e (**_e x (0_e))
		      (0_e)))))

(defthm
  Involution-Law
  (implies (edp x)
	   (==_e (-_e (-_e x))
		 x))
  :hints (("Goal"
	   :use (:functional-instance
                 acl2-agp::Involution-of-inv
                 (acl2-agp::equiv ==_e)
                 (acl2-agp::pred edp)
                 (acl2-agp::op binary-++_e)
                 (acl2-agp::id 0_e)
                 (acl2-agp::inv -_e)))))

(defthm
  Inverse-Distributive-Law
  (implies (and (edp x)
		(edp y))
	   (==_e (-_e (++_e x y))
		 (++_e (-_e x)(-_e y))))
  :hints (("Goal"
	   :use (:functional-instance
                 acl2-agp::Distributivity-of-inv-over-op
                 (acl2-agp::equiv ==_e)
                 (acl2-agp::pred edp)
                 (acl2-agp::op binary-++_e)
                 (acl2-agp::id 0_e)
                 (acl2-agp::inv -_e)))))

(defthm
  Inverse-Cancellation-Laws
  (implies (and (edp x)
		(edp y))
	   (and (==_e (++_e x y (-_e x))
		      y)
		(==_e (++_e x (-_e x) y)
		      y)))
  :hints (("Goal"
	   :use (:functional-instance
                 acl2-agp::inv-cancellation-on-right
                 (acl2-agp::equiv ==_e)
                 (acl2-agp::pred edp)
                 (acl2-agp::op binary-++_e)
                 (acl2-agp::id 0_e)
                 (acl2-agp::inv -_e)))))

(defthm
  Cancellation-Laws-for-++_e
  (implies (and (edp x)
		(edp y)
		(edp z))
	   (and (equal (==_e (++_e x z)(++_e y z))
		       (==_e x y))
		(equal (==_e (++_e z x)(++_e z y))
		       (==_e x y))
		(equal (==_e (++_e z x)(++_e y z))
		       (==_e x y))
		(equal (==_e (++_e x z)(++_e z y))
		       (==_e x y))))
  :hints (("Goal"
	   :use (:functional-instance
                 acl2-agp::Right-cancellation-for-op
                 (acl2-agp::equiv ==_e)
                 (acl2-agp::pred edp)
                 (acl2-agp::op binary-++_e)
                 (acl2-agp::id 0_e)
                 (acl2-agp::inv -_e)))))

(defthm
  Functional-Commutativity-Laws-1
  (implies (and (edp x)
		(edp y))
	   (and (==_e (**_e x (-_e y))
		      (-_e (**_e x y)))
		(==_e (**_e (-_e y) x)
		      (-_e (**_e y x)))))
  :hints (("Goal"
	   :use (:functional-instance
                 acl2-crg::functional-commutativity-of-minus-times-right
                 (acl2-crg::equiv ==_e)
                 (acl2-crg::pred edp)
                 (acl2-crg::plus binary-++_e)
                 (acl2-crg::times binary-**_e)
                 (acl2-crg::zero 0_e)
                 (acl2-crg::minus -_e)))))

(defthm
  -_e-0
  (==_e (-_e (0_e))
	(0_e))
  :hints (("Goal"
	   :use (:instance
		 Cancellation-Laws-for-++_e
		 (x (-_e (0_e)))
		 (y (0_e))
		 (z (0_e))))))

(defthm
  Equal_-_e-zero
  (implies (edp x)
	   (equal (==_e (0_e)(-_e x))
		  (==_e (0_e) x)))
  :hints (("Goal"
	   :use (:instance
		 ==_e-implies-==_e_-_e
		 (y1 (0_e))
		 (y2 (-_e x))))))

(defthm
  ==_e-Inverses-Law
  (implies (and (edp x)
		(edp y))
	   (equal (==_e (-_e x)(-_e y))
		  (==_e x y)))
  :hints (("Goal"
	   :use (:instance
		 ==_e-implies-==_e_-_e
		 (y1 (-_e x))
		 (y2 (-_e y))))))

(defthm
  Idempotent-Law
  (implies (edp x)
	   (equal (==_e (++_e x x) x)
		  (==_e x (0_e))))
  :hints (("Goal"
	   :use (:functional-instance
                 acl2-agp::Uniqueness-of-id-as-op-idempotent
                 (acl2-agp::equiv ==_e)
                 (acl2-agp::pred edp)
                 (acl2-agp::op binary-++_e)
                 (acl2-agp::id 0_e)
                 (acl2-agp::inv -_e)))))

(defthm
  ==_e_-_e-0_e
  (implies (and (edp x)
		(edp y))
	   (equal (==_e (++_e x (-_e y))(0_e))
		  (==_e x y)))
  :hints (("Goal"
	   :use (:instance
		 Cancellation-Laws-for-++_e
		 (x (++_e x (-_e y)))
		 (y (0_e))
		 (z y)))))

(defthm
  Cancellation-Laws-for-**_e
  (implies (and (edp x)
		(edp y)
		(edp z))
	   (and (equal (==_e (**_e x z)(**_e y z))
		       (or (==_e z (0_e))
			   (==_e x y)))
		(equal (==_e (**_e x z)(**_e z y))
		       (or (==_e z (0_e))
			   (==_e x y)))
		(equal (==_e (**_e z x)(**_e y z))
		       (or (==_e z (0_e))
			   (==_e x y)))
		(equal (==_e (**_e z x)(**_e z y))
		       (or (==_e z (0_e))
			   (==_e x y)))))
  :hints (("Goal"
	   :use ((:instance
		  Zero-Divisor-Law-for-**_e
		  (x (++_e x (-_e y)))
		  (y z))))))

(defthm
  Projection-Laws
  (implies (and (edp x)
		(edp y))
	   (and (equal (==_e (**_e x y) x)
		       (or (==_e x (0_e))
			   (==_e y (1_e))))
		(equal (==_e (**_e y x) x)
		       (or (==_e x (0_e))
			   (==_e y (1_e))))
		(equal (==_e (++_e x y) x)
		       (==_e y (0_e)))
		(equal (==_e (++_e y x) x)
		       (==_e y (0_e)))))
  :hints (("Goal"
	   :use ((:instance
		  Cancellation-Laws-for-**_e
		  (z x)(x y)(y (1_e)))
		 (:instance
		  Cancellation-Laws-for-++_e
		  (z x)(x y)(y (0_e)))))))

(defthm
  Commutativity-of-==_e
  (equal (==_e x y)
	 (==_e y x))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:theorem
		  (implies (==_e x y)
			   (==_e y x)))))))

(defthm
  Projection-Laws-1
  (implies (and (edp x)
		(edp y))
	   (and (equal (==_e x (**_e x y))
		       (or (==_e x (0_e))
			   (==_e y (1_e))))
		(equal (==_e x (**_e y x))
		       (or (==_e x (0_e))
			   (==_e y (1_e))))
		(equal (==_e x (++_e x y))
		       (==_e y (0_e)))
		(equal (==_e x (++_e y x))
		       (==_e y (0_e)))))
  :hints (("Goal"
	   :use ((:instance
		  Commutativity-of-==_e
		  (y (**_e x y)))
		 (:instance
		  Commutativity-of-==_e
		  (y (++_e x y)))))))

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
	   :use Left-Unicity-Laws-for-++_e-&-**_e)))

;;;;;;;;;;;;;;;;;;;;
;; Divides-p theory:

(defun-sk
  Divides-p (x y)
  (exists z (and (edp x)
		 (edp z)
		 (=_e (*_e x z)
		      y))))

(defun-sk
  Divides-p1 (x y)
  (exists z (and (edp x)
		 (edp z)
		 (==_e (**_e x z)
		       y))))

(defthm
  Divides-p-implies-divides-p1
  (implies (divides-p x y)
	   (divides-p1 x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable (:definition ==_e)
			      (:definition binary-**_e))
	    :use (:instance
		  congruence-laws
		  (y1 (*_e x (divides-p-witness x y)))
		  (y2 y)))))

(defthm
  Divides-p1-implies-divides-p
  (implies (divides-p1 x y)
	   (divides-p x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable (:definition ==_e)
			      (:definition binary-**_e)))))

(defthm
  Divides-p-iff-divides-p1
  (iff (divides-p x y)
       (divides-p1 x y))
  :rule-classes nil
  :hints (("Goal"
	   :use (Divides-p-implies-divides-p1
		 Divides-p1-implies-divides-p))))

(defthm
  Booleanp-divides-p
  (Booleanp (divides-p x y))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :use (:instance
		 congruence-laws
		 (y1 (*_e x (divides-p-witness x y)))
		 (y2 y)))))

(defthm
  Divides-p-=-divides-p1
  (equal (divides-p x y)
	 (divides-p1 x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition divides-p)
			       (:definition divides-p1))
	   :use Divides-p-iff-divides-p1)))

(defun
  Divides-pp-witness (x y)
  "Divides-pp-witness nicely
   modifies divides-p1-witness."
  (divides-p1-witness (C_==_e x)(C_==_e y)))

(defthm
  ==_e-implies-==_e-divides-pp-witness-1
  (implies (==_e y1 y2)
	   (==_e (divides-pp-witness y1 z)
		 (divides-pp-witness y2 z)))
  :rule-classes :congruence)

(defthm
  ==_e-implies-==_e-divides-pp-witness-2
  (implies (==_e y1 y2)
	   (==_e (divides-pp-witness x y1)
		 (divides-pp-witness x y2)))
  :rule-classes :congruence)

(defun
  Divides-pp (x y)
  (let ((z (divides-pp-witness x y)))
       (and (edp x)
	    (edp z)
	    (==_e (**_e x z) y))))

(defthm
  ==_e-implies-equal-divides-pp-1
  (implies (==_e y1 y2)
	   (equal (divides-pp y1 z)
		  (divides-pp y2 z)))
  :rule-classes :congruence)

(defthm
  ==_e-implies-equal-divides-pp-2
  (implies (==_e y1 y2)
	   (equal (divides-pp x y1)
		  (divides-pp x y2)))
  :rule-classes :congruence)

(defthm
  Divides-pp-suff
  (implies (and (edp x)
		(edp z)
		(==_e (**_e x z) y))
	   (divides-pp x y))
  :hints (("Goal"
	   :in-theory (disable divides-p1-suff)
	   :use (:instance
		 divides-p1-suff
		 (x (C_==_e x))
		 (y (C_==_e y))))))

(in-theory (disable (:definition Divides-pp-witness)
		    (:executable-counterpart divides-pp)))

(defthm
  Divides-p1-=-Divides-pp
  (equal (divides-p1 x y)
	 (divides-pp x y))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:theorem
		  (implies (divides-p1 x y)
			   (divides-pp x y)))
		 (:theorem
		  (implies (divides-pp x y)
			   (divides-p1 x y)))))))

(defthm
  Divides-p-=-Divides-pp
  (equal (divides-p x y)
	 (divides-pp x y))
  :rule-classes nil
  :hints (("Goal"
	   :use (Divides-p-=-Divides-p1
		 Divides-p1-=-Divides-pp))))

(defthm
  Divides-pp-edp-1
  (implies (divides-pp x y)
	   (edp x))
  :rule-classes :forward-chaining)

(defthm
  Divides-pp-edp-2
  (implies (divides-pp x y)
	   (edp y))
  :rule-classes :forward-chaining
  :hints (("goal"
	   :use (:instance
		 Closure-Laws-for-++_e-&-**_e
		 (y (divides-pp-witness x y))))))

(defthm
  Divides-pp-edp-divides-pp-witness
  (implies (divides-pp x y)
	   (edp (divides-pp-witness x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (O_e) is greatest element with
;;  respect to divides-pp relation.
(defthm
  Greatest-divides-pp=0_e
  (implies (edp x)
	   (divides-pp x (0_e))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (1_e) is least element with
;;  respect to divides-pp relation.
(defthm
  Least-divides-pp=1_e
  (implies (edp x)
	   (divides-pp (1_e) x)))

(defthm
  Transitivity-divides-pp-lemma
  (implies (and (edp x)
		(edp (divides-pp-witness x y))
		(edp (divides-pp-witness y z))
		(==_e (**_e x (divides-pp-witness x y)) y)
		(==_e (**_e y (divides-pp-witness y z)) z))
	   (==_e (**_e x
		       (divides-pp-witness x y)
		       (divides-pp-witness y z))
		 z))
  :hints (("goal"
	   :use (:instance
		 Associativity-laws-for-++_e-&-**_e
		 (y (divides-pp-witness x y))
		 (z (divides-pp-witness y z))))))

(defthm
  Transitivity-divides-pp
  (implies (and (divides-pp x y)
		(divides-pp y z))
	   (divides-pp x z))
  :rule-classes (:rewrite
		 :forward-chaining)
  :hints (("Goal"
	   :use (:instance
		 Divides-pp-suff
		 (y z)
		 (z (**_e (divides-pp-witness x y)
			  (divides-pp-witness y z)))))))

(defthm
  Divides-pp-++_e
  (implies (and (divides-pp x y)
		(divides-pp x z))
	   (divides-pp x (++_e y z)))
  :hints (("Goal"
	   :use (:instance
		 divides-pp-suff
		 (y (++_e y z))
		 (z (++_e (divides-pp-witness x y)
			  (divides-pp-witness x z)))))))

(defthm
  Divides-pp--_e
  (implies (and (divides-pp x y)
		(divides-pp x z))
	   (divides-pp x (++_e y (-_e z))))
  :hints (("Goal"
	   :use (:instance
		 divides-p1-suff
		 (y (++_e y (-_e z)))
		 (z (++_e (divides-pp-witness x y)
			  (-_e (divides-pp-witness x z))))))))

(defthm
  Divides-pp-**_e
  (implies (and (edp v)
		(divides-pp x y))
	   (and (divides-pp x (**_e y v))
		(divides-pp x (**_e v y))))
  :hints (("Goal"
	   :in-theory (disable divides-pp-edp-2)
	   :use ((:instance
		  divides-pp-suff
		  (y (**_e v y))
		  (z (**_e v (divides-pp-witness x y))))
		 divides-pp-edp-2))))

(defthm
  Divides-pp-witness-0_e
  (implies (and (edp x)
		(not (==_e x (0_e))))
	   (==_e (divides-pp-witness x (0_e))
		 (0_e)))
  :hints (("Goal"
	   :in-theory (disable divides-pp-suff
			       Greatest-divides-pp=0_e)
	   :use (:instance
		 divides-pp-suff
		 (y (0_e))
		 (z (0_e))))))

(defthm
  Rr_e=0-implies-divides-pp
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y)
		(==_e (rr_e y x)(0_e)))
	   (divides-pp x y))
  :hints (("Goal"
	   :in-theory (disable closure-of-qq_e-&-rr_e)
	   :use ((:instance
		  divides-pp-suff
		  (z (qq_e y x)))
		 (:instance
		  closure-of-qq_e-&-rr_e
		  (x y)
		  (y x))))))

(defthm
  Divides-pp-implies-rr_e=0-lemma
  (implies (and (divides-pp x y)
		(not (==_e x (0_e))))
	   (==_e (**_e x (++_e (divides-pp-witness x y)
			       (-_e (qq_e y x))))
		 (rr_e y x)))
  :hints (("Goal"
	   :in-theory (disable closure-of-qq_e-&-rr_e
			       divides-pp-edp-2)
	   :use ((:instance
		  closure-of-qq_e-&-rr_e
		  (x y)
		  (y x))
		 divides-pp-edp-2))))

(defthm
  Divides-pp-implies-rr_e=0-lemma-1
  (implies (and (==_e (divides-pp-witness x y)(qq_e y x))
		(edp x)
		(edp y)
		(==_e (**_e x (divides-pp-witness x y)) y)
		(not (==_e x (0_e))))
	   (==_e (rr_e y x)(0_e)))
  :hints (("goal"
	   :in-theory (disable closure-of-qq_e-&-rr_e)
	   :use (:instance
		 closure-of-qq_e-&-rr_e
		 (x y)
		 (y x)))))

(defthm
  Divides-p-implies-rr_e=0
  (implies (and (divides-pp x y)
		(not (==_e x (0_e))))
	   (==_e (rr_e y x)(0_e)))
  :hints (("Goal"
	   :in-theory (disable divides-pp-edp-2)
	   :use (divides-pp-edp-2
		 (:instance
		  Size-**_e
		  (y (++_e (divides-pp-witness x y)
			   (-_e (qq_e y x)))))))))

(defthm
  Divides-pp-implies-witness=qq_e
  (implies (and (divides-pp x y)
		(not (==_e x (0_e))))
	   (==_e (divides-pp-witness x y)
		 (qq_e y x)))
  :hints (("Goal"
	   :in-theory (disable divides-pp-edp-2
			       divides-pp-edp-divides-pp-witness)
	   :use (divides-pp-edp-2
		 (:instance
		  Cancellation-Laws-for-**_e
		  (z x)
		  (x (divides-pp-witness x y))
		  (y (qq_e y x)))
		 (:instance
		  Division-property-for-qq_e-&-rr_e
		  (x y)
		  (y x))))))

;;;;;;;;;;;;;;;;;;;;;;;
;; Associates-p theory:

(defun
  Associates-p (x y)
  (if (and (edp x)
	   (edp y))
      (and (divides-p x y)
	   (divides-p y x))
      (equal x y)))

(defun
  Associates-pp (x y)
  (if (and (edp x)
	   (edp y))
      (and (divides-pp x y)
	   (divides-pp y x))
      (equal x y)))

(defthm
  Associates-p-=-Associates-pp
  (equal (associates-p x y)
	 (associates-pp x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition divides-p)
			       (:definition divides-pp))
	   :use (Divides-p-=-Divides-pp
		 (:instance
		  Divides-p-=-Divides-pp
		  (x y)
		  (y x))))))

(defthm
  Associates-pp-is-an-equivalence
  (and (booleanp (associates-pp x y))
       (associates-pp x x)
       (implies (associates-pp x y)
		(associates-pp y x))
       (implies (and (associates-pp x y)
		     (associates-pp y z))
		(associates-pp x z)))
  :rule-classes :equivalence
  :hints (("Goal"
	   :in-theory (disable divides-pp))))

(defthm
  ==_e-implies-equal-associates-pp-1
  (implies (==_e y1 y2)
	   (equal (associates-pp y1 z)
		  (associates-pp y2 z)))
  :rule-classes :congruence
  :hints (("Goal"
	   :in-theory (disable (:definition divides-pp)))
	  ("Subgoal 2"
	   :in-theory (enable (:definition ==_e)))
	  ("Subgoal 1"
	   :in-theory (enable (:definition ==_e)))))

(defthm
  ==_e-implies-equal-associates-pp-2
  (implies (==_e y1 y2)
	   (equal (associates-pp x y1)
		  (associates-pp x y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :in-theory (disable (:definition divides-pp)))
	  ("Subgoal 2"
	   :in-theory (enable (:definition ==_e)))
	  ("Subgoal 1"
	   :in-theory (enable (:definition ==_e)))))

(defthm
  ==_e-refines-associates-pp
  (implies (==_e x y)
	   (associates-pp x y))
  :rule-classes :refinement)

(defthm
  Associates-pp-implies-equal-divides-pp-1
  (implies (associates-pp x1 x2)
	   (equal (divides-pp x1 y)
		  (divides-pp x2 y)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use ((:instance
		  Transitivity-divides-pp
		  (x x2)
		  (y x1)
		  (z y))
		 (:instance
		  Transitivity-divides-pp
		  (x x1)
		  (y x2)
		  (z y))))))

(defthm
  Associates-pp-implies-equal-divides-pp-2
  (implies (associates-pp y1 y2)
	   (equal (divides-pp x y1)
		  (divides-pp x y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :in-theory (disable
		       associates-pp-implies-equal-divides-pp-1)
	   :use ((:instance
		  Transitivity-divides-pp
		  (y y1)
		  (z y2))
		 (:instance
		  Transitivity-divides-pp
		  (y y2)
		  (z y1))))))

(defthm
  Divides-pp-<=-Size
  (implies (and (divides-pp x y)
		(not (==_e y (0_e))))
	   (<= (size x)
	       (size y)))
  :hints (("Goal"
	   :in-theory (disable divides-pp-implies-witness=qq_e)
	   :use (:instance
		 Size-**_e
		 (y (divides-pp-witness x y))))))

(defthm
  Associates-pp-implies-equal-Size-lemma-1
  (implies (and (associates-pp x y)
		(not (==_e y (0_e))))
	   (equal (Size x)
		  (Size y)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition divides-pp))
	   :use (Divides-pp-<=-Size
		 (:instance
		  Divides-pp-<=-Size
		  (x y)
		  (y x))
		 (:theorem
		  (implies (and (associates-pp x y)
				(not (==_e y (0_e))))
			   (not (==_e x (0_e)))))))
	  ("Subgoal 1"
	   :in-theory (enable (:definition divides-pp)))))

(defthm
  Associates-pp-implies-equal-Size-lemma-2
  (implies (and (associates-pp x y)
		(not (==_e x (0_e))))
	   (equal (Size x)
		  (Size y)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition divides-pp))
	   :use (Divides-pp-<=-Size
		 (:instance
		  Divides-pp-<=-Size
		  (x y)
		  (y x))
		 (:theorem
		  (implies (and (associates-pp x y)
				(not (==_e x (0_e))))
			   (not (==_e y (0_e)))))))
	  ("Subgoal 1"
	   :in-theory (enable (:definition divides-pp)))))

(defthm
  Associates-pp-implies-equal-Size
  (implies (associates-pp x1 x2)
	   (equal (size x1)
		  (size x2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :cases ((not (==_e x2 (0_e)))
		   (not (==_e x1 (0_e)))))
	  ("Subgoal 2"
	   :by (:instance
		Associates-pp-implies-equal-Size-lemma-1
		(x x1)
		(y x2)))
	  ("Subgoal 1"
	   :by (:instance
		Associates-pp-implies-equal-Size-lemma-2
		(x x1)
		(y x2)))))

;;;;;;;;;;;;;;;;;
;; Unit-p theory:

(defun
  Unit-p (x)
  (divides-p x (1_e)))

(defun
  Unit-p1 (x)
  (divides-p1 x (1_e)))

(defun
  Unit-pp (x)
  (divides-pp x (1_e)))

(defthm
  Unit-p-=-unit-p1
  (equal (unit-p x)
	 (unit-p1 x))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 Divides-p-=-Divides-p1
		 (y (1_e))))))

(defthm
  Unit-p1-=-unit-pp
  (equal (unit-p1 x)
	 (unit-pp x))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 Divides-p1-=-Divides-pp
		 (y (1_e))))))

(defthm
  Unit-p-=-Unit-pp
  (equal (unit-p x)
	 (unit-pp x))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 Divides-p-=-Divides-pp
		 (y (1_e))))))

(defthm
  ==_e-implies-equal-unit-pp
  (implies (==_e x1 x2)
	   (equal (unit-pp x1)
		  (unit-pp x2)))
  :rule-classes :congruence)

(defthm
  Associates-pp-implies-equal-unit-pp
  (implies (associates-pp x1 x2)
	   (equal (unit-pp x1)
		  (unit-pp x2)))
  :rule-classes :congruence)

(defthm
  Unit-pp-1_e
  (unit-pp (1_e)))

(defthm
  Unit-pp-_-_e-1_e
  (unit-pp (-_e (1_e)))
  :hints (("Goal"
	   :use (:instance
		 Divides-pp-suff
		 (x (-_e (1_e)))
		 (y (1_e))
		 (z (-_e (1_e)))))))

(defthm
  Size-unit-pp=Size-1_e
  (implies (unit-pp x)
	   (equal (size x)
		  (size (1_e))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition associates-pp))
	   :use (:theorem
		 (implies (unit-pp x)
			  (associates-pp x (1_e)))))
	  ("Subgoal 1"
	   :in-theory (enable (:definition associates-pp)))))

(defthm
  Size-unit-p=Size-1_e
  (implies (unit-p x)
	   (equal (size x)
		  (size (1_e))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p)
			       (:definition unit-pp))
	   :use (unit-p-=-unit-pp
		 Size-unit-pp=Size-1_e))))

(defthm
  Size->=-Size-1_e
  (implies (and (not (==_e x (0_e)))
		(edp x))
	   (>= (size x)(size (1_e))))
  :rule-classes (:linear
		 :rewrite))

(defthm
  Rr_e-1_e-x=0_e
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(equal (size x)
		       (size (1_e))))
	   (==_e (rr_e (1_e) x)(0_e))))

(defthm
  Size=Size-1_e-implies-unit-pp
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(equal (size x)
		       (size (1_e))))
	   (unit-pp x)))

(defthm
  Size=Size-1_e-implies-unit-p
  (implies (and (edp x)
		(not (=_e x (0_e)))
		(equal (size x)
		       (size (1_e))))
	   (unit-p x))
  :hints (("Goal"
	   :in-theory (e/d ((:definition ==_e))
			   ((:definition unit-p)
			    (:definition unit-pp)
			    Size=Size-1_e-implies-unit-pp))
	   :use (unit-p-=-unit-pp
		 Size=Size-1_e-implies-unit-pp))))

(defthm
  Size-<-Size-**_e-lemma-1
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y)
		(not (==_e y (0_e))))
	   (==_e (++_e x
		       (-_e (**_e x y (qq_e x (**_e x y)))))
		 (rr_e x (**_e x y))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Division-property-for-qq_e-&-rr_e
		  (y (**_e x y)))
		 (:instance
		  (:theorem
		   (implies (and (edp x)
				 (edp y)
				 (edp z))
			    (iff (==_e x (++_e y z))
				 (==_e y (++_e x (-_e z))))))
		  (y (rr_e x (**_e x y)))
		  (z (**_e x y (qq_e x (**_e x y)))))))))

(defthm
  Size-<-Size-**_e-lemma-2
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y)
		(not (==_e y (0_e)))
		(not (==_e (rr_e x (**_e x y))
			   (0_e))))
	   (>= (Size (rr_e x (**_e x y)))
	       (Size x)))
  :rule-classes nil
  :hints (("Goal"
	   :use (Size-<-Size-**_e-lemma-1))))

(defthm
  Size-<-Size-**_e-lemma-3
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y)
		(not (==_e y (0_e)))
		(equal (Size x)
		       (Size (**_e x y))))
	   (unit-pp y))
  :rule-classes nil
  :hints (("Goal"
	   :use (Size-<-Size-**_e-lemma-2
		 (:instance
		  divides-pp-suff
		  (y (1_e))
		  (x y)
		  (z (qq_e x (**_e x y))))
		 (:instance
		  Division-property-for-qq_e-&-rr_e
		  (y (**_e x y)))))))

(defthm
  Size-<-Size-**_e
  (implies (and (not (unit-pp y))
		(edp x)
		(not (==_e x (0_e)))
		(edp y)
		(not (==_e y (0_e))))
	   (< (Size x)
	      (Size (**_e x y))))
  :rule-classes (:linear
		 :rewrite)
  :hints (("Goal"
	   :use Size-<-Size-**_e-lemma-3)
	  ("[1]Subgoal 2"
	   :use (:theorem
		 (implies (and (edp x)
			       (not (==_e x (0_e)))
			       (edp y)
			       (not (==_e y (0_e))))
			  (integerp (size (**_e x y))))))
	  ("[1]Subgoal 1"
	   :use (:theorem
		 (implies (and (edp x)
			       (not (==_e x (0_e)))
			       (edp y)
			       (not (==_e y (0_e))))
			  (integerp (size (**_e x y))))))))

(defthm
  Unit-pp-divides-pp-witness
  (implies (unit-pp x)
	   (unit-pp (divides-pp-witness x (1_e)))))

(defthm
  Divides-pp-witness-divides-pp-witness
  (implies (unit-pp x)
	   (==_e (divides-pp-witness (divides-pp-witness x (1_e))
				     (1_e))
		 x))
  :hints (("Goal"
	   :in-theory (disable divides-pp-implies-witness=qq_e)
	   :use (Unit-pp-divides-pp-witness
		 (:instance
		  Cancellation-Laws-for-**_e
		  (z (divides-pp-witness x (1_e)))
		  (y (divides-pp-witness (divides-pp-witness x (1_e))
					 (1_e))))
		 (:instance
		  1_e-0_e
		  (x (divides-pp-witness (0_e)(0_e))))))
	  ("Subgoal 2"
	   :use 1_e-0_e)))

(defthm
  Unit-pp-closure-**_e
  (implies (and (unit-pp u)
		(unit-pp v))
	   (unit-pp (**_e u v)))
  :hints (("Goal"
	   :in-theory (disable divides-pp-edp-1)
	   :use (:instance
		 divides-pp-suff
		 (x (**_e u v))
		 (y (1_e))
		 (z (**_e (divides-pp-witness u (1_e))
			  (divides-pp-witness v (1_e))))))))

(defthm
  Inverse-Cancellation-Laws-**_e
  (implies (and (edp u)
		(edp x)
		(edp y)
		(==_e (**_e u x)(1_e)))
	   (and (==_e (**_e u x y) y)
		(==_e (**_e u y x) y)
		(==_e (**_e x u y) y)
		(==_e (**_e x y u) y)
		(==_e (**_e y u x) y)
		(==_e (**_e y x u) y)))
  :hints (("Goal"
	   :use (:instance
		 associativity-laws-for-++_e-&-**_e
		 (x u)
		 (y x)
		 (z y)))))

(defthm
  Unit-pp-**_e-inverse
  (implies (and (unit-pp u)
		(edp x)
		(==_e (**_e u x)
		      y))
	   (==_e (**_e y (divides-pp-witness u (1_e)))
		 x))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (unit-pp u)
				(==_e (**_e u x)
				      y)
				(edp x))
			   (==_e (**_e y (divides-pp-witness u (1_e)))
				 x)))))

(defthm
  Unit-pp-Inverse-Distributive-Law
  (implies (and (unit-pp x)
		(unit-pp y))
	   (==_e (divides-pp-witness (**_e x y)(1_e))
		 (**_e (divides-pp-witness x (1_e))
		       (divides-pp-witness y (1_e)))))
  :hints (("Goal"
	   :by (:functional-instance
                acl2-agp::Distributivity-of-inv-over-op
                (acl2-agp::equiv ==_e)
                (acl2-agp::pred unit-pp)
                (acl2-agp::op binary-**_e)
                (acl2-agp::id 1_e)
                (acl2-agp::inv (lambda (x)(divides-pp-witness x (1_e))))))
	  ("Subgoal 5"
; Changed after v4-3 by Kaufmann/Moore, for tau system --
; tau on {"Subgoal 3"} tau off: {"Subgoal 8"}
	   :use (:instance
                 Unit-pp-closure-**_e
                 (u x)
                 (v y)))))

(defthm
  Divides-pp-witness-1_e
  (==_e (divides-pp-witness (1_e)(1_e))
	(1_e))
  :hints (("Goal"
	   :in-theory (disable least-divides-pp=1_e
			       divides-pp-suff)
	   :use (:instance
		 divides-pp-suff
		 (x (1_e))
		 (y (1_e))
		 (z (1_e))))))

(defthm
  Divides-pp-witness-_-_e-1_e
  (==_e (divides-pp-witness (-_e (1_e))(1_e))
	(-_e (1_e)))
  :hints (("Goal"
	   :use (:instance
		 Unit-pp-**_e-inverse
		 (u (-_e (1_e)))
		 (x (-_e (1_e)))
		 (y (1_e))))))

(defthm
  Not-Unit-pp-0_e
  (implies (and (not (==_e x (0_e)))
		(edp x))
	   (not (unit-pp (0_e))))
  :hints (("Goal"
	   :in-theory (disable 1_e-0_e)
	   :use 1_e-0_e)))

(defthm
  Unit-pp-0_e
  (implies (==_e (1_e)(0_e))
	   (unit-pp (0_e))))

(defthm
  Unit-pp-edp
  (implies (unit-pp x)
	   (edp x))
  :rule-classes :forward-chaining)

(defthm
  Unit-pp-**_e=>unit-pp-factor-left
  (implies (and (edp x)
		(edp y)
		(unit-pp (**_e x y)))
	   (unit-pp x))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 divides-pp-suff
		 (y (1_e))
		 (z (**_e y (divides-pp-witness (**_e x y)(1_e))))))))

(defthm
  Unit-pp-**_e=>unit-pp-factor-right
  (implies (and (edp x)
		(edp y)
		(unit-pp (**_e x y)))
	   (unit-pp y))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 Unit-pp-**_e=>unit-pp-factor-left
		 (x y)
		 (y x)))))

(in-theory (disable (:executable-counterpart unit-p)
		    (:executable-counterpart unit-p1)
		    (:executable-counterpart unit-pp)))

;;;;;;;;;;;;;;;;;;;;;;;;
;; Reducible-p and
;; Irreducible-p theory:

(defun-sk
  Reducible-p (x)
  (exists (y z)(and (edp y)
		    (edp z)
		    (not (unit-p y))
		    (not (unit-p z))
		    (=_e (*_e y z) x))))

(defun-sk
  Reducible-p1 (x)
  (exists (y z)(and (edp y)
		    (edp z)
		    (not (unit-p1 y))
		    (not (unit-p1 z))
		    (==_e (**_e y z) x))))

(defthm
  Reducible-p1-suff-1
  (implies (and (==_e (**_e y z) x)
		(edp y)
		(edp z)
		(not (unit-p y))
		(not (unit-p z)))
	   (reducible-p1 x))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p)
			       (:definition unit-p1))
	   :use ((:instance
		  unit-p-=-unit-p1
		  (x y))
		 (:instance
		  unit-p-=-unit-p1
		  (x z))))))

(defthm
  Reducible-p1-suff-2
  (implies (and (=_e (*_e y z) x)
		(edp y)
		(edp z)
		(not (unit-p y))
		(not (unit-p z)))
	   (reducible-p1 x))
  :hints (("Goal"
	   :in-theory (e/d ((:definition ==_e)
			    (:definition binary-**_e))
			   ((:definition reducible-p1)
			    (:definition unit-p)))
	   :use (Reducible-p1-suff-1
		 (:instance
		  congruence-laws
		  (y1 (*_e y z))
		  (y2 x))))))

(defthm
  Reducible-p-implies-reducible-p1
  (implies (reducible-p x)
	   (reducible-p1 x))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-p1)
			       (:definition unit-p)))))

(defthm
  Reducible-p-suff-1
  (implies (and (=_e (*_e y z) x)
		(edp y)
		(edp z)
		(not (unit-p1 y))
		(not (unit-p1 z)))
	   (reducible-p x))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p)
			       (:definition unit-p1))
	   :use ((:instance
		  unit-p-=-unit-p1
		  (x y))
		 (:instance
		  unit-p-=-unit-p1
		  (x z))))))

(defthm
  Reducible-p-suff-2
  (implies (and (==_e (**_e y z) x)
		(edp y)
		(edp z)
		(not (unit-p1 y))
		(not (unit-p1 z)))
	   (reducible-p x))
  :hints (("Goal"
	   :in-theory (e/d ((:definition ==_e)
			    (:definition binary-**_e))
			   ((:definition reducible-p)
			    (:definition unit-p1)))
	   :use Reducible-p-suff-1)))

(in-theory (disable (:executable-counterpart binary-**_e)))

(defthm
  Reducible-p1-implies-reducible-p
  (implies (reducible-p1 x)
	   (reducible-p x))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-p)
			       (:definition unit-p1)))))

(defthm
  Reducible-p-iff-reducible-p1
  (iff (reducible-p x)
       (reducible-p1 x))
  :rule-classes nil
  :hints (("Goal"
	   :use (Reducible-p-implies-reducible-p1
		 Reducible-p1-implies-reducible-p))))

(defthm
  Booleanp-reducible-p
  (Booleanp (reducible-p x))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p))
	   :use (:instance
		 congruence-laws
		 (y1 (*_e (mv-nth 0 (reducible-p-witness x))
			 (mv-nth 1 (reducible-p-witness x))))
		 (y2 x)))))

(defthm
  Reducible-p-=-reducible-p1
  (equal (reducible-p x)
	 (reducible-p1 x))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-p)
			       (:definition reducible-p1))
	   :use Reducible-p-iff-reducible-p1)))

(defun
  Reducible-pp-witness (x)
  "Reducible-pp-witness nicely
   modifies reducible-p1-witness."
  (reducible-p1-witness (C_==_e x)))

(defthm
  ==_e-implies-equal-reducible-pp-witness
  (implies (==_e y1 y2)
	   (equal (reducible-pp-witness y1)
		  (reducible-pp-witness y2)))
  :rule-classes :congruence)

(defun
  Reducible-pp (x)
  (mv-let (y z)
	  (reducible-pp-witness x)
	  (and (edp y)
	       (edp z)
	       (not (unit-pp y))
	       (not (unit-pp z))
	       (==_e (**_e y z) x))))

(defthm
  ==_e-implies-equal-reducible-pp
  (implies (==_e y1 y2)
	   (equal (reducible-pp y1)
		  (reducible-pp y2)))
  :rule-classes :congruence)

(defthm
  Reducible-p1-suff-3
  (implies (and (edp y)
		(edp z)
		(not (unit-pp y))
		(not (unit-pp z))
		(==_e (**_e y z) x))
	   (reducible-p1 x))
  :hints (("Goal"
	   :use ((:instance
		  Unit-p1-=-Unit-pp
		  (x y))
		 (:instance
		  Unit-p1-=-Unit-pp
		  (x z))))))

(defthm
  Reducible-pp-suff
  (implies (and (==_e (**_e y z) x)
		(edp y)
		(edp z)
		(not (unit-pp y))
		(not (unit-pp z)))
	   (reducible-pp x))
  :hints (("Goal"
	   :in-theory (disable reducible-p1-suff-3)
	   :use (:instance
		 reducible-p1-suff-3
		 (x (C_==_e x))))))

(in-theory (disable (:definition reducible-pp-witness)
		    (:executable-counterpart reducible-pp)))

(defthm
  Reducible-p1-implies-reducible-pp
  (implies (reducible-p1 x)
	   (reducible-pp x))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable unit-p1 unit-pp
			       (:definition reducible-pp))
	  :use ((:instance
		 Reducible-pp-suff
		 (y (car (reducible-p1-witness x)))
		 (z (mv-nth 1 (reducible-p1-witness x))))
		(:instance
		 unit-p1-=-unit-pp
		 (x (car (reducible-p1-witness x))))
		(:instance
		 unit-p1-=-unit-pp
		 (x (mv-nth 1 (reducible-p1-witness x))))))))

(defthm
  Reducible-pp-implies-reducible-p1
  (implies (reducible-pp x)
	   (reducible-p1 x))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable unit-p1 unit-pp
			       (:definition reducible-p1))
	  :use ((:instance
		 Reducible-p1-suff-3
		 (y (car (reducible-pp-witness x)))
		 (z (mv-nth 1 (reducible-pp-witness x))))))))

(defthm
  Reducible-p1-=-reducible-pp
  (equal (reducible-p1 x)
	 (reducible-pp x))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable reducible-p1
			       reducible-pp)
	   :use (Reducible-p1-implies-reducible-pp
		 Reducible-pp-implies-reducible-p1))))

(defthm
  Reducible-p-=-reducible-pp
  (equal (reducible-p x)
	 (reducible-pp x))
  :rule-classes nil
  :hints (("Goal"
	   :use (Reducible-p1-=-reducible-pp
		 Reducible-p-=-reducible-p1))))

(defthm
  Reducible-pp-edp
  (implies (reducible-pp x)
	   (edp x))
  :rule-classes :forward-chaining
  :hints (("Goal"
	   :use (:instance
		 closure-laws-for-++_e-&-**_e
		 (x (mv-nth 0 (reducible-pp-witness x)))
		 (y (mv-nth 1 (reducible-pp-witness x)))))))

(defthm
  Reducible-pp-0_e
  (implies (and (not (==_e x (0_e)))
		(edp x))
	   (reducible-pp (0_e)))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp)
			       (:definition reducible-pp))
	   :use (:instance
		 reducible-pp-suff
		 (x (0_e))
		 (y (0_e))
		 (z (0_e))))))

(defthm
  Unit-pp-not-reducible-pp
  (implies (unit-pp x)
	   (not (reducible-pp x)))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp))
	   :use (:instance
		 unit-pp-**_e=>unit-pp-factor-left
		 (x (mv-nth 0 (reducible-pp-witness x)))
		 (y (mv-nth 1 (reducible-pp-witness x)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Now, define Irreducible-p so that some form of unique
;; factorization (into irreducible elements) can be
;; proved for Euclidean Domains.

;;  Clearly (0_e) can be factored in many ways, if the
;;   Euclidean Domain is not trivial (that is, if the
;;   domain contains at least two distinct elements).
;;  Also any factorization of (0_e) must contain at
;;   least one (0_e).

;;  Also units can be factored in many ways. For example
;;   (-_e (1_e)) = (*_e (-_e (1_e))(-_e (1_e))(-_e (1_e)))
;;               = (*_e (-_e (1_e))(-_e (1_e))(-_e (1_e))
;;                                 (-_e (1_e))(-_e (1_e)))
;;  Unique factorization should at least imply that any two
;;   factorizations contain the same number of factors.

;; Irreducible elements are non-zero, non-unit, non-reducible
;;  elements of the domain.

(defun
  Irreducible-p (x)
  (and (edp x)
       (not (unit-p x))
       (not (reducible-p x))))

(in-theory (disable (:executable-counterpart irreducible-p)))

(defun
  Irreducible-pp (x)
  (and (edp x)
       (not (unit-pp x))
       (not (reducible-pp x))))

(in-theory (disable (:executable-counterpart irreducible-pp)))

(defthm
  ==_e-implies-equal-irreducible-pp
  (implies (==_e y1 y2)
	   (equal (irreducible-pp y1)
		  (irreducible-pp y2)))
  :rule-classes :congruence)

(defthm
  Irreducible-p-=-irreducible-pp
  (equal (irreducible-p x)
	 (irreducible-pp x))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-p)
			       (:definition reducible-pp)
			       (:definition unit-p)
			       (:definition unit-pp))
	   :use (Unit-p-=-Unit-pp
		 Reducible-p-=-reducible-pp))))

(defthm
  Irreducible-pp-not-0_e
  (implies (irreducible-pp x)
	   (not (==_e x (0_e))))
  :rule-classes :forward-chaining
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-pp)
			       (:definition unit-pp))
	   :use Unit-pp-0_e)))

(defthm
  Irreducible-pp-implies-unit-pp-factor
  (implies (and (irreducible-pp x)
		(edp y)
		(edp z)
		(==_e (**_e y z) x))
	   (or (unit-pp y)
	       (unit-pp z)))
  :rule-classes ((:rewrite
		  :corollary
		  (and (implies (and (==_e (**_e y z) x)
				     (irreducible-pp x)
				     (not (unit-pp y))
				     (edp y)
				     (edp z))
				(unit-pp z))
		       (implies (and (==_e (**_e y z) x)
				     (irreducible-pp x)
				     (not (unit-pp z))
				     (edp y)
				     (edp z))
				(unit-pp y)))))
  :hints (("Goal"
	   :use reducible-pp-suff)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Factorization existence theory:

(defun
  Irreducible-factors-1 (x)
  "Return a list, lst, of irreducible
   elements of edp, so that if x is
   in edp, x is not ==_e to 0_e, and x
   is not an unit, then x ==_e product
   of the members in lst."
  (declare (xargs :measure (if (and (edp x)
				    (not (==_e x (0_e))))
			       (Size x)
			       0)
		  :hints (("subgoal 2"
			   :in-theory (disable (:definition mv-nth)
					       reducible-pp-edp)
			   :use (:instance
				 size-<-size-**_e
				 (x (mv-nth 1 (reducible-pp-witness x)))
				 (y (mv-nth 0 (reducible-pp-witness x)))))
			  ("subgoal 1"
			   :in-theory (disable (:definition mv-nth)
					       reducible-pp-edp)
			   :use (:instance
				 size-<-size-**_e
				 (x (mv-nth 0 (reducible-pp-witness x)))
				 (y (mv-nth 1 (reducible-pp-witness x))))))))
  (cond ((or (not (edp x))
	     (==_e x (0_e))
	     (equal (Size x)
		    (Size (1_e))))
	 nil)
	((reducible-pp x)
	 (mv-let (y z)
		 (reducible-pp-witness x)
		 (append (irreducible-factors-1 y)
			 (irreducible-factors-1 z))))
	(t (list x))))

(in-theory (disable (:executable-counterpart irreducible-factors-1)))

(defthm
  Size-<-size-*_e
  (implies (and (not (unit-p y))
		(edp x)
		(not (=_e x (0_e)))
		(edp y)
		(not (=_e y (0_e))))
	   (< (size x) (size (*_e x y))))
  :rule-classes nil
  :hints (("goal"
	   :in-theory (e/d ((:definition ==_e)
			    (:definition binary-**_e))
			   ((:definition unit-p)
			    (:definition unit-pp)))
	   :use (size-<-size-**_e
		 unit-p-=-unit-pp
		 (:instance
		  unit-p-=-unit-pp
		  (x y))))))

(defun
  Irreducible-factors (x)
  "Return a list, lst, of irreducible
   elements of edp, so that if x is
   in edp, x is not =_e to 0_e, and x
   is not an unit, then x =_e product
   of the members in lst."
  (declare (xargs :measure (if (and (edp x)
				    (not (=_e x (0_e))))
			       (Size x)
			       0)
		  :hints (("subgoal 2"
			   :in-theory (disable (:definition mv-nth)
					       (:definition unit-p)
					       Zero-Divisor-Law)
			   :use ((:instance
				  equivalence-law
				  (y (*_e (mv-nth 0 (reducible-p-witness x))
					  (mv-nth 1 (reducible-p-witness x))))
				  (z (0_e)))
				 (:instance
				  Zero-Divisor-Law
				  (x (mv-nth 0 (reducible-p-witness x)))
				  (y (mv-nth 1 (reducible-p-witness x))))
				 (:instance
				  size-<-size-*_e
				  (x (mv-nth 1 (reducible-p-witness x)))
				  (y (mv-nth 0 (reducible-p-witness x))))
				 (:instance
				  Congruence-for-Size
				  (y1 (*_e (mv-nth 0 (reducible-p-witness x))
					   (mv-nth 1 (reducible-p-witness x))))
				  (y2 (*_e (mv-nth 1 (reducible-p-witness x))
					   (mv-nth 0 (reducible-p-witness x)))))
				 (:instance
				  Congruence-for-Size
				  (y1 (*_e (mv-nth 0 (reducible-p-witness x))
					   (mv-nth 1 (reducible-p-witness x))))
				  (y2 x))))
			  ("subgoal 1"
			   :in-theory (disable (:definition mv-nth)
					       (:definition unit-p)
					       Zero-Divisor-Law)
			   :use ((:instance
				  equivalence-law
				  (y (*_e (mv-nth 0 (reducible-p-witness x))
					  (mv-nth 1 (reducible-p-witness x))))
				  (z (0_e)))
				 (:instance
				  Zero-Divisor-Law
				  (x (mv-nth 0 (reducible-p-witness x)))
				  (y (mv-nth 1 (reducible-p-witness x))))
				 (:instance
				  size-<-size-*_e
				  (x (mv-nth 0 (reducible-p-witness x)))
				  (y (mv-nth 1 (reducible-p-witness x))))
				 (:instance
				  Congruence-for-Size
				  (y1 (*_e (mv-nth 0 (reducible-p-witness x))
					   (mv-nth 1 (reducible-p-witness x))))
				  (y2 x)))))))
  (cond ((or (not (edp x))
	     (=_e x (0_e))
	     (equal (Size x)
		    (Size (1_e))))
	 nil)
	((reducible-p x)
	 (mv-let (y z)
		 (reducible-p-witness x)
		 (append (irreducible-factors y)
			 (irreducible-factors z))))
	(t (list x))))

; No longer needed after v3-6-1 (essentially part of axioms.lisp):
; (defthm
;   True-listp-append
;   (implies (true-listp lst2)
;            (true-listp (append lst1 lst2)))
;   :rule-classes :type-prescription)

(defthm
  True-listp-irreducible-factors-1
  (true-listp (irreducible-factors-1 x))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp)
			       (:definition reducible-pp)))))

(defthm
  True-listp-irreducible-factors
  (true-listp (irreducible-factors x))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p)
			       (:definition reducible-p)))))

(defun
  Irreducible-listp-1 (lst)
  (if (consp lst)
      (and (irreducible-pp (car lst))
	   (irreducible-listp-1 (cdr lst)))
      t))

(defun
  Irreducible-listp (lst)
  (if (consp lst)
      (and (irreducible-p (car lst))
	   (irreducible-listp (cdr lst)))
      t))

(defthm
  Irreducible-listp-1-append
  (implies (and (irreducible-listp-1 lst1)
		(irreducible-listp-1 lst2))
	   (irreducible-listp-1 (append lst1 lst2)))
  :hints (("goal"
	   :in-theory (disable (:definition irreducible-pp)))))

(defthm
  Irreducible-listp-append
  (implies (and (irreducible-listp lst1)
		(irreducible-listp lst2))
	   (irreducible-listp (append lst1 lst2)))
  :hints (("goal"
	   :in-theory (disable (:definition irreducible-p)))))

(defthm
  Size-implies-irreducible-pp
  (implies (and (edp x)
		(not (equal (size x)
			    (size (1_e))))
		(not (reducible-pp x)))
	   (irreducible-pp x))
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-pp)
			       (:definition unit-pp))
	   :use Size-unit-pp=Size-1_e)))

(defthm
  Size-implies-irreducible-p
  (implies (and (edp x)
		(not (equal (size x)
			    (size (1_e))))
		(not (reducible-p x)))
	   (irreducible-p x))
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-p)
			       (:definition unit-p))
	   :use Size-unit-p=Size-1_e)))

(defthm
  Irreducible-listp-1-irreducible-factors-1
  (irreducible-listp-1 (irreducible-factors-1 x))
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-pp)
			       (:definition unit-pp)))))

(defthm
  Irreducible-listp-irreducible-factors
  (irreducible-listp (irreducible-factors x))
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-p)
			       (:definition unit-p)))))

(defun
  Edp-listp (lst)
  (if (consp lst)
      (and (edp (car lst))
	   (edp-listp (cdr lst)))
      t))

(defthm
  Irreducible-listp-1-implies-edp-listp
  (implies (irreducible-listp-1 lst)
	   (edp-listp lst)))

(defthm
  Irreducible-listp-implies-edp-listp
  (implies (irreducible-listp lst)
	   (edp-listp lst)))

(defthm
  Edp-listp-irreducible-factors-1
  (edp-listp (irreducible-factors-1 x)))

(defthm
  Edp-listp-irreducible-factors
  (edp-listp (irreducible-factors x)))

(defun
  **_e-lst (lst)
  (if (consp lst)
      (if (edp (car lst))
	  (**_e (car lst)(**_e-lst (cdr lst)))
	  (0_e))
      (1_e)))

(in-theory (disable (:executable-counterpart **_e-lst)))

(defun
  *_e-lst (lst)
  (if (consp lst)
      (if (edp (car lst))
	  (*_e (car lst)(*_e-lst (cdr lst)))
	  (0_e))
      (1_e)))

(in-theory (disable (:executable-counterpart *_e-lst)))

(defthm
  Edp-**_e-lst
  (edp (**_e-lst lst)))

(defthm
  Edp-*_e-lst
  (edp (*_e-lst lst)))

(defthm
  **_e-lst-append
  (==_e (**_e-lst (append lst1 lst2))
	(**_e (**_e-lst lst1)
	      (**_e-lst lst2))))

(defthm
  *_e-lst-=-**_e-lst
  (equal (*_e-lst lst)
	 (**_e-lst lst))
  :rule-classes nil
  :hints (("Subgoal *1/1"
	   :in-theory (enable (:definition binary-**_e)))))

(defthm
  *_e-lst-append
  (=_e (*_e-lst (append lst1 lst2))
       (*_e (*_e-lst lst1)
	    (*_e-lst lst2)))
  :hints (("Goal"
	   :in-theory (e/d ((:definition ==_e)
			    (:definition binary-**_e))
			   (**_e-lst-append))
	   :use (**_e-lst-append
		 (:instance
		  *_e-lst-=-**_e-lst
		  (lst (append lst1 lst2)))
		 (:instance
		  *_e-lst-=-**_e-lst
		  (lst lst1))
		 (:instance
		  *_e-lst-=-**_e-lst
		  (lst lst2))))))

(defthm
  **_e-lst-irreducible-factors-1
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(not (unit-pp x)))
	   (==_e (**_e-lst (irreducible-factors-1 x)) x))
  :hints (("Goal"
	   :in-theory (disable (:definition mv-nth)
			       (:definition unit-pp)

; The authors want unit-pp to stay in the problem.  But the enabled rewrite rule
; (DEFTHM UNIT-PP-NOT-REDUCIBLE-PP
;  (IMPLIES (UNIT-PP X)
;           (NOT (REDUCIBLE-PP X))))
; is also a tau rule that removes unit-pp given the earlier assumption of
; (reducible-pp x).  So we must ensure that the tau-system is disabled.

                               (:executable-counterpart tau-system)
                               ))))

(defthm
  Right-unicity-law-for-*_e
  (implies (edp x)
	   (=_e (*_e x (1_e)) x))
  :hints (("Goal"
	   :in-theory (disable Left-Unicity-Laws
			       Equivalence-law)
	   :use (Left-Unicity-Laws
		 (:instance
		  Equivalence-law
		  (x (*_e x (1_e)))
		  (y (*_e (1_e) x))
		  (z x))))))

(defthm
  *_e-congruence
  (implies (and (edp x1)
		(edp x2)
		(edp y1)
		(edp y2)
		(=_e x1 x2)
		(=_e y1 y2))
	   (=_e (*_e x1 y1)
		(*_e x2 y2)))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Congruence-laws
		  (y1 x1)
		  (y2 x2)
		  (z y1))
		 (:instance
		  Congruence-laws
		  (x x2))
		 (:instance
		  Equivalence-law
		  (x (*_e x1 y1))
		  (y (*_e x2 y1))
		  (z (*_e x2 y2)))))))

(defthm
  *_e-lst-irreducible-factors
  (implies (and (edp x)
		(not (=_e x (0_e)))
		(not (unit-p x)))
	   (=_e (*_e-lst (irreducible-factors x)) x))
  :hints (("Goal"
	   :do-not generalize
	   :in-theory (disable (:definition mv-nth)
			       (:definition unit-p)))
	  ("Subgoal *1/17"
	   :in-theory (disable (:definition mv-nth)
			       (:definition unit-p)
			       Equivalence-law)
	   :use ((:instance
		  *_e-congruence
		  (x1 (*_e-lst (irreducible-factors
				(mv-nth 0 (reducible-p-witness x)))))
		  (x2 (mv-nth 0 (reducible-p-witness x)))
		  (y1 (*_e-lst (irreducible-factors
				(mv-nth 1 (reducible-p-witness x)))))
		  (y2 (mv-nth 1 (reducible-p-witness x))))
		 (:instance
		  equivalence-law
		  (x (*_e-lst (append (irreducible-factors
				       (mv-nth 0 (reducible-p-witness x)))
				      (irreducible-factors
				       (mv-nth 1 (reducible-p-witness x))))))
		  (y (*_e (*_e-lst (irreducible-factors
				    (mv-nth 0 (reducible-p-witness x))))
			  (*_e-lst (irreducible-factors
				    (mv-nth 1 (reducible-p-witness x))))))
		  (z (*_e (mv-nth 0 (reducible-p-witness x))
			  (mv-nth 1 (reducible-p-witness x)))))
		 (:instance
		  equivalence-law
		  (x (*_e-lst (append (irreducible-factors
				       (mv-nth 0 (reducible-p-witness x)))
				      (irreducible-factors
				       (mv-nth 1 (reducible-p-witness x))))))
		  (y (*_e (mv-nth 0 (reducible-p-witness x))
			  (mv-nth 1 (reducible-p-witness x))))
		  (z x))))
	  ("subgoal *1/15"
	   :use (:instance
		 (:theorem
		  (implies (and (edp x)
				(edp y)
				(edp z)
				(=_e x y)
				(=_e x z))
			   (=_e y z)))
		 (x (*_e (mv-nth 0 (reducible-p-witness x))
			 (mv-nth 1 (reducible-p-witness x))))
		 (y x)
		 (z (0_e))))
	  ("subgoal *1/9"
	   :use (:instance
		 (:theorem
		  (implies (and (edp x)
				(edp y)
				(edp z)
				(=_e x y)
				(=_e x z))
			   (=_e y z)))
		 (x (*_e (mv-nth 0 (reducible-p-witness x))
			 (mv-nth 1 (reducible-p-witness x))))
		 (y x)
		 (z (0_e))))
	  ("subgoal *1/7"
	   :use (:instance
		 (:theorem
		  (implies (and (edp x)
				(edp y)
				(edp z)
				(=_e x y)
				(=_e x z))
			   (=_e y z)))
		 (x (*_e (mv-nth 0 (reducible-p-witness x))
			 (mv-nth 1 (reducible-p-witness x))))
		 (y x)
		 (z (0_e))))))

(defthm
  IRREDUCIBLE-FACTORIZATION-EXISTENCE
  (and (true-listp (irreducible-factors x))
       (edp-listp  (irreducible-factors x))
       (irreducible-listp (irreducible-factors x))
       (implies (and (edp x)
		     (not (=_e x (0_e)))
		     (not (unit-p x)))
		(=_e (*_e-lst (irreducible-factors x)) x)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p)))))

;;;;;;;;;;;;;;
;; GCD Theory:

;;Determine if g is a gcd of x and y.
(defun-sk
  gcd-p (x y g)
  (forall d (and (divides-p g x)
		 (divides-p g y)
		 (implies (and (divides-p d x)
			       (divides-p d y))
			  (divides-p d g)))))

(defun
  Gcd-pp-witness (x y g)
  "Gcd-pp-witness nicely
   modifies Gcd-p-witness."
  (gcd-p-witness (C_==_e x)
		 (C_==_e y)
		 (C_==_e g)))

(defthm
  ==_e-implies-==_e-gcd-pp-witness-1
  (implies (==_e x1 x2)
	   (==_e (gcd-pp-witness x1 y g)
		 (gcd-pp-witness x2 y g)))
  :rule-classes :congruence)

(defthm
  ==_e-implies-==_e-gcd-pp-witness-2
  (implies (==_e y1 y2)
	   (==_e (gcd-pp-witness x y1 g)
		 (gcd-pp-witness x y2 g)))
  :rule-classes :congruence)

(defthm
  ==_e-implies-==_e-gcd-pp-witness-3
  (implies (==_e g1 g2)
	   (==_e (gcd-pp-witness x y g1)
		 (gcd-pp-witness x y g2)))
  :rule-classes :congruence)

(defun
  Gcd-pp (x y g)
  (let ((d (gcd-pp-witness x y g)))
       (and (divides-pp g x)
	    (divides-pp g y)
	    (implies (and (divides-pp d x)
			  (divides-pp d y))
		     (divides-pp d g)))))

(defthm
  ==_e-implies-equal-gcd-pp-1
  (implies (==_e x1 x2)
	   (equal (gcd-pp x1 y g)
		  (gcd-pp x2 y g)))
  :rule-classes :congruence)

(defthm
  ==_e-implies-equal-gcd-pp-2
  (implies (==_e y1 y2)
	   (equal (gcd-pp x y1 g)
		  (gcd-pp x y2 g)))
  :rule-classes :congruence)

(defthm
  ==_e-implies-equal-gcd-pp-3
  (implies (==_e g1 g2)
	   (equal (gcd-pp x y g1)
		  (gcd-pp x y g2)))
  :rule-classes :congruence)

(defthm
  Gcd-p-necc-1
  (implies (not (and (divides-pp g x)
		     (divides-pp g y)
		     (implies (and (divides-pp d x)
				   (divides-pp d y))
			      (divides-pp d g))))
	   (not (gcd-p x y g)))
  :hints (("Goal"
	   :in-theory (disable (:definition divides-p)
			       (:definition divides-pp)
			       (:definition gcd-p))
	   :use (gcd-p-necc
		 (:instance
		  divides-p-=-divides-pp
		  (x g)
		  (y x))
		 (:instance
		  divides-p-=-divides-pp
		  (x g))
		 (:instance
		  divides-p-=-divides-pp
		  (x d)
		  (y x))
		 (:instance
		  divides-p-=-divides-pp
		  (x d))
		 (:instance
		  divides-p-=-divides-pp
		  (x d)
		  (y g))))))

(defthm
  Gcd-pp-necc-lemma-1
  (implies (not (and (divides-pp g x)
		     (divides-pp g y)
		     (implies (and (divides-pp d x)
				   (divides-pp d y))
			      (divides-pp d g))))
	   (not (and (divides-p (C_==_e g)(C_==_e x))
		     (divides-p (C_==_e g)(C_==_e y))
		     (implies (and (divides-p (gcd-p-witness (C_==_e x)
							     (C_==_e y)
							     (C_==_e g))
					      (C_==_e x))
				   (divides-p (gcd-p-witness (C_==_e x)
							     (C_==_e y)
							     (C_==_e g))
					      (C_==_e y)))
			      (divides-p (gcd-p-witness (C_==_e x)
							(C_==_e y)
							(C_==_e g))
					 (C_==_e g))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition divides-p)
			       (:definition divides-pp))
	   :use (:instance
		 gcd-p-necc-1
		 (x (C_==_e x))
		 (y (C_==_e y))
		 (g (C_==_e g))))))

(defthm
  Gcd-pp-necc-lemma-2
  (implies (not (and (divides-p (C_==_e g)(C_==_e x))
		     (divides-p (C_==_e g)(C_==_e y))
		     (implies (and (divides-p (gcd-p-witness (C_==_e x)
							     (C_==_e y)
							     (C_==_e g))
					      (C_==_e x))
				   (divides-p (gcd-p-witness (C_==_e x)
							     (C_==_e y)
							     (C_==_e g))
					      (C_==_e y)))
			      (divides-p (gcd-p-witness (C_==_e x)
							(C_==_e y)
							(C_==_e g))
					 (C_==_e g)))))
	   (not (and (divides-pp g x)
		     (divides-pp g y)
		     (implies (and (divides-pp (gcd-pp-witness x
							       y
							       g)
					       x)
				   (divides-pp (gcd-pp-witness x
							       y
							       g)
					       y))
			      (divides-pp (gcd-pp-witness x
							  y
							  g)
					  g)))))
  :rule-classes nil
  :hints (("Goal"
          :in-theory (disable (:definition divides-p)
			      (:definition divides-pp))
	  :use ((:instance
		 divides-p-=-divides-pp
		 (x (C_==_e g))
		 (y (C_==_e x)))
		(:instance
		 divides-p-=-divides-pp
		 (x (C_==_e g))
		 (y (C_==_e y)))
		(:instance
		 divides-p-=-divides-pp
		 (x (gcd-p-witness (C_==_e x)
				   (C_==_e y)
				   (C_==_e g)))
		 (y (C_==_e x)))
		(:instance
		 divides-p-=-divides-pp
		 (x (gcd-p-witness (C_==_e x)
				   (C_==_e y)
				   (C_==_e g)))
		 (y (C_==_e y)))
		(:instance
		 divides-p-=-divides-pp
		 (x (gcd-p-witness (C_==_e x)
				   (C_==_e y)
				   (C_==_e g)))
		 (y (C_==_e g)))))))

(defthm
  Gcd-pp-necc
  (implies (not (and (divides-pp g x)
		     (divides-pp g y)
		     (implies (and (divides-pp d x)
				   (divides-pp d y))
			      (divides-pp d g))))
	   (not (gcd-pp x y g)))
  :hints (("Goal"
	   :in-theory (disable (:definition divides-pp)
			       (:definition divides-p)
			       (:definition gcd-pp-witness))
	   :use (Gcd-pp-necc-lemma-1
		 Gcd-pp-necc-lemma-2))))

(in-theory (disable (:definition gcd-pp-witness)
		    (:executable-counterpart gcd-pp)))

(defthm
  Gcd-p-implies-gcd-pp
  (implies (gcd-p x y g)
	   (gcd-pp x y g))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition divides-pp)
			       (:definition gcd-p))
	   :use (:instance
		 Gcd-p-necc-1
		 (d (gcd-pp-witness x y g))))))

(defthm
  Gcd-pp-implies-gcd-p
  (implies (gcd-pp x y g)
	   (gcd-p x y g))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition divides-p)
			       (:definition divides-pp)
			       (:definition gcd-pp))
	   :use ((:instance
		  Gcd-pp-necc
		  (d (gcd-p-witness x y g)))
		 (:instance
		  divides-p-=-divides-pp
		  (x g)
		  (y x))
		 (:instance
		  divides-p-=-divides-pp
		  (x g))
		 (:instance
		  divides-p-=-divides-pp
		  (x (gcd-p-witness x y g))
		  (y g))
		 (:instance
		  divides-p-=-divides-pp
		  (x (gcd-p-witness x y g))
		  (y x))
		 (:instance
		  divides-p-=-divides-pp
		  (x (gcd-p-witness x y g)))))))

(defthm
  Gcd-p-=-gcd-pp
  (equal (gcd-p x y g)
	 (gcd-pp x y g))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition gcd-p)
			       (:definition gcd-pp))
	   :use (Gcd-p-implies-gcd-pp
		 Gcd-pp-implies-gcd-p))))

;;For nonzero element x and element y of edp, choose elements
;; z0,z1 of edp so that the linear combination x z0 + y z1 is
;; a nonzero element and has Size n (if they exists).
(defchoose
  Bezout1 (z0 z1)(x y n)
  (and (edp x)
       (not (==_e x (0_e)))
       (edp y)
       (edp z0)
       (edp z1)
       (not (==_e (++_e (**_e x z0)
			(**_e y z1))
		  (0_e)))
       (equal (Size (++_e (**_e x z0)
			  (**_e y z1)))
	      (nfix n))))

(defthm
  Bezout1-property
  (and (true-listp (Bezout1 x y n))
       (implies (and (integerp n)
		     (>= n 0)
		     (edp x)
		     (not (==_e x (0_e)))
		     (edp y)
		     (edp z0)
		     (edp z1)
		     (not (==_e (++_e (**_e x z0)
				      (**_e y z1))
				(0_e)))
		     (equal (Size (++_e (**_e x z0)
					(**_e y z1)))
			    n))
		(and (edp (mv-nth 0 (Bezout1 x y n)))
		     (edp (mv-nth 1 (Bezout1 x y n)))
		     (not (==_e (++_e (**_e x (mv-nth 0 (Bezout1 x y n)))
				      (**_e y (mv-nth 1 (Bezout1 x y n))))
				(0_e)))
		     (equal (Size (++_e (**_e x (mv-nth 0 (Bezout1 x y n)))
					(**_e y (mv-nth 1 (Bezout1 x y n)))))
			    n))))
  :rule-classes ((:rewrite
		  :corollary
		  (and (true-listp (Bezout1 x y n))
		       (implies (and (integerp n)
				     (>= n 0)
				     (edp x)
				     (not (==_e x (0_e)))
				     (edp y)
				     (equal (Size (++_e (**_e x z0)
							(**_e y z1)))
					    n)
				     (not (==_e (++_e (**_e x z0)
						      (**_e y z1))
						(0_e)))
				     (edp z0)
				     (edp z1))
				(and (edp (mv-nth 0 (Bezout1 x y n)))
				     (edp (mv-nth 1 (Bezout1 x y n)))
				     (not (==_e (++_e (**_e x
							    (mv-nth 0
								    (Bezout1 x y n)))
						      (**_e y
							   (mv-nth 1
								   (Bezout1 x y n))))
						(0_e)))
				     (equal (Size (++_e (**_e x
							      (mv-nth 0
								      (Bezout1 x y n)))
							(**_e y
							      (mv-nth 1
								      (Bezout1 x y n)))
							))
					    n)))))
		 (:type-prescription
		  :corollary
		  (true-listp (Bezout1 x y n))))
  :hints (("Goal"
	   :use Bezout1)))

(defthm
  Bezout1-properties-Size
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y)
		(edp z0)
		(edp z1)
		(not (==_e (++_e (**_e x z0)
				 (**_e y z1))
			   (0_e))))
	   (and (edp (mv-nth 0 (Bezout1 x y (Size (++_e (**_e x z0)
							(**_e y z1))))))
		(edp (mv-nth 1 (Bezout1 x y (Size (++_e (**_e x z0)
							(**_e y z1))))))
		(not (==_e (++_e (**_e x (mv-nth 0 (Bezout1 x y (Size (++_e (**_e x z0)
									    (**_e y z1))
								      ))))
				 (**_e y (mv-nth 1 (Bezout1 x y (Size (++_e (**_e x z0)
									    (**_e y z1))
								      )))))
			   (0_e)))
		(equal (Size (++_e (**_e x (mv-nth 0 (Bezout1 x y (Size (++_e (**_e x z0)
									      (**_e y z1)
									      )))))
				   (**_e y (mv-nth 1 (Bezout1 x y (Size (++_e (**_e x z0)
									      (**_e y z1)
									      )))))))
		       (Size (++_e (**_e x z0)
				   (**_e y z1))))))
  :hints (("Goal"
	   :use (:instance
		 Bezout1-property
		 (n (Size (++_e (**_e x z0)
				(**_e y z1))))))))

(defthm
  Bezout1-properties-Size-1_e-0_e
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (and (edp (mv-nth 0 (Bezout1 x y (Size x))))
		(edp (mv-nth 1 (Bezout1 x y (Size x))))
		(not (==_e (++_e (**_e x (mv-nth 0 (Bezout1 x y (Size x))))
				 (**_e y (mv-nth 1 (Bezout1 x y (Size x)))))
			   (0_e)))
		(equal (Size (++_e (**_e x (mv-nth 0 (Bezout1 x y (Size x))))
				   (**_e y (mv-nth 1 (Bezout1 x y (Size x))))))
		       (Size x))))
  :hints (("Goal"
	   :use (:instance
		 Bezout1-properties-Size
		 (z0 (1_e))
		 (z1 (0_e))))))

(defun
  Find-smallest-n (x y n)
  "Find smallest natp n such that the first two elements
   of the true list (Bezout1 x y n) are in edp, the linear
   combination
               (++_e (**_e x
			   (mv-nth 0 (Bezout1 x y n)))
		     (**_e y
			   (mv-nth 1 (Bezout1 x y n))))
   is nonzero, and the size of the linear conbination is n."
  (declare (xargs :measure (let ((n (nfix n)))
			            (nfix (- (Size x) n)))))
  (if (and (edp x)
	   (not (==_e x (0_e)))
	   (edp y))
      (let ((n (nfix n)))
	   (if (and (< n (size x))
		    (mv-let (z0 z1)
			    (Bezout1 x y n)
			    (not (and (edp z0)
				      (edp z1)
				      (not (==_e (++_e (**_e x z0)
						       (**_e y z1))
						 (0_e)))
				      (equal (Size (++_e (**_e x z0)
							 (**_e y z1)))
					     n)))))
	       (Find-smallest-n x y (+ n 1))
	       n))
      n))

(in-theory (disable (:executable-counterpart Find-smallest-n)))

(defthm
  Integerp-Find-smallest-n
  (implies (integerp n)
	   (integerp (Find-smallest-n x y n)))
  :rule-classes :type-prescription)

(defthm
  Natp-Find-smallest-n
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (and (integerp (Find-smallest-n x y n))
		(>= (Find-smallest-n x y n) 0)))
  :rule-classes :type-prescription)

(defthm
  Find-smallest-n-Size-x
  (implies (<= n (Size x))
	   (<= (Find-smallest-n x y n)
	       (Size x))))

(defthm
  Bezout1-Find-smallest-n
  (implies (and (integerp n)
		(<= 0 n)
		(<= n (Size x))
		(edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (and (edp (mv-nth 0 (Bezout1 x y (Find-smallest-n x y n))))
		(edp (mv-nth 1 (Bezout1 x y (Find-smallest-n x y n))))
		(not (==_e (++_e (**_e x
				       (mv-nth 0
					       (Bezout1 x y (Find-smallest-n x y n)))
				       )
				 (**_e y
				       (mv-nth 1
					       (Bezout1 x y (Find-smallest-n x y n)))
				       )
				 )
			   (0_e)))
		(equal (Size (++_e (**_e x
					 (mv-nth 0
						 (Bezout1 x y (Find-smallest-n x y n))
						 )
					 )
				   (**_e y
					 (mv-nth 1
						 (Bezout1 x y (Find-smallest-n x y n))
						 )
					 )))
		       (Find-smallest-n x y n))))
  :hints (("Goal"
	   :in-theory (disable (:definition mv-nth)))))

(defthm
  Not-Size-Bezout1-n-=-n
  (implies (and (integerp k)
		(integerp n)
		(<= 0 k)
		(<= k n)
		(< n (Find-smallest-n x y k))
		(edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (not (and (edp (mv-nth 0 (Bezout1 x y n)))
		     (edp (mv-nth 1 (Bezout1 x y n)))
		     (not (==_e (++_e (**_e x (mv-nth 0 (Bezout1 x y n)))
				      (**_e y (mv-nth 1 (Bezout1 x y n))))
				(0_e)))
		(equal (Size (++_e (**_e x (mv-nth 0 (Bezout1 x y n)))
				   (**_e y (mv-nth 1 (Bezout1 x y n)))))
		       n))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (< n (Find-smallest-n x y k))
				(integerp k)
				(integerp n)
				(<= 0 k)
				(<= k n)
				(edp x)
				(not (==_e x (0_e)))
				(edp y)
				(edp (mv-nth 0 (Bezout1 x y n)))
				(edp (mv-nth 1 (Bezout1 x y n)))
				(not (==_e (++_e (**_e x (mv-nth 0 (Bezout1 x y n)))
						 (**_e y (mv-nth 1 (Bezout1 x y n))))
					   (0_e))))
			   (not (equal (Size (++_e (**_e x (mv-nth 0 (Bezout1 x y n)))
						   (**_e y (mv-nth 1 (Bezout1 x y n)))
						   ))
				       n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (Find-smallest-n x y 0),
;;   provided x is a nonzero element of edp,
;;   finds the smallest natp n such that
;;          (and (edp (mv-nth 0 (Bezout1 x y n)))
;;               (edp (mv-nth 1 (Bezout1 x y n)))
;;               (not (equal (+_e (*_e x (mv-nth 0 (Bezout1 x y n)))
;;                                (*_e y (mv-nth 1 (Bezout1 x y n))))
;;                           (0_e)))
;;               (equal (Size (+_e (*_e x (mv-nth 0 (Bezout1 x y n)))
;;                                 (*_e y (mv-nth 1 (Bezout1 x y n)))))
;;                      n))
;;   (if it exists).

(defthm
  Natp-Find-smallest-n-0
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (and (integerp (Find-smallest-n x y 0))
		(>= (Find-smallest-n x y 0) 0)))
  :rule-classes nil)

(defthm
  Bezout1-Find-smallest-n-0
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (and (edp (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
		(edp (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
		(not (==_e (++_e (**_e x
				       (mv-nth 0
					       (Bezout1 x y (Find-smallest-n x y 0)))
				       )
				 (**_e y
				       (mv-nth 1
					       (Bezout1 x y (Find-smallest-n x y 0)))
				       )
				 )
			   (0_e)))
		(equal (Size (++_e (**_e x
					 (mv-nth 0
						 (Bezout1 x y (Find-smallest-n x y 0))
						 )
					 )
				   (**_e y
					 (mv-nth 1
						 (Bezout1 x y (Find-smallest-n x y 0))
						 )
					 )))
		       (Find-smallest-n x y 0))))
  :hints (("Goal"
	   :use (:instance
		 Bezout1-Find-smallest-n
		 (n 0)))))

(defthm
  Not-Size-Bezout1-n-=-n-1
  (implies (and (integerp n)
		(<= 0 n)
		(< n (Find-smallest-n x y 0))
		(edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (not (and (edp (mv-nth 0 (Bezout1 x y n)))
		     (edp (mv-nth 1 (Bezout1 x y n)))
		     (not (==_e (++_e (**_e x (mv-nth 0 (Bezout1 x y n)))
				      (**_e y (mv-nth 1 (Bezout1 x y n))))
				(0_e)))
		     (equal (Size (++_e (**_e x (mv-nth 0 (Bezout1 x y n)))
					(**_e y (mv-nth 1 (Bezout1 x y n)))))
			    n))))
  :rule-classes nil
  :hints (("Goal"
	   :by (:instance
		 Not-Size-Bezout1-n-=-n
		 (k 0)))))

(defthm
  Size->=-Find-smallest-n-0
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y)
		(edp z0)
		(edp z1)
		(not (==_e (++_e (**_e x z0)
				 (**_e y z1))
			   (0_e))))
	   (>= (Size (++_e (**_e x z0)
			   (**_e y z1)))
	       (Find-smallest-n x y 0)))
  :rule-classes (:rewrite
		 :linear)
  :hints (("Goal"
	   :in-theory (disable (:definition mv-nth))
	   :use (:instance
		 Not-Size-Bezout1-n-=-n-1
		 (n (Size (++_e (**_e x z0)
				(**_e y z1))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The next sequence of equations and inequalities
;;  is used to establish the existence of the gcd
;;  of any two elements of edp when at least one
;;  of the elements is nonzero. Any gcd of two
;;  elements can always be written as a linear
;;  combination of the two elements.

(defthm
  Equation-0
  (implies (and (edp a)
		(edp b)
		(edp c))
	   (iff (==_e (++_e a b) c)
		(==_e (++_e c (-_e b)) a)))
  :rule-classes nil)

(defthm
  Equation-1
  (implies (and (edp a)
		(edp b)
		(edp c))
	   (equal (==_e (++_e a b) c)
		  (==_e (++_e c (-_e b)) a)))
  :rule-classes nil
  :hints (("Goal"
	   :use Equation-0)))

(defthm
  Equation-2
  (implies (and (edp x)
		(edp y)
		(not (==_e y (0_e))))
	   (==_e (++_e x
		       (-_e (**_e y
				  (qq_e x y))))
		 (rr_e x y)))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 Equation-1
		 (a (rr_e x y))
		 (b (**_e y
			 (qq_e x y)))
		 (c x)))))

(defthm
  Equation-3
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (let ((lc (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			   (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			   )))
	        (==_e (++_e x
			    (-_e (**_e lc
				       (qq_e x lc))))
		      (rr_e x lc))))
  :rule-classes nil
  :hints (("Goal"
 	   :in-theory (disable (:definition find-smallest-n)
 			       (:definition mv-nth))
	   :use (:instance
		 Equation-2
		 (y (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			  (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			  ))))))

(defthm
  Equation-3a
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (let ((lc (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			   (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			   )))
	        (==_e (++_e y
			    (-_e (**_e lc
				       (qq_e y lc))))
		      (rr_e y lc))))
  :rule-classes nil
  :hints (("Goal"
 	   :in-theory (disable (:definition find-smallest-n)
 			       (:definition mv-nth))
	   :use (:instance
		 Equation-2
		 (x y)
		 (y (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			  (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			  ))))))

(defthm
  Inequality-4
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (let ((lc (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			   (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			   )))
	        (or (==_e (++_e x
				(-_e (**_e lc
					   (qq_e x lc))))
			  (0_e))
		    (< (Size (++_e x
				  (-_e (**_e lc
					     (qq_e x lc)))))
		       (Find-smallest-n x y 0)))))
  :rule-classes nil
  :hints (("Goal"
 	   :in-theory (disable (:definition find-smallest-n)
 			       (:definition mv-nth))
	   :use Equation-3)))

(defthm
  Inequality-4a
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (let ((lc (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			   (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			   )))
	        (or (==_e (++_e y
				(-_e (**_e lc
					   (qq_e y lc))))
			  (0_e))
		    (< (Size (++_e y
				  (-_e (**_e lc
					     (qq_e y lc)))))
		       (Find-smallest-n x y 0)))))
  :rule-classes nil
  :hints (("Goal"
 	   :in-theory (disable (:definition find-smallest-n)
 			       (:definition mv-nth))
	   :use Equation-3a)))

(defthm
  Equation-5
  (implies (and (edp x)
		(edp y)
		(edp q)
		(edp b0)
		(edp b1))
	   (==_e (++_e x
		       (-_e (**_e (++_e (**_e x b0)
					(**_e y b1))
				  q)))
		 (++_e (**_e x
			     (++_e (1_e)
				   (-_e (**_e b0 q))))
		      (-_e (**_e y b1 q)))))
  :rule-classes nil)

(defthm
  Equation-5a
  (implies (and (edp x)
		(edp y)
		(edp q)
		(edp b0)
		(edp b1))
	   (==_e (++_e y
		       (-_e (**_e (++_e (**_e x b0)
					(**_e y b1))
				  q)))
		  (++_e (**_e y
			      (++_e (1_e)
				    (-_e (**_e b1 q))))
			(-_e (**_e x b0 q)))))
  :rule-classes nil)

(defthm
  Equation-6
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (let ((lc (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			   (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			   ))
		 (b0 (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
		 (b1 (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0)))))
	        (==_e (++_e x
			    (-_e (**_e lc
				       (qq_e x lc))))
		      (++_e (**_e x
				  (++_e (1_e)
					(-_e (**_e b0
						   (qq_e x lc)))))
			    (++_e (**_e y
					(-_e (**_e b1
						   (qq_e x lc)))))))))
  :rule-classes nil
  :hints (("Goal"
 	   :in-theory (disable (:definition find-smallest-n)
 			       (:definition mv-nth))
	   :use (:instance
		 Equation-5
		 (b0 (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
		 (b1 (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
		 (q (qq_e x
			  (++_e (**_e x
				      (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
				(**_e y
				      (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
				)))))))

(defthm
  Equation-6a
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (let ((lc (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			   (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			   ))
		 (b0 (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
		 (b1 (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0)))))
	        (==_e (++_e y
			    (-_e (**_e lc
				       (qq_e y lc))))
		      (++_e (**_e y
				  (++_e (1_e)
					(-_e (**_e b1
						   (qq_e y lc)))))
			    (-_e (**_e x
				       (**_e b0
					     (qq_e y lc))))))))
  :rule-classes nil
  :hints (("Goal"
 	   :in-theory (disable (:definition find-smallest-n)
 			       (:definition mv-nth))
	   :use (:instance
		 Equation-5a
		 (b0 (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
		 (b1 (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
		 (q (qq_e y
			  (++_e (**_e x
				      (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
				(**_e y
				      (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
				)))))))

(defthm
  Inequality-7
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (let* ((lc (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			    (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			    ))
		  (b0 (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
		  (b1 (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
		  (z0 (++_e (1_e)
			    (-_e (**_e b0
				       (qq_e x lc)))))
		  (z1 (-_e (**_e b1
				 (qq_e x lc)))))
	         (or (==_e (++_e (**_e x z0)
				 (**_e y z1))
			   (0_e))
		     (>= (Size (++_e (**_e x z0)
				     (**_e y z1)))
			 (Find-smallest-n x y 0)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition mv-nth)
			       (:definition find-smallest-n))
	   :use (:instance
		 Size->=-Find-smallest-n-0
		 (z0 (++_e (1_e)
			   (-_e (**_e (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0)))
				      (qq_e x
					    (++_e
					     (**_e x
						   (mv-nth 0
							   (Bezout1 x
								    y
								    (Find-smallest-n x y 0)))
						   )
					     (**_e y
						   (mv-nth 1
							   (Bezout1 x
								    y
								    (Find-smallest-n x y 0)))
						   )))))))
		 (z1 (-_e
		      (**_e (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0)))
			    (qq_e x
				  (++_e
				   (**_e x
					 (mv-nth 0
						 (Bezout1 x y (Find-smallest-n x y 0)
							  )))
				   (**_e y
					 (mv-nth 1
						 (Bezout1 x y (Find-smallest-n x y 0)
							  ))))))))))))

(defthm
  Inequality-7a
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (let* ((lc (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			    (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			    ))
		  (b0 (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
		  (b1 (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
		  (z1 (++_e (1_e)
			    (-_e (**_e b1
				       (qq_e y lc)))))
		  (z0 (-_e (**_e b0
				 (qq_e y lc)))))
	         (or (==_e (++_e (**_e x z0)
				 (**_e y z1))
			   (0_e))
		     (>= (Size (++_e (**_e x z0)
				     (**_e y z1)))
			 (Find-smallest-n x y 0)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition mv-nth)
			       (:definition find-smallest-n))
	   :use (:instance
		 Size->=-Find-smallest-n-0
		 (z1 (++_e (1_e)
			   (-_e (**_e (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0)))
				      (qq_e y
					    (++_e
					     (**_e x
						   (mv-nth 0
							   (Bezout1 x
								    y
								    (Find-smallest-n x y 0)))
						   )
					     (**_e y
						   (mv-nth 1
							   (Bezout1 x
								    y
								    (Find-smallest-n x y 0)))
						   )))))))
		 (z0 (-_e
		      (**_e (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0)))
			    (qq_e y
				  (++_e
				   (**_e x
					 (mv-nth 0
						 (Bezout1 x y (Find-smallest-n x y 0)
							  )))
				   (**_e y
					 (mv-nth 1
						 (Bezout1 x y (Find-smallest-n x y 0)
							  ))))))))))))

(defthm
  Equation-8
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (let ((lc (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			   (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			   )))
	        (==_e (**_e lc
			    (qq_e x lc))
		      x)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition find-smallest-n)
 			       (:definition mv-nth)
			       right-distributivity-law)
	   :use (Inequality-4
		 Equation-6
	         Inequality-7))))

(defthm
  Equation-8a
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (let ((lc (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			   (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))
			   )))
	        (==_e (**_e lc
			    (qq_e y lc))
		      y)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition find-smallest-n)
 			       (:definition mv-nth)
			       right-distributivity-law)

	   :use (Inequality-4a
		 Equation-6a
	         Inequality-7a))))

(defthm
  Divides-pp-Bezout1-x
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (divides-pp (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			     (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0)))))
		       x))
  :hints (("Goal"
	   :in-theory (disable (:definition find-smallest-n)
			       (:definition mv-nth))
	   :use (Equation-8
		 (:instance
		  divides-pp-suff
		  (x (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			   (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))))
		  (y x)
		  (z (qq_e x (++_e (**_e x
					 (mv-nth 0
						 (Bezout1 x y (Find-smallest-n x y 0)))
					 )
				   (**_e y
					 (mv-nth 1
						 (Bezout1 x y (Find-smallest-n x y 0)))
					 )))))))))

(defthm
  Divides-pp-Bezout1-y
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(edp y))
	   (divides-pp (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			     (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0)))))
		       y))
  :hints (("Goal"
	   :in-theory (disable (:definition find-smallest-n)
			       (:definition mv-nth))
	   :use (Equation-8a
		 (:instance
		  divides-pp-suff
		  (x (++_e (**_e x (mv-nth 0 (Bezout1 x y (Find-smallest-n x y 0))))
			   (**_e y (mv-nth 1 (Bezout1 x y (Find-smallest-n x y 0))))))
		  (z (qq_e y (++_e (**_e x
					 (mv-nth 0
						 (Bezout1 x y (Find-smallest-n x y 0)))
					 )
				   (**_e y
					 (mv-nth 1
						 (Bezout1 x y (Find-smallest-n x y 0))))
				   ))))))))

(defun
  Bezout (x y)
  "Return (mv b0 b1) so that
   x b0 + y b1 is a gcd of x and y."
  (if (and (edp x)
	   (not (==_e x (0_e)))
	   (edp y))
      (Bezout1 x y (Find-smallest-n x y 0))
      (mv (0_e)(1_e))))

(defthm
  Edp-mv-nth-Bezout
  (and (edp (mv-nth 0 (Bezout x y)))
       (edp (mv-nth 1 (Bezout x y))))
  :hints (("goal"
	   :in-theory (disable (:definition mv-nth)
			       (:definition find-smallest-n)))))

(defthm
  Gcd-pp-mv-nth-Bezout
  (implies (and (edp x)
		(edp y))
	   (gcd-pp x y (++_e (**_e x (mv-nth 0 (Bezout x y)))
			     (**_e y (mv-nth 1 (Bezout x y))))))
  :hints (("goal"
	   :in-theory (disable (:definition mv-nth)
			       (:definition find-smallest-n)))))

(defthm
  nth-mv-nth
  (equal (nth k lst)(mv-nth k lst)))

(defthm
  Gcd-pp-nth-Bezout
  (implies (and (edp x)
		(edp y))
	   (gcd-pp x y (++_e (**_e x (nth 0 (Bezout x y)))
			     (**_e y (nth 1 (Bezout x y))))))
  :hints (("goal"
	   :in-theory (disable (:definition mv-nth)
			       (:definition find-smallest-n)))))

(in-theory (disable nth-mv-nth))

(defthm
  1st-2nd-mv-nth
  (and (equal (first lst)(mv-nth 0 lst))
       (equal (second lst)(mv-nth 1 lst))))

(defthm
  Gcd-pp-Bezout
  (implies (and (edp x)
		(edp y))
	   (Gcd-pp x y (++_e (**_e x (first  (Bezout x y)))
			     (**_e y (second (Bezout x y))))))
  :hints (("goal"
	   :in-theory (disable (:definition mv-nth)
			       (:definition find-smallest-n)))))

(in-theory (disable 1st-2nd-mv-nth))

(defthm
  COMMON-divisor-mv-nth-Bezout
  (implies (and (edp x)
		(edp y))
	   (and (divides-pp (++_e (**_e x (mv-nth 0 (Bezout x y)))
				  (**_e y (mv-nth 1 (Bezout x y))))
			    x)
		(divides-pp (++_e (**_e x (mv-nth 0 (Bezout x y)))
				  (**_e y (mv-nth 1 (Bezout x y))))
			    y)))
  :hints (("goal"
	   :in-theory (disable (:definition mv-nth)
			       (:definition find-smallest-n)))))

(defthm
  GREATEST-common-divisor-mv-nth-Bezout
  (implies (and (divides-pp d x)
		(divides-pp d y))
	   (divides-pp d (++_e (**_e x (mv-nth 0 (Bezout x y)))
			       (**_e y (mv-nth 1 (Bezout x y))))))
  :hints (("Goal"
	   :in-theory (disable (:definition mv-nth)
			       (:definition bezout)))))

(defthm
  Gcd-pp-associates-pp
  (implies (and (gcd-pp x y g1)
		(gcd-pp x y g2))
	   (equal (associates-pp g1 g2) t))
  :hints (("goal"
	   :use ((:instance
		  gcd-pp-necc
		  (g g1)
		  (d g2))
		 (:instance
		  gcd-pp-necc
		  (g g2)
		  (d g1))))))

(defthm
  Gcd-pp-edp-1
  (implies (gcd-pp x y g)
	   (edp x))
  :rule-classes :forward-chaining
  :hints (("goal"
	   :in-theory (disable (:definition divides-pp)))))

(defthm
  Gcd-pp-edp-2
  (implies (gcd-pp x y g)
	   (edp y))
  :rule-classes :forward-chaining
  :hints (("goal"
	   :in-theory (disable (:definition divides-pp)))))

(defthm
  Gcd-pp-edp-3
  (implies (gcd-pp x y g)
	   (edp g))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Show that any gcd of two edp elements can
;;  always be written as a linear combination
;;  of the two elements.

(defthm
  Gcd=linear-combination
  (implies (gcd-pp x y g)
	   (==_e (++_e (**_e x
			     (mv-nth 0 (Bezout x y))
			     (divides-pp-witness
			      (++_e (**_e x (mv-nth 0 (Bezout x y)))
				    (**_e y (mv-nth 1 (Bezout x y))))
			      g))
		       (**_e y
			     (mv-nth 1 (Bezout x y))
			     (divides-pp-witness
			      (++_e (**_e x (mv-nth 0 (Bezout x y)))
				    (**_e y (mv-nth 1 (Bezout x y))))
			      g)))
		 g))
  :hints (("Goal"
	   :in-theory (disable (:definition bezout)
			       (:definition mv-nth)
			       gcd-pp-mv-nth-Bezout
			       gcd-pp-associates-pp)
	  :use (gcd-pp-mv-nth-Bezout
		(:instance
		 gcd-pp-associates-pp
		 (g2 g)
		 (g1 (++_e (**_e x (mv-nth 0 (Bezout x y)))
			   (**_e y (mv-nth 1 (Bezout x y))))))))))

(defthm
  Associates-pp-implies-equal-gcd-pp-1
  (implies (associates-pp x1 x2)
	   (equal (gcd-pp x1 y g)
		  (gcd-pp x2 y g)))
  :rule-classes :congruence
  :hints (("Goal"
	   :in-theory (disable (:definition divides-pp))
	   :use ((:instance
		  gcd-pp-necc
		  (d (gcd-pp-witness x2 y g))
		  (x x1))
		 (:instance
		  gcd-pp-necc
		  (d (gcd-pp-witness x1 y g))
		  (x x2))))))

(defthm
  Associates-pp-implies-iff-gcd-pp-2
  (implies (associates-pp y1 y2)
	   (iff (gcd-pp x y1 g)
		(gcd-pp x y2 g)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition divides-pp))
	   :use ((:instance
		  gcd-pp-necc
		  (d (gcd-pp-witness x y2 g))
		  (y y1))
		 (:instance
		  gcd-pp-necc
		  (d (gcd-pp-witness x y1 g))
		  (y y2))))))

(defthm
  Associates-pp-implies-equal-gcd-pp-2
  (implies (associates-pp y1 y2)
	   (equal (gcd-pp x y1 g)
		  (gcd-pp x y2 g)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use (Associates-pp-implies-iff-gcd-pp-2
		 (:instance
		  (:theorem
		   (implies (and (booleanp x)
				 (booleanp y))
			    (equal (iff x y)
				   (equal x y))))
		  (x (gcd-pp x y1 g))
		  (y (gcd-pp x y2 g)))))))

(defthm
  Associates-pp-implies-iff-gcd-pp-3
  (implies (associates-pp g1 g2)
	   (iff (gcd-pp x y g1)
		(gcd-pp x y g2)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition divides-pp))
	   :use ((:instance
		  gcd-pp-necc
		  (d (gcd-pp-witness x y g2))
		  (g g1))
		 (:instance
		  gcd-pp-necc
		  (d (gcd-pp-witness x y g1))
		  (g g2))))))

(defthm
  Associates-pp-implies-equal-gcd-pp-3
  (implies (associates-pp g1 g2)
	   (equal (gcd-pp x y g1)
		  (gcd-pp x y g2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use (Associates-pp-implies-iff-gcd-pp-3
		 (:instance
		  (:theorem
		   (implies (and (booleanp x)
				 (booleanp y))
			    (equal (iff x y)
				   (equal x y))))
		  (x (gcd-pp x y g1))
		  (y (gcd-pp x y g2)))))))

(defthm
  Linear-combination-divides-pp-gcd
  (implies (gcd-pp x y g)
	   (divides-pp (++_e (**_e x
				   (mv-nth 0 (bezout x y)))
			     (**_e y
				   (mv-nth 1 (bezout x y))))
		       g))
  :hints (("goal"
	   :in-theory (disable  (:definition gcd-pp)
				(:definition bezout)
				(:definition divides-pp)
				gcd-pp-associates-pp)
	   :use (gcd-pp-mv-nth-bezout
		 (:instance
		  gcd-pp-associates-pp
		  (g1 (++_e (**_e x
				  (mv-nth 0 (bezout x y)))
			    (**_e y
				  (mv-nth 1 (bezout x y)))))
		  (g2 g))))))

(defthm
  Edp-divides-p-witness-linear-combination
  (implies (gcd-pp x y g)
	   (edp (divides-pp-witness (++_e (**_e x (mv-nth 0 (bezout x y)))
					  (**_e y (mv-nth 1 (bezout x y))))
				    g)))
  :hints (("goal"
	   :in-theory (disable (:definition bezout)
			       (:definition divides-pp)
			       (:definition mv-nth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unit-associates-p theory:

(defun-sk
  Unit-associates-p (x y)
  (exists u (if (and (edp x)
		     (edp y))
		(and (unit-p u)
		     (=_e (*_e u x)
			   y))
	        (equal x y))))

(defun-sk
  Unit-associates-p1 (x y)
  (exists u (if (and (edp x)
		     (edp y))
		(and (unit-p u)
		     (==_e (**_e u x)
			   y))
	        (equal x y))))

(defthm
  *_e-=-**_e
  (implies (and (edp x)
		(edp y))
	   (equal (*_e x y)(**_e x y)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable (:definition binary-**_e)))))

(defthm
  =_e-=-==_e
  (implies (and (edp x)
		(edp y))
	   (equal (=_e x y)(==_e x y)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable (:definition ==_e)))))

(defthm
  Unit-p-implies-edp
  (implies (unit-p x)
	   (edp x)))

(defthm
  Unit-associates-p-implies-unit-associates-p1
  (implies (unit-associates-p x y)
	   (unit-associates-p1 x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p)
			       (:definition unit-associates-p1))
	   :use ((:instance
		  unit-associates-p1-suff
		  (u (unit-associates-p-witness x y)))
		 (:instance
		  *_e-=-**_e
		  (x (unit-associates-p-witness x y))
		  (y x))
		 (:instance
		  =_e-=-==_e
		  (x (**_e (unit-associates-p-witness x y) x)))))))

(defthm
  Unit-associates-p1-implies-unit-associates-p
  (implies (unit-associates-p1 x y)
	   (unit-associates-p x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p)
			       (:definition unit-associates-p))
	   :use ((:instance
		  unit-associates-p-suff
		  (u (unit-associates-p1-witness x y)))
		 (:instance
		  *_e-=-**_e
		  (x (unit-associates-p1-witness x y))
		  (y x))
		 (:instance
		  =_e-=-==_e
		  (x (**_e (unit-associates-p1-witness x y) x)))))))

(defthm
  Unit-associates-p-iff-unit-associates-p1
  (iff (unit-associates-p x y)
       (unit-associates-p1 x y))
  :rule-classes nil
  :hints (("Goal"
	   :use (Unit-associates-p-implies-unit-associates-p1
		 Unit-associates-p1-implies-unit-associates-p))))

(defthm
  Booleanp-unit-associates-p
  (booleanp (unit-associates-p x y))
  :rule-classes :type-prescription)

(defthm
  Unit-associates-p-=-unit-associates-p1
  (equal (unit-associates-p x y)
	 (unit-associates-p1 x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-associates-p)
			       (:definition unit-associates-p1))
	   :use Unit-associates-p-iff-unit-associates-p1)))

(defun
  Unit-associates-pp-witness (x y)
  "Unit-associates-pp-witness nicely
   modifies unit-associates-p1-witness."
  (unit-associates-p1-witness (C_==_e x)
			      (C_==_e y)))

(defthm
  ==_e-implies-==_e-associates-pp-witness-1
  (implies (==_e x1 x2)
	   (==_e (Unit-associates-pp-witness x1 y)
		 (Unit-associates-pp-witness x2 y)))
  :rule-classes :congruence)

(defthm
  ==_e-implies-==_e-associates-pp-witness-2
  (implies (==_e y1 y2)
	   (==_e (Unit-associates-pp-witness x y1)
		 (Unit-associates-pp-witness x y2)))
  :rule-classes :congruence)

(defun
  Unit-associates-pp (x y)
  (let ((u (unit-associates-pp-witness x y)))
       (if (and (edp x)
		(edp y))
	   (and (unit-pp u)
		(==_e (**_e u x) y))
	   (equal x y))))

(defthm
  ==_e-=-equal
  (implies (not (edp y1))
	   (equal (==_e y1 y2)
		  (equal y1 y2)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable (:definition ==_e)))))

(defthm
  ==_e-implies-equal-unit-associates-pp-1
  (implies (==_e y1 y2)
	   (equal (unit-associates-pp y1 z)
		  (unit-associates-pp y2 z)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use ==_e-=-equal)))

(in-theory (disable (:definition divides-pp)))

(defthm
  ==_e-implies-equal-unit-associates-pp-2
  (implies (==_e y1 y2)
	   (equal (unit-associates-pp x y1)
		  (unit-associates-pp x y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use ==_e-=-equal)))

(defthm
  Unit-associates-pp-suff
  (implies (if (and (edp x)
		    (edp y))
	       (and (unit-pp u)
		    (==_e (**_e u x) y))
	       (equal x y))
	   (unit-associates-pp x y))
  :hints (("Goal"
	   :in-theory (disable unit-associates-p1-suff
			       (:definition unit-p)
			       (:definition unit-pp))
	   :use ((:instance
		  unit-associates-p1-suff
		  (x (C_==_e x))
		  (y (C_==_e y)))
		 (:instance
		  unit-p-=-unit-pp
		  (x u))
		 (:instance
		  unit-p-=-unit-pp
		  (x (unit-associates-p1-witness (c_==_e x)
						 (c_==_e y))))))))

(in-theory (disable (:definition unit-associates-pp-witness)
		    (:executable-counterpart unit-associates-pp)))

(defthm
  Unit-associates-p1-implies-unit-associates-pp
  (implies (unit-associates-p1 x y)
	   (unit-associates-pp x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p)
			       (:definition unit-pp))
	   :use ((:instance
		  Unit-associates-pp-suff
		  (u (unit-associates-p1-witness x y)))
		 (:instance
		  unit-p-=-unit-pp
		  (x (unit-associates-p1-witness x y)))))))

(defthm
  Unit-associates-pp-implies-unit-associates-p1
  (implies (unit-associates-pp x y)
	   (unit-associates-p1 x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p)
			       (:definition unit-pp))
	   :use ((:instance
		  Unit-associates-p1-suff
		  (u (unit-associates-pp-witness x y)))
		 (:instance
		  unit-p-=-unit-pp
		  (x (unit-associates-pp-witness x y)))))))

(defthm
  Unit-associates-p1-iff-unit-associates-pp
  (iff (unit-associates-p1 x y)
       (unit-associates-pp x y))
  :rule-classes nil
  :hints (("Goal"
	   :use (Unit-associates-p1-implies-unit-associates-pp
		 Unit-associates-pp-implies-unit-associates-p1))))

(defthm
  Unit-associates-p1-=-unit-associates-pp
  (equal (unit-associates-p1 x y)
	 (unit-associates-pp x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-associates-p1)
			       (:definition unit-associates-pp))
	   :use Unit-associates-p1-iff-unit-associates-pp)))

(defthm
  Unit-associates-p-=-unit-associates-pp
  (equal (unit-associates-p x y)
	 (unit-associates-pp x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-associates-p)
			       (:definition unit-associates-p1)
			       (:definition unit-associates-pp))
	   :use (Unit-associates-p-=-unit-associates-p1
		 Unit-associates-p1-=-unit-associates-pp))))

(defthm
  Reflexivity-unit-associates-pp
  (unit-associates-pp x x)
  :hints (("Goal"
	   :in-theory (disable (:definition unit-associates-pp))
	   :use (:instance
		 unit-associates-pp-suff
		 (u (1_e))
		 (y x)))))

(set-backchain-limit 1)

(defthm
  Symmetry-unit-associates-pp
  (implies (unit-associates-pp x y)
	   (unit-associates-pp y x))
  :hints (("Goal"
	   :in-theory (disable unit-pp-**_e-inverse
			       (:definition unit-pp))
	   :use ((:instance
		  unit-associates-pp-suff
		  (u (divides-pp-witness (unit-associates-pp-witness x y)
					 (1_e)))
		  (x y)
		  (y x))
		 (:instance
		  unit-pp-**_e-inverse
		  (u (unit-associates-pp-witness x y)))))
	  ("Subgoal 2"
	   :in-theory (enable (:definition unit-pp)))
	  ("Subgoal 1"
	   :in-theory (enable (:definition unit-pp)))))

(defthm
  Transitivity-unit-associates-pp
  (implies (and (unit-associates-pp x y)
		(unit-associates-pp y z))
	   (unit-associates-pp x z))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp)
			       commutativity-laws-for-++_e-&-**_e)
	   :use ((:instance
		  unit-associates-pp-suff
		  (u (**_e (unit-associates-pp-witness y z)
			   (unit-associates-pp-witness x y)))
		  (y z))))))

(set-backchain-limit nil)

(defthm
  Unit-associates-pp-is-an-equivalence
  (and (booleanp (unit-associates-pp x y))
       (unit-associates-pp x x)
       (implies (unit-associates-pp x y)
		(unit-associates-pp y x))
       (implies (and (unit-associates-pp x y)
		     (unit-associates-pp y z))
		(unit-associates-pp x z)))
  :rule-classes :equivalence
  :hints (("Goal"
	   :in-theory (disable (:definition unit-associates-pp)))))

(in-theory (disable Reflexivity-unit-associates-pp
		    Symmetry-unit-associates-pp
		    Transitivity-unit-associates-pp))

(defthm
  Associates-pp-implies-iff-edp
  (implies (associates-pp x y)
	   (iff (edp x)
		(edp y)))
  :rule-classes :congruence)

(set-backchain-limit 1)

(defthm
  Associates-pp-refines-unit-associates-pp-lemma-1
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(associates-pp x y))
	   (==_e (**_e (divides-pp-witness x y)
		       (divides-pp-witness y x))
		 (1_e)))
  :hints (("Goal"
	   :in-theory (e/d ((:definition divides-pp))
			   (divides-pp-implies-witness=qq_e
			    divides-pp-edp-divides-pp-witness))
	   :use ((:instance
		  projection-laws
		  (y (**_e (divides-pp-witness x y)
			   (divides-pp-witness y x))))))))

(set-backchain-limit 2)

(defthm
  Associates-pp-refines-unit-associates-pp-lemma-2
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(associates-pp x y))
	   (unit-pp (divides-pp-witness x y)))
  :hints (("Goal"
	   :in-theory (enable (:definition divides-pp))
	   :use
	   Associates-pp-refines-unit-associates-pp-lemma-1)))

(defthm
  Associates-pp-refines-unit-associates-pp-lemma-3
  (implies (and (edp x)
		(not (==_e x (0_e)))
		(associates-pp x y))
	   (unit-associates-pp x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (e/d ((:definition divides-pp))
			   ((:definition unit-pp)
			    divides-pp-implies-witness=qq_e
			    unit-associates-pp-suff))
	   :use (:instance
		 Unit-associates-pp-suff
		 (u (divides-pp-witness x y))))))

(defthm
  Associates-pp-refines-unit-associates-pp
  (implies (associates-pp x y)
	   (unit-associates-pp x y))
  :rule-classes :refinement
  :hints (("Goal"
	   :in-theory (e/d ((:definition divides-pp))
			   ((:definition unit-pp)
			    (:definition unit-associates-pp)))
	   :cases ((not (edp x))
		   (==_e x (0_e))))
	  ("Subgoal 3"
	   :use Associates-pp-refines-unit-associates-pp-lemma-3)
	  ("Subgoal 1"
	   :use (:instance
		 unit-associates-pp-suff
		 (u (1_e))))))

(defthm
  Unit-associates-pp-implies-iff-edp
  (implies (unit-associates-pp x y)
	   (iff (edp x)
		(edp y)))
  :rule-classes :congruence)

(defthm
  Unit-associates-pp-refines-associates-pp-lemma-1
  (implies (and (edp x)
		(unit-associates-pp x y))
	  (divides-pp x y))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp)
			       (:definition divides-pp)))))

(defthm
  Unit-associates-pp-refines-associates-pp
  (implies (unit-associates-pp x y)
	   (associates-pp x y))
  :rule-classes :refinement
  :hints (("Goal"
	   :cases ((edp x)))
	  ("Subgoal 1"
	   :in-theory (disable (:definition unit-associates-pp)))))

(defthm
  Unit-associates-pp-implies-reducible-pp-lemma-1
  (implies (and (not (edp (unit-associates-pp-witness x y)))
		(unit-associates-pp x y)
		(edp (mv-nth 0 (reducible-pp-witness x)))
		(edp (mv-nth 1 (reducible-pp-witness x)))
		(not (unit-pp (mv-nth 0 (reducible-pp-witness x))))
		(not (unit-pp (mv-nth 1 (reducible-pp-witness x))))
		(==_e (**_e (mv-nth 0 (reducible-pp-witness x))
			    (mv-nth 1 (reducible-pp-witness x)))
		      x))
	   (reducible-pp y))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp)
			       (:definition reducible-pp)))))

(defthm
  Unit-associates-pp-implies-reducible-pp-lemma-2
  (implies (and (not (==_e (**_e (unit-associates-pp-witness x y)
				 x)
			   y))
		(not (unit-pp (**_e (mv-nth 0 (reducible-pp-witness x))
				    (unit-associates-pp-witness x y))))
		(unit-associates-pp x y)
		(edp (mv-nth 0 (reducible-pp-witness x)))
		(edp (mv-nth 1 (reducible-pp-witness x)))
		(not (unit-pp (mv-nth 0 (reducible-pp-witness x))))
		(not (unit-pp (mv-nth 1 (reducible-pp-witness x))))
		(==_e (**_e (mv-nth 0 (reducible-pp-witness x))
			    (mv-nth 1 (reducible-pp-witness x)))
		      x))
	   (reducible-pp y))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp)
			       (:definition reducible-pp)))))

(defthm
  Unit-associates-pp-implies-reducible-pp-lemma-3
  (implies (and (not (==_e (**_e (**_e (unit-associates-pp-witness x y)
				       (mv-nth 0 (reducible-pp-witness x)))
				 (mv-nth 1 (reducible-pp-witness x)))
			   y))
		(==_e (**_e (mv-nth 0 (reducible-pp-witness x))
			    (mv-nth 1 (reducible-pp-witness x))
			    (unit-associates-pp-witness x y))
		      y)
		(not (unit-pp (**_e (mv-nth 0 (reducible-pp-witness x))
				    (unit-associates-pp-witness x y))))
		(unit-associates-pp x y)
		(edp (mv-nth 0 (reducible-pp-witness x)))
		(edp (mv-nth 1 (reducible-pp-witness x)))
		(not (unit-pp (mv-nth 0 (reducible-pp-witness x))))
		(not (unit-pp (mv-nth 1 (reducible-pp-witness x))))
		(==_e (**_e (mv-nth 0 (reducible-pp-witness x))
			    (mv-nth 1 (reducible-pp-witness x)))
		      x))
	   (reducible-pp y))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp)
			       (:definition reducible-pp)))))

(defthm
  Unit-associates-pp-implies-reducible-pp-lemma-4
  (implies (and (unit-pp (**_e (unit-associates-pp-witness x y)
			       (mv-nth 0 (reducible-pp-witness x))))
		(==_e (**_e (mv-nth 0 (reducible-pp-witness x))
			    (mv-nth 1 (reducible-pp-witness x))
			    (unit-associates-pp-witness x y))
		      y)
		(not (unit-pp (**_e (mv-nth 0 (reducible-pp-witness x))
				    (unit-associates-pp-witness x y))))
		(unit-associates-pp x y)
		(edp (mv-nth 0 (reducible-pp-witness x)))
		(edp (mv-nth 1 (reducible-pp-witness x)))
		(not (unit-pp (mv-nth 0 (reducible-pp-witness x))))
		(not (unit-pp (mv-nth 1 (reducible-pp-witness x))))
		(==_e (**_e (mv-nth 0 (reducible-pp-witness x))
			    (mv-nth 1 (reducible-pp-witness x)))
		      x))
	   (reducible-pp y))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp)
			       (:definition reducible-pp)))))

(defthm
  Unit-associates-pp-implies-reducible-pp-lemma-5
  (implies (and (not (edp (**_e (unit-associates-pp-witness x y)
				(mv-nth 0 (reducible-pp-witness x)))))
		(==_e (**_e (mv-nth 0 (reducible-pp-witness x))
			    (mv-nth 1 (reducible-pp-witness x))
			    (unit-associates-pp-witness x y))
		      y)
		(not (unit-pp (**_e (mv-nth 0 (reducible-pp-witness x))
				    (unit-associates-pp-witness x y))))
		(unit-associates-pp x y)
		(edp (mv-nth 0 (reducible-pp-witness x)))
		(edp (mv-nth 1 (reducible-pp-witness x)))
		(not (unit-pp (mv-nth 0 (reducible-pp-witness x))))
		(not (unit-pp (mv-nth 1 (reducible-pp-witness x))))
		(==_e (**_e (mv-nth 0 (reducible-pp-witness x))
			    (mv-nth 1 (reducible-pp-witness x)))
		      x))
	   (reducible-pp y))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp)
			       (:definition reducible-pp)))))

(defthm
  Unit-associates-pp-implies-reducible-pp
  (implies (and (unit-associates-pp x y)
		(reducible-pp x))
	   (reducible-pp y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition mv-nth)
			       (:definition unit-pp)
			       (:definition reducible-pp)
			       (:definition unit-associates-pp)
			       reducible-pp-edp
			       reducible-pp-suff)
	   :expand ((reducible-pp x))
	   :use ((:instance
		  reducible-pp-suff
		  (x y)
		  (y (**_e (unit-associates-pp-witness x y)
			   (mv-nth 0 (reducible-pp-witness x))))
		  (z (mv-nth 1 (reducible-pp-witness x))))
		 (:instance
		  (:theorem
		   (implies (and (edp a)
				 (edp b)
				 (edp c)
				 (==_e (**_e c x) y)
				 (==_e (**_e a b) x))
			    (==_e (**_e a b c) y)))
		  (a (mv-nth 0 (reducible-pp-witness x)))
		  (b (mv-nth 1 (reducible-pp-witness x)))
		  (c (unit-associates-pp-witness x y)))
		 (:instance
		  unit-pp-**_e=>unit-pp-factor-right
		  (x (unit-associates-pp-witness x y))
		  (y (mv-nth 0 (reducible-pp-witness x))))))))

(in-theory (disable Unit-associates-pp-implies-reducible-pp-lemma-1
		    Unit-associates-pp-implies-reducible-pp-lemma-2
		    Unit-associates-pp-implies-reducible-pp-lemma-3
		    Unit-associates-pp-implies-reducible-pp-lemma-4
		    Unit-associates-pp-implies-reducible-pp-lemma-5))

(defthm
  Unit-associates-pp-implies-equal-reducible-pp
  (implies (unit-associates-pp x y)
	   (equal (reducible-pp x)
		  (reducible-pp y)))
  :rule-classes :congruence
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-pp)
			       (:definition unit-associates-pp))
	   :use (unit-associates-pp-implies-reducible-pp
		 (:instance
		  Unit-associates-pp-implies-reducible-pp
		  (x y)
		  (y x))))))

(defthm
  Unit-associates-pp-implies-equal-irreducible-pp
  (implies (unit-associates-pp x y)
	   (equal (irreducible-pp x)
		  (irreducible-pp y)))
  :rule-classes :congruence
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-pp)
			       (:definition unit-associates-pp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unique factorization theory:

(defun
  Member-unit-associate (x lst)
  "Determine if an unit-associate-p
   of x is a member of lst."
  (cond ((atom lst)
	 nil)
	((unit-associates-p x (car lst))
	 lst)
	(t (member-unit-associate x (cdr lst)))))

(defun
  Member-unit-associate-pp (x lst)
  "Determine if an unit-associate-pp
   of x is a member of lst."
  (cond ((atom lst)
	 nil)
	((unit-associates-pp x (car lst))
	 lst)
	(t (member-unit-associate-pp x (cdr lst)))))

(in-theory (disable (:definition unit-associates-p)))
(in-theory (disable (:definition unit-associates-pp)))

(defthm
  Member-unit-associate-=-member-unit-associate-pp
  (equal (member-unit-associate x lst)
	(member-unit-associate-pp x lst))
  :rule-classes nil
  :hints (("Subgoal *1/3"
	   :use (:instance
		 Unit-associates-p-=-unit-associates-pp
		 (y (car lst))))
	  ("Subgoal *1/2"
	   :use (:instance
		 Unit-associates-p-=-unit-associates-pp
		 (y (car lst))))))

(defun
  Delete-one-unit-associate (x lst)
  "Return the result of deleting one occurrence
   of an unit-associate-p of x from the list lst."
  (if (consp lst)
      (if (unit-associates-p x (car lst))
	  (cdr lst)
	  (cons (car lst)(delete-one-unit-associate x (cdr lst))))
      lst))

(defun
  Delete-one-unit-associate-pp (x lst)
  "Return the result of deleting one occurrence
   of an unit-associate-pp of x from the list lst."
  (if (consp lst)
      (if (unit-associates-pp x (car lst))
	  (cdr lst)
	  (cons (car lst)(delete-one-unit-associate-pp x (cdr lst))))
      lst))

(defthm
  Delete-one-unit-associate-=-Delete-one-unit-associate-pp
  (equal (Delete-one-unit-associate x lst)
	 (Delete-one-unit-associate-pp x lst))
  :rule-classes nil
  :hints (("Subgoal *1/2"
	   :use (:instance
		 Unit-associates-p-=-unit-associates-pp
		 (y (car lst))))
	  ("Subgoal *1/1"
	   :use (:instance
		 Unit-associates-p-=-unit-associates-pp
		 (y (car lst))))))

(defun
  Bag-equal-unit-associates (lst1 lst2)
  "Return T iff lst1 and lst2 have the same
   members, up to unit-associates-p, with the
   same multiplicity, up to unit-associates-p."
  (if (consp lst1)
      (and (member-unit-associate (car lst1) lst2)
	   (bag-equal-unit-associates (cdr lst1)
				      (delete-one-unit-associate (car lst1)
								 lst2)))
      (atom lst2)))

(defun
  Bag-equal-unit-associates-pp (lst1 lst2)
  "Return T iff lst1 and lst2 have the same
   members, up to unit-associates-pp, with the
   same multiplicity, up to unit-associates-pp."
  (if (consp lst1)
      (and (member-unit-associate-pp (car lst1) lst2)
	   (bag-equal-unit-associates-pp (cdr lst1)
					 (delete-one-unit-associate-pp (car lst1)
								       lst2)))
      (atom lst2)))

(defthm
  Bag-equal-unit-associates-=-Bag-equal-unit-associates-pp
  (equal (Bag-equal-unit-associates lst1 lst2)
	 (Bag-equal-unit-associates-pp lst1 lst2))
  :rule-classes nil
  :hints (("Subgoal *1/2"
	   :use (:instance
		 Member-unit-associate-=-member-unit-associate-pp
		 (x (car lst1))
		 (lst lst2)))
	  ("Subgoal *1/1"
	   :use ((:instance
		  Member-unit-associate-=-member-unit-associate-pp
		  (x (car lst1))
		  (lst lst2))
		 (:instance
		  Delete-one-unit-associate-=-Delete-one-unit-associate-pp
		  (x (car lst1))
		  (lst lst2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Show that bag-equal-unit-associates has the expected properties:

;;  Lisp objects that are bag-equal-unit-associates have the same length.

;;  Lisp objects that are bag-equal-unit-associates have the same members,
;;   up to unit-associates-p

;;  Elements in Lisp objects that are bag-equal-unit-associates occur
;;  in each object with the same multiplicity, up to unit-associates-p.

(defthm
  Len-delete-one-unit-associate
  (implies (member-unit-associate x lst)
	   (equal (+ 1 (len (delete-one-unit-associate x lst)))
		  (len lst))))

(defthm
  Len-delete-one-unit-associate-pp
  (implies (member-unit-associate-pp x lst)
	   (equal (+ 1 (len (delete-one-unit-associate-pp x lst)))
		  (len lst))))

(defthm
  Bag-equal-unit-associates->equal-len
  (implies (bag-equal-unit-associates lst1 lst2)
	   (equal (len lst1)
		  (len lst2)))
  :rule-classes nil)

(defthm
  Bag-equal-unit-associates-pp->equal-len
  (implies (bag-equal-unit-associates-pp lst1 lst2)
	   (equal (len lst1)
		  (len lst2)))
  :rule-classes nil)

(defthm
  Member-unit-associate-pp-delete-one-unit-associate-pp
  (implies (not (unit-associates-pp x y))
	   (iff (member-unit-associate-pp x
					  (delete-one-unit-associate-pp y lst))
	        (member-unit-associate-pp x lst))))

(defthm
  Unit-associates-pp-member-unit-associate-pp
  (implies (and (unit-associates-pp x y)
		(member-unit-associate-pp y lst))
	   (member-unit-associate-pp x lst)))

(defthm
  Unit-associates-pp-implies-iff-member-unit-associate-pp
  (implies (unit-associates-pp x1 x2)
	   (iff (member-unit-associate-pp x1 lst)
		(member-unit-associate-pp x2 lst)))
  :rule-classes :congruence)

(in-theory (disable Unit-associates-pp-member-unit-associate-pp))

(defthm
  Bag-equal-unit-associates-pp->iff-member-unit-associate-pp
  (implies (bag-equal-unit-associates-pp lst1 lst2)
	   (iff (member-unit-associate-pp x lst1)
		(member-unit-associate-pp x lst2)))
  :rule-classes nil)

(defthm
  Bag-equal-unit-associates->iff-member-unit-associate
  (implies (bag-equal-unit-associates lst1 lst2)
	   (iff (member-unit-associate x lst1)
		(member-unit-associate x lst2)))
  :rule-classes nil
  :hints (("Goal"
	   :use (Bag-equal-unit-associates-pp->iff-member-unit-associate-pp
		 Bag-equal-unit-associates-=-Bag-equal-unit-associates-pp
		 (:instance
		  Member-unit-associate-=-member-unit-associate-pp
		  (lst lst1))
		 (:instance
		  Member-unit-associate-=-member-unit-associate-pp
		  (lst lst2))))))

(defun
  Multiplicity-unit-associate (x lst)
  (if (consp lst)
      (if (unit-associates-p x (car lst))
	  (+ 1 (multiplicity-unit-associate x (cdr lst)))
	  (multiplicity-unit-associate x (cdr lst)))
      0))

(defun
  Multiplicity-unit-associate-pp (x lst)
  (if (consp lst)
      (if (unit-associates-pp x (car lst))
	  (+ 1 (multiplicity-unit-associate-pp x (cdr lst)))
	  (multiplicity-unit-associate-pp x (cdr lst)))
      0))

(defthm
  Multiplicity-unit-associate-=-Multiplicity-unit-associate-pp
  (equal (Multiplicity-unit-associate x lst)
	 (Multiplicity-unit-associate-pp x lst))
  :rule-classes nil
  :hints (("Subgoal *1/2"
	   :use (:instance
		 Unit-associates-p-=-unit-associates-pp
		 (y (car lst))))
	  ("Subgoal *1/1"
	   :use (:instance
		 Unit-associates-p-=-unit-associates-pp
		 (y (car lst))))))

(defthm
  Multiplicity-unit-associate-pp-delete-one-unit-associate-pp-1
  (implies (and (member-unit-associate-pp y lst)
		(unit-associates-pp x y))
	   (equal (+ 1 (multiplicity-unit-associate-pp
			x
			(delete-one-unit-associate-pp y lst)))
		  (multiplicity-unit-associate-pp x lst))))

(defthm
  Multiplicity-unit-associate-pp-delete-one-unit-associate-pp-2
  (implies (not (unit-associates-pp x y))
	   (equal (multiplicity-unit-associate-pp
		   x
		   (delete-one-unit-associate-pp y lst))
		  (multiplicity-unit-associate-pp x lst))))

(defthm
  Bag-equal-unit-associates-pp->equal-multiplicity-unit-associate-pp
  (implies (bag-equal-unit-associates-pp lst1 lst2)
	   (equal (multiplicity-unit-associate-pp x lst1)
		  (multiplicity-unit-associate-pp x lst2)))
  :rule-classes nil)

(defthm
  Bag-equal-unit-associates->equal-multiplicity-unit-associate
  (implies (bag-equal-unit-associates lst1 lst2)
	   (equal (multiplicity-unit-associate x lst1)
		  (multiplicity-unit-associate x lst2)))
  :rule-classes nil
  :hints (("Goal"
	   :use (Bag-equal-unit-associates-pp->equal-multiplicity-unit-associate-pp
		 Bag-equal-unit-associates-=-Bag-equal-unit-associates-pp
		 (:instance
		  Multiplicity-unit-associate-=-Multiplicity-unit-associate-pp
		  (lst lst1))
		 (:instance
		  Multiplicity-unit-associate-=-Multiplicity-unit-associate-pp
		  (lst lst2))))))

(defthm
  Divides-pp-member-unit-associate-pp-**_e-lst
  (implies (and (edp-listp lst)
		(member-unit-associate-pp x lst))
	   (divides-pp x (**_e-lst lst)))
  :hints (("Goal"
	   :in-theory (disable (:definition divides-pp)
			       unit-associates-pp-refines-associates-pp-lemma-1
			       irreducible-listp-implies-edp-listp
			       irreducible-listp-1-implies-edp-listp))))

(defthm
  Divisors-of-irreducible-pp
  (implies (and (irreducible-pp x)
		(divides-pp d x))
	   (or (unit-associates-pp d x)
	       (unit-pp d)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (e/d ((:definition divides-pp))
			   ((:definition unit-pp)
			    (:definition reducible-pp)))
	   :use (:instance
		 unit-associates-pp-suff
		 (u (divides-pp-witness d x))
		 (x d)
		 (y x)))))

(defthm
  Gcd-pp-of-irreducible-pp
  (implies (and (irreducible-pp x)
		(gcd-pp x y g))
	   (or (unit-associates-pp g x)
	       (unit-pp g)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition irreducible-pp))
	   :use (:instance
		 Divisors-of-irreducible-pp
		 (d g)))))

(defthm
  Gcd-pp-of-irreducible-pp-divides-pp
  (implies (and (irreducible-pp x)
		(gcd-pp x y g))
	   (or (divides-pp x y)
	       (unit-pp g)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition irreducible-pp))
	   :use Gcd-pp-of-irreducible-pp)))

(defthm
  Unit-pp-Bezout
  (implies (and (edp x)
		(irreducible-pp x)
		(edp y)
		(not (divides-pp x y)))
	   (unit-pp (++_e (**_e x (first  (Bezout x y)))
			  (**_e y (second (Bezout x y))))))
  :hints (("Goal"
	   :use (gcd-pp-Bezout
		 (:instance
		  Gcd-pp-of-irreducible-pp-divides-pp
		  (g (++_e (**_e x (first  (Bezout x y)))
			   (**_e y (second (Bezout x y))))))))))

(defthm
  Associate-pp-unit-pp
  (implies (and (unit-pp x)
		(unit-pp y))
	   (equal (associates-pp x y) t)))

(defthm
  Irreducible-pp-gcd=1_e
  (implies (and (irreducible-pp x)
		(edp y)
		(not (divides-pp x y)))
	   (gcd-pp x y (1_e)))
  :hints (("Goal"
	   :in-theory (disable (:definition associates-pp)
			       (:definition bezout)
			       (:definition unit-pp)
			       (:definition gcd-pp)
			       unit-associates-pp-refines-associates-pp-lemma-1
			       Unit-pp-Bezout)
	   :use ((:instance
		  Associate-pp-unit-pp
		  (x (++_e (**_e x (first  (Bezout x y)))
			   (**_e y (second (Bezout x y)))))
		  (y (1_e)))
		 Unit-pp-Bezout))))

(defthm
  Edp-linear-combination
  (implies (gcd-pp x y g)
	   (edp (divides-pp-witness (++_e (**_e x (mv-nth 0 (bezout x y)))
					  (**_e y (mv-nth 1 (bezout x y))))
				    g)))
  :hints (("goal"
	   :in-theory (disable (:definition bezout)
			       (:definition mv-nth)))))

(in-theory (disable unit-associates-pp-refines-associates-pp-lemma-1))

(set-backchain-limit 3)

(defthm
  Prime-property-lemma
  (implies (and (gcd-pp x y (1_e))
		(divides-pp x (**_e y z))
		(edp z))
	   (divides-pp x z))
  :hints (("goal"
	   :in-theory (disable (:definition gcd-pp)
			       (:definition bezout)
			       (:definition mv-nth)
			       gcd=linear-combination)
	   :use ((:instance
		  (:theorem
		   (implies (==_e x y)
			    (==_e (**_e x z)
				  (**_e y z))))
		  (x (++_e (**_e x
				 (mv-nth 0 (bezout x y))
				 (divides-pp-witness
				  (++_e (**_e x (mv-nth 0 (bezout x y)))
					(**_e y (mv-nth 1 (bezout x y))))
				  (1_e)))
			   (**_e y
				 (mv-nth 1 (bezout x y))
				 (divides-pp-witness
				  (++_e (**_e x (mv-nth 0 (bezout x y)))
					(**_e y (mv-nth 1 (bezout x y))))
				  (1_e)))))
		  (y (1_e)))
		 (:instance
		  gcd=linear-combination
		  (g (1_e)))
		 (:instance
		  (:theorem
		   (implies (and (edp c)
				 (edp d)
				 (divides-pp x a)
				 (divides-pp x b))
			    (divides-pp x (++_e (**_e a c)
						(**_e b d)))))
		  (a x)
		  (b (**_e y z))
		  (c (**_e z
			   (mv-nth 0 (bezout x y))
			   (divides-pp-witness
			    (++_e (**_e x
					(mv-nth 0 (bezout x y)))
				  (**_e y
					(mv-nth 1 (bezout x y))))
			    (1_e))))
		  (d (**_e (mv-nth 1 (bezout x y))
			   (divides-pp-witness
			    (++_e (**_e x
					(mv-nth 0 (bezout x y)))
				  (**_e y (mv-nth 1 (bezout x y))))
			    (1_e)))))))))

(defthm
  Irreducible-pp-implies-prime-property
  (implies (and (irreducible-pp x)
		(edp y)
		(edp z)
		(divides-pp x (**_e y z)))
	   (or (divides-pp x y)
	       (divides-pp x z)))
  :rule-classes ((:rewrite
		  :corollary
		  (and (implies (and (irreducible-pp x)
				     (divides-pp x (**_e y z))
				     (edp y)
				     (edp z)
				     (not (divides-pp x y)))
				(divides-pp x z))
		       (implies (and (irreducible-pp x)
				     (divides-pp x (**_e y z))
				     (edp y)
				     (edp z)
				     (not (divides-pp x z)))
				(divides-pp x y)))))
  :hints (("Goal"
	   :in-theory (disable (:definition gcd-pp)
			       (:definition irreducible-pp)
			       Irreducible-pp-gcd=1_e)
	   :use Irreducible-pp-gcd=1_e)))

(defthm
  Irreducible-p-implies-prime-property
  (implies (and (irreducible-p x)
		(edp y)
		(edp z)
		(divides-p x (*_e y z)))
	   (or (divides-p x y)
	       (divides-p x z)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable Irreducible-pp-implies-prime-property
			       (:definition irreducible-pp)
			       (:definition irreducible-p)
			       (:definition divides-p))
	   :use (Irreducible-pp-implies-prime-property
		 Irreducible-p-=-irreducible-pp
		 Divides-p-=-Divides-pp
		 (:instance
		  Divides-p-=-Divides-pp
		  (y z))
		 (:instance
		  Divides-p-=-Divides-pp
		  (y (*_e y z)))
		 (:instance
		  *_e-=-**_e
		  (x y)
		  (y z))))))

(defthm
  Irreducible-pp-unit-associates
  (implies (and (divides-pp x y)
		(not (unit-pp x))
		(irreducible-pp y))
	   (equal (unit-associates-pp x y) t))
  :hints (("Goal"
	   :in-theory (e/d ((:definition divides-pp))
			   ((:definition irreducible-pp)
			    (:definition unit-pp)))
	   :use ((:instance
		  irreducible-pp-implies-unit-pp-factor
		  (x y)
		  (y x)
		  (z (divides-pp-witness x y)))
		 (:instance
		  unit-associates-pp-suff
		  (u (divides-pp-witness x y)))))))

(defthm
  Irreducible-p-unit-associates
  (implies (and (divides-p x y)
		(not (unit-p x))
		(irreducible-p y))
	   (unit-associates-p x y))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable Irreducible-pp-unit-associates
			       (:definition irreducible-pp)
			       (:definition irreducible-p)
			       (:definition unit-pp)
			       (:definition unit-p)
			       (:definition unit-associates-pp)
			       (:definition unit-associates-p))
	   :use (Irreducible-pp-unit-associates
		 Divides-p-=-Divides-pp
		 Unit-p-=-Unit-pp
		 (:instance
		  Irreducible-p-=-irreducible-pp
		  (x y))
		 Unit-associates-p-=-unit-associates-pp))))

(defthm
  Edp-Irreducible-pp
  (implies (irreducible-pp x)
	   (edp x))
  :rule-classes :forward-chaining)

(defthm
  Divides-pp-**_e-lst-implies-member-unit-associate-lemma
  (implies (and (irreducible-pp x)
		(not (unit-pp x))
		(edp-listp lst)
		(irreducible-listp-1 lst)
		(divides-pp x (**_e-lst lst)))
	   (member-unit-associate-pp x lst))
  :hints (("Goal"
	   :in-theory (disable irreducible-listp-implies-edp-listp
			       (:definition irreducible-pp)))))

(defthm
  Irreducible-pp-not-unit-pp
  (implies (irreducible-pp x)
	   (not (unit-pp x)))
  :rule-classes :forward-chaining)

(defthm
  Divides-pp-**_e-lst-implies-member-unit-associate-pp
  (implies (and (irreducible-pp x)
		(irreducible-listp-1 lst)
		(divides-pp x (**_e-lst lst)))
	   (member-unit-associate-pp x lst))
  :hints (("Goal"
	   :in-theory (disable (:definition irreducible-pp)))))

(defthm
  Edp-Unit-associates-pp-witness
  (implies (and (edp x)
		(unit-associates-pp x y))
	  (edp (unit-associates-pp-witness x y)))
  :hints (("Goal"
	   :in-theory (e/d ((:definition unit-associates-pp))
			   ((:definition unit-pp))))))

(defthm
  ==_e-**_e-Unit-associates-pp-witness
  (implies (and (edp x)
		(unit-associates-pp x y))
	   (==_e (**_e x (unit-associates-pp-witness x y)) y))
  :hints (("Goal"
	   :in-theory (e/d ((:definition unit-associates-pp))
			   ((:definition unit-pp))))))

(defthm
  ==_e-**_e-Unit-associates-pp-witness-1
  (implies (and (edp x)
		(unit-associates-pp (**_e x (**_e-lst lst1))
				    (**_e-lst lst2)))
	   (==_e (**_e x
		       (**_e-lst lst1)
		       (unit-associates-pp-witness (**_e x (**_e-lst lst1))
						   (**_e-lst lst2)))
		 (**_e-lst lst2)))
  :hints (("Goal"
	   :in-theory (disable ==_e-**_e-Unit-associates-pp-witness
			       (:definition unit-pp))
	   :use (:instance
		 ==_e-**_e-Unit-associates-pp-witness
		 (x (**_e x (**_e-lst lst1)))
		 (y (**_e-lst lst2))))))

(defthm
  **_e-irreducible-pp-**_e-lst-implies-member-unit-associate-pp-lemma
  (implies (and (unit-associates-pp (**_e x (**_e-lst lst1))
				    (**_e-lst lst2))
		(edp x))
	   (divides-pp x (**_e-lst lst2)))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp))
	   :use (:instance
		 divides-pp-suff
		 (y (**_e-lst lst2))
		 (z (**_e (unit-associates-pp-witness (**_e x (**_e-lst lst1))
						      (**_e-lst lst2))
			  (**_e-lst lst1)))))))

(defthm
  **_e-irreducible-pp-**_e-lst-implies-member-unit-associate-pp
  (implies (and (unit-associates-pp (**_e x (**_e-lst lst1))
				    (**_e-lst lst2))
		(irreducible-pp x)
		(irreducible-listp-1 lst2))
	   (member-unit-associate-pp x lst2))
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-pp)
			       (:definition unit-pp)))))

(defthm
  **_e-lst-of-irreducible-listp-1-not-unit-associate-pp-1_e
  (implies (and (irreducible-listp-1 lst)
		(consp lst))
	   (not (unit-associates-pp (1_e)(**_e-lst lst))))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-p)
			       (:definition reducible-pp)))))

(defthm
  Irreducible-listp-1-delete-one-unit-associate-pp
  (implies (and (member-unit-associate-pp x lst)
		(irreducible-listp-1 lst))
	   (irreducible-listp-1 (delete-one-unit-associate-pp x lst)))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp)
			       (:definition reducible-pp)))))

(defthm
  Unit-associates-pp-**_e-lst-implies-member-unit-associate-pp
  (implies (and (irreducible-pp x)
		(irreducible-listp-1 lst)
		(unit-associates-pp x (**_e-lst lst)))
	   (member-unit-associate-pp x lst))
  :hints (("goal"
	   :in-theory (disable (:definition reducible-pp)
			       (:definition unit-pp)))))

(set-backchain-limit 1)

(defthm
  Reducible-pp-**_e
  (implies (and (edp x)
		(reducible-pp y))
	   (reducible-pp (**_e x y)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (edp x)
				(reducible-pp y))
			   (and (reducible-pp (**_e x y))
				(reducible-pp (**_e y x))))
		  :hints (("Goal"
			   :in-theory (disable (:definition reducible-pp))))))
  :hints (("goal"
	   :in-theory (disable (:definition unit-pp)
			       (:definition mv-nth)
			       (:rewrite reducible-pp-suff))
	   :use ((:instance
		  reducible-pp-suff
		  (x (**_e x y))
		  (y (**_e x (mv-nth 0 (reducible-pp-witness y))))
		  (z (mv-nth 1 (reducible-pp-witness y))))
		 (:instance
		  unit-pp-**_e=>unit-pp-factor-right
		  (y (mv-nth 0 (reducible-pp-witness y))))))))

(defthm
  Reducible-pp-**_e-1
  (implies (and (edp x)
		(edp y)
		(not (unit-pp x))
		(not (unit-pp y)))
	   (reducible-pp (**_e x y)))
  :hints (("goal"
	   :in-theory (disable (:definition reducible-pp)
			       (:definition unit-pp))
	   :use (:instance
		 reducible-pp-suff
		 (x (**_e x y))
		 (y x)
		 (z y)))))

(defthm
  Reducible-pp-**_e-lst
  (implies (and (irreducible-listp-1 lst)
		(consp lst)
		(consp (cdr lst)))
	   (reducible-pp (**_e-lst lst)))
  :hints (("goal"
	   :in-theory (disable (:definition reducible-pp)
			       (:definition unit-pp)))))

(defthm
  Not-irreducible-pp-1_e
  (not (irreducible-pp (1_e))))

(defthm
  Irreducible-listp-1-irreducible-pp-member-unit-associate-pp
  (implies (and (member-unit-associate-pp x lst)
		(irreducible-listp-1 lst))
	   (irreducible-pp x))
  :hints (("Goal"
	   :in-theory (disable (:definition irreducible-pp)))))

(set-backchain-limit 3)

(defthm
  Unit-associates-pp-**_e-lst-implies-member-unit-associate-pp-1
  (implies (and (unit-associates-pp (**_e-lst lst1)
				    (**_e-lst lst2))
		(irreducible-listp-1 lst1)
		(irreducible-listp-1 lst2)
		(member-unit-associate-pp x lst1))
	   (member-unit-associate-pp x lst2))
  :hints (("Goal"
	   :in-theory (disable (:definition member-unit-associate-pp)))))

(defthm
  Member-unit-associate-pp-edp-listp-implies-edp
  (implies (and (member-unit-associate-pp x lst)
		(edp-listp lst))
	   (edp x)))

(defthm
  Unit-pp-unit-associates-pp-witness
  (implies (and (edp x)
		(unit-associates-pp x y))
	   (unit-pp (unit-associates-pp-witness x y)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (e/d ((:definition unit-associates-pp))
			   ((:definition unit-pp))))))

(defthm
  ==_e-**_e-Unit-associates-pp-witness-a
  (implies (and (edp x)
		(edp z)
		(unit-associates-pp x y))
	   (==_e (**_e x z (unit-associates-pp-witness x y))
		 (**_e y z)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable ==_e-**_e-Unit-associates-pp-witness
			       cancellation-laws-for-**_e
			       ==_e-implies-==_e-**_e-1)
	   :use (==_e-**_e-Unit-associates-pp-witness
		 (:instance
		  ==_e-implies-==_e-**_e-1
		  (y1 (**_e x (unit-associates-pp-witness x y)))
		  (y2 y))))))

(defthm
  Unit-associates-pp-**_e-1
  (implies (and (unit-associates-pp x y)
		(edp x)
		(edp z))
	   (unit-associates-pp (**_e x z)
			       (**_e y z)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp))
	   :use ((:instance
		  unit-associates-pp-suff
		  (x (**_e x z))
		  (y (**_e y z))
		  (u (unit-associates-pp-witness x y)))
		 Unit-pp-unit-associates-pp-witness
		 ==_e-**_e-Unit-associates-pp-witness-a))))

(defthm
  Unit-associates-pp-==_e-**_e-2
  (implies (and (unit-associates-pp x y)
		(edp x)
		(edp z))
	   (unit-associates-pp (**_e z x)
			       (**_e z y)))
  :rule-classes nil
  :hints (("Goal"
	   :use Unit-associates-pp-**_e-1)))

(defthm
  Unit-associates-pp-**_e-**_e-lst-delete-one-unit-associate-lemma
  (implies (and (unit-associates-pp
		 (**_e x (**_e-lst (delete-one-unit-associate-pp x (cdr lst))))
		 (**_e-lst (cdr lst)))
		(edp (car lst))
		(edp-listp (cdr lst))
		(member-unit-associate-pp x (cdr lst)))
	   (unit-associates-pp (**_e x
				     (car lst)
				     (**_e-lst
				      (delete-one-unit-associate-pp x
								    (cdr lst))))
			       (**_e (car lst) (**_e-lst (cdr lst)))))
 :hints (("goal"
	  :in-theory (disable (:definition unit-pp))
	  :use (:instance
		Unit-associates-pp-==_e-**_e-2
		(z (car lst))
		(x (**_e x (**_e-lst (delete-one-unit-associate-pp x (cdr lst)))))
		(y (**_e-lst (cdr lst)))))))

(defthm
  Unit-associates-pp-**_e-**_e-lst-delete-one-unit-associate
  (implies (and (edp-listp lst)
		(member-unit-associate-pp x lst))
	   (unit-associates-pp (**_e x (**_e-lst
					(delete-one-unit-associate-pp x
								      lst)))
			       (**_e-lst lst)))
  :hints (("Goal"
	   :in-theory (disable (:definition unit-pp)))
	  ("Subgoal *1/1"
	   :use (:instance
		 Unit-associates-pp-**_e-1
		 (z (**_e-lst (cdr lst)))
		 (y (car lst))))))

(defthm
  Unit-associates-pp-**_e-cancellation
  (implies (and (unit-associates-pp (**_e x y)
				    (**_e x z))
		(not (==_e x (0_e)))
		(edp x)
		(edp y)
		(edp z))
	   (unit-associates-pp y z))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (e/d ((:definition unit-associates-pp))
			   ((:definition unit-pp)))
	   :use (:instance
		 unit-associates-pp-suff
		 (x y)
		 (y z)
		 (u (unit-associates-pp-witness (**_e x y)
						(**_e x z)))))))

(defthm
  Unit-associates-pp-**_e-**_e-lst-delete-one-unit-associate-pp-cancellation
  (implies (and (unit-associates-pp (**_e x (**_e-lst lst1))
				    (**_e-lst lst2))
		(irreducible-pp x)
		(edp-listp lst1)
		(irreducible-listp-1 lst2))
	   (unit-associates-pp (**_e-lst (delete-one-unit-associate-pp x lst2))
			       (**_e-lst lst1)))
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-pp)
			       (:definition unit-pp))
	   :use (Irreducible-pp-not-0_e
		 (:instance
		  Unit-associates-pp-**_e-cancellation
		  (y (**_e-lst (delete-one-unit-associate-pp x lst2)))
		  (z (**_e-lst lst1)))))))

(defthm
  IRREDUCIBLE-FACTORIZATION-UNIQUENESS-general-1
  (implies (and (irreducible-listp-1 lst1)
		(irreducible-listp-1 lst2)
		(unit-associates-pp (**_e-lst lst1)
				    (**_e-lst lst2)))
	  (bag-equal-unit-associates-pp lst1 lst2))
  :hints (("Goal"
	   :in-theory (disable (:definition reducible-pp)
			       (:definition unit-pp)))))

(defthm
  Irreducible-listp-=-irreducible-listp-1
  (equal (irreducible-listp lst)
	 (irreducible-listp-1 lst))
  :rule-classes nil
  :hints (("Subgoal *1/2"
	   :in-theory (disable (:definition irreducible-pp)
			       (:definition irreducible-p))
	   :use (:instance
		 Irreducible-p-=-irreducible-pp
		 (x (car lst))))
	  ("Subgoal *1/1"
	   :in-theory (disable (:definition irreducible-pp)
			       (:definition irreducible-p))
	   :use (:instance
		 Irreducible-p-=-irreducible-pp
		 (x (car lst))))))

(defthm
  IRREDUCIBLE-FACTORIZATION-UNIQUENESS-general
  (implies (and (irreducible-listp lst1)
		(irreducible-listp lst2)
		(unit-associates-p (*_e-lst lst1)
				   (*_e-lst lst2)))
	  (bag-equal-unit-associates lst1 lst2))
  :hints (("Goal"
	   :use (IRREDUCIBLE-FACTORIZATION-UNIQUENESS-general-1
		 (:instance
		  Irreducible-listp-=-irreducible-listp-1
		  (lst lst1))
		 (:instance
		  Irreducible-listp-=-irreducible-listp-1
		  (lst lst2))
		 (:instance
		  *_e-lst-=-**_e-lst
		  (lst lst1))
		 (:instance
		  *_e-lst-=-**_e-lst
		  (lst lst2))
		 (:instance
		  unit-associates-p-=-unit-associates-pp
		  (x (*_e-lst lst1))
		  (y (*_e-lst lst2)))
		 bag-equal-unit-associates-=-bag-equal-unit-associates-pp))))

(defthm
  IRREDUCIBLE-FACTORIZATION-UNIQUENESS-1
  (implies (and (irreducible-listp-1 lst1)
		(irreducible-listp-1 lst2)
		(==_e (**_e-lst lst1)
		      (**_e-lst lst2)))
	  (bag-equal-unit-associates-pp lst1 lst2))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition irreducible-pp)))))

(defthm
  IRREDUCIBLE-FACTORIZATION-UNIQUENESS
  (implies (and (irreducible-listp lst1)
		(irreducible-listp lst2)
		(=_e (*_e-lst lst1)
		     (*_e-lst lst2)))
	  (bag-equal-unit-associates lst1 lst2))
  :rule-classes nil
  :hints (("Goal"
	   :use (IRREDUCIBLE-FACTORIZATION-UNIQUENESS-1
		 (:instance
		  Irreducible-listp-=-irreducible-listp-1
		  (lst lst1))
		 (:instance
		  Irreducible-listp-=-irreducible-listp-1
		  (lst lst2))
		 (:instance
		  *_e-lst-=-**_e-lst
		  (lst lst1))
		 (:instance
		  *_e-lst-=-**_e-lst
		  (lst lst2))
		 (:instance
		  =_e-=-==_e
		  (x (*_e-lst lst1))
		  (y (*_e-lst lst2)))
		 bag-equal-unit-associates-=-bag-equal-unit-associates-pp))))
