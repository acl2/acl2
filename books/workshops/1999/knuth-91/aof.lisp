; ACL2 Archimedean Ordered Field book.
; Copyright (C) 1999  John R. Cowles, University of Wyoming

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
To certify this book, first, create a world with the following packages:

(DEFPKG
  "ACL2-ASG"
  (UNION-EQ
   *ACL2-EXPORTS*
   *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*))

(DEFPKG
  "ACL2-AGP"
  (UNION-EQ *ACL2-EXPORTS*
	    *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*))

(DEFPKG
  "ACL2-CRG"
  (UNION-EQ
   *ACL2-EXPORTS*
   *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*))

(certify-book "aof" 3)
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; An ordered field is Archimedean if and only if each element of the field is
; less than some positive integer. This book contains a convenient ACL2
; axiomatization of such fields. ACL2 is able to verify that the axioms are
; consistent. The axioms permit the definition of a function, called
; Least-nat-bound, that returns the least nonnegative integer larger than its
; input.

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Make temporary use of an ACL2 Arithmetic Book to help certify this book,

(local
 (include-book "../../../arithmetic/inequalities"))

(local (include-book "cowles/acl2-crg" :dir :system))

; Note that the Abelian SemiGroup, Abelian Group, and Commutative Ring Books
;  are also temporarily available because they help certify the Arithmetic Book.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ; Signatures
 ((aofp (x) Boolean)
  (binary-+_a (x y) aofp)
  (unary--_a (x) aofp)
  (binary-*_a (x y) aofp)
  (unary-/_a (x) aofp)
  (<_a (x y) Boolean)
  (nat-int-bound (x) integerp))

 ; Witnesses:
 (local
  (defun
    aofp (x)
    (rationalp x)))

 (local
  (defun
    binary-+_a (x y)
    (+ x y)))

 (local
  (defun
    unary--_a (x)
    (- x)))

 (local
  (defun
    binary-*_a (x y)
    (* x y)))

 (local
  (defun
    unary-/_a (x)
    (/ x)))

 (local
  (defun
    <_a (x y)
    (< x y)))

 (local
  (defun
    nat-int-bound (x)
    (numerator x)))

 ; Convenient Notation:
 (defmacro
   +_a (&rest rst)
   (if rst
       (if (cdr rst)
	   (xxxjoin 'binary-+_a rst)
	   (list 'binary-+_a 0 (car rst)))
       0))

 (defmacro
   *_a (&rest rst)
   (if rst
       (if (cdr rst)
	   (xxxjoin 'binary-*_a rst)
	   (list 'binary-*_a 1 (car rst)))
       1))

 (defmacro
   /_a (x &optional (y 'nil binary-casep))
   (cond (binary-casep
	  (list 'binary-*_a x (list 'unary-/_a y)))
	 (t (list 'unary-/_a x))))

 (defmacro
   -_a (x &optional (y 'nil binary-casep))
   (if binary-casep
       (let ((y (if (and (consp y)
			 (eq (car y) 'quote)
			 (consp (cdr y))
			 (rationalp (cadr y))
			 (eq (cddr y) nil))
		    (cadr y)
		    y)))
	   (if (rationalp y)
	       (list 'binary-+_a
		     (unary-- y)
		     x)
	       (list 'binary-+_a
		     x
		     (list 'unary--_a
			   y))))
       (let ((x (if (and (consp x)
			 (eq (car x) 'quote)
			 (consp (cdr y))
			 (rationalp (cadr x))
			 (eq (cddr x) nil))
		    (cadr x)
		    x)))
	   (if (rationalp x)
	       (unary-- x)
	       (list 'unary--_a
		     x)))))

 (defmacro
   >_a (x y)
   (list '<_a y x))

 (defmacro
   >=_a (x y)
   (list 'not (list '<_a x y)))

 (defmacro
   <=_a (x y)
   (list 'not (list '<_a y x)))

 ; Axioms
 ;  Every Archimedian field contains the rationals:
 (defthm
   aofp-extends-rationalp
   (implies (rationalp x)
	    (aofp x)))

 (defthm
   Extension-Laws
   (implies (rationalp x)
	    (and (implies (rationalp y)
			  (and (equal (+_a x y)
				      (+ x y))
			       (equal (*_a x y)
				      (* x y))
			       (equal (<_a x y)
				      (< x y))))
		 (equal (-_a x)
			(- x))
		 (equal (/_a x)
			(/ x)))))

 ; Field axioms:
 (defthm
   Closure-Laws
   (implies (aofp x)
	    (and (implies (aofp y)
			  (and (aofp (+_a x y))
			       (aofp (*_a x y))))
		 (aofp (-_a x))
		 (aofp (/_a x)))))

 (defthm
   Commutativity-Laws
   (implies (and (aofp x)
		 (aofp y))
	    (and (equal (+_a x y)
			(+_a y x))
		 (equal (*_a x y)
			(*_a y x)))))

 (defthm
   Associativity-Laws
   (implies (and (aofp x)
		 (aofp y)
		 (aofp z))
	    (and (equal (+_a (+_a x y) z)
			(+_a x (+_a y z)))
		 (equal (*_a (*_a x y) z)
			(*_a x (*_a y z))))))

 (defthm
   Distributivity-Law
   (implies (and (aofp x)
		 (aofp y)
		 (aofp z))
	    (equal (*_a x (+_a y z))
		   (+_a (*_a x y)
			(*_a x z)))))

 (defthm
   Left-Unicity-Laws
   (implies (aofp x)
	    (and (equal (+_a 0 x)
			x)
		 (equal (*_a 1 x)
			x))))

 (defthm
   Right-Inverse-Laws
   (implies (aofp x)
	    (and (equal (+_a x (-_a x))
			0)
		 (implies (not (equal x 0))
			  (equal (*_a x (/_a x))
				 1)))))

 ; Order axioms:

 (defthm
   type-of-<_a
   (implies (and (aofp x)
		 (aofp y))
	    (booleanp (<_a x y)))
   :rule-classes ((:rewrite)
		  (:type-prescription
		   :corollary
		   (implies (and (aofp x)
				 (aofp y))
			    (or (equal (<_a x y) t)
				(equal (<_a x y) nil))))))

 (defthm
   <=_a-extends-<_a
   (implies (and (<_a x y)
		 (aofp x)
		 (aofp y))
	    (<=_a x y))
   :rule-classes (:rewrite :forward-chaining)
; Matt K. mod: :doc is no longer supported for defthm after v7-1
   ;; :doc "Equivalent to asymmetry of <_a."
   )

 (defthm
   Transitivity-of-<_a
   (implies (and (<_a x y)
		 (<_a y z)
		 (aofp x)
		 (aofp y)
		 (aofp z))
	    (<_a x z)))

 (defthm
   Antisymmetry-of-<=_a
   (implies (and (<=_a x y)
		 (<=_a y x)
		 (aofp x)
		 (aofp y))
	    (equal x y))
   :rule-classes :forward-chaining
; Matt K. mod: :doc is no longer supported for defthm after v7-1
   ;; :doc "Equivalent to trichotomy of <_a."
   )

 (defthm
   Compatibility-Laws
   ;Arithmetic library required for *_a.
   (implies (and (aofp x)
		 (aofp y)
		 (aofp z)
		 (<_a y z))
	    (and (<_a (+_a x y)
		      (+_a x z))
		 (implies (>_a x 0)
			  (<_a (*_a x y)
			       (*_a x z))))))

 ; Archimedean axioms
 (defthm
  Type-of-Nat-Int-Bound
  (implies (aofp x)
	   (integerp (nat-int-bound x)))
  :rule-classes :type-prescription)

 (defthm
   Nat-Int-Bound-is-a-bound
   ;Arithmetic library required.
   (implies (and (aofp x)
		 (>=_a  x 0))
	    (<=_a x (nat-int-bound x)))
   :hints (("Goal"
	    :use (:instance
		  (:theorem
		   (implies (and (rationalp x)
				 (> x 0)
				 (rationalp y)
				 (rationalp z)
				 (<= y z))
			    (<= (* x y)(* x z))))
		  (y 1)(z (denominator x))))))
 ) ; End encapsulate

(local ; change for v2-7
 (set-invisible-fns-table ((binary-+ unary-- unary--_a)
                           (binary-* unary-/ unary-/_a)
                           (unary-- unary-- unary--_a)
                           (unary-/ unary-/ unary-/_a)
                           (binary-+_a unary-- unary--_a)
                           (binary-*_a unary-/ unary-/_a)
                           (unary--_a unary-- unary--_a)
                           (unary-/_a unary-/ unary-/_a))))

;The next two Right Unicity theorems are needed
; for Knuth's generalized 91 function:

(defthm
  Right-Unicity-of-1
  (equal (* x 1)(fix x)))

(defthm
  Right-Unicity-Laws
  (implies (aofp x)
	   (and (equal (+_a x 0)
		       x)
		(equal (*_a x 1)
		       x))))

(defthm
  Commutativity-2-Laws
  (implies (and (aofp x)
		(aofp y)
		(aofp z))
	   (and (equal (+_a x y z)
		       (+_a y x z))
		(equal (*_a x y z)
		       (*_a y x z))))
  :hints (("Goal"
	   :use ((:functional-instance
                  acl2-asg::commutativity-2-of-op
                  (acl2-asg::equiv equal)
                  (acl2-asg::pred aofp)
                  (acl2-asg::op binary-+_a))
		 (:functional-instance
                  acl2-asg::commutativity-2-of-op
                  (acl2-asg::equiv equal)
                  (acl2-asg::pred aofp)
                  (acl2-asg::op binary-*_a))))))

(defthm
  Reverse-Extension-Laws
   (implies (rationalp x)
	    (and (implies (rationalp y)
			  (and (equal (+ x y)
				      (+_a x y))
			       (equal (* x y)
				      (*_a x y))
			       (equal (< x y)
				      (<_a x y))))
		 (equal (- x)
			(-_a x))
		 (equal (/ x)
			(/_a x)))))

(defthm
  Associate-constants-left
  (implies (and (rationalp x)
		(syntaxp (quotep x))
		(rationalp y)
		(syntaxp (quotep y))
		(aofp z))
	   (and (equal (+_a x y z)
		       (+_a (+ x y) z))
		(equal (*_a x y z)
		       (*_a (* x y) z))))
  :hints (("Goal"
	   :in-theory (disable Extension-Laws))))

(in-theory (disable Reverse-Extension-Laws))

; The following was formerly before Associate-constants-left, but starting with
; v2-7 we move it back to here (Matt K.) because otherwise it causes an error,
; since the current theory just before Associate-constants-left, violates the
; invariant.
(theory-invariant (incompatible (:rewrite Extension-Laws)
                                (:rewrite Reverse-Extension-Laws))
                  ;; Added for v2-7 by Matt K.
                  :key inv1)

;Both of the equalities in the next Nullity theorem
; are needed for Knuth's generalized 91 function:

(defthm
  Nullity-Laws
  (implies (aofp x)
	   (and (equal (*_a 0 x)
		       0)
		(equal (*_a x 0)
		       0)))
  :hints (("Goal"
	   :use (:functional-instance
                 acl2-crg::Left-nullity-of-zero-for-times
                 (acl2-crg::equiv equal)
                 (acl2-crg::pred aofp)
                 (acl2-crg::plus binary-+_a)
                 (acl2-crg::times binary-*_a)
                 (acl2-crg::minus unary--_a)
                 (acl2-crg::zero (lambda () 0))))))

(defthm
  Type-of-/_a
  (implies (and (aofp x)
		(not (equal x 0)))
	   (not (equal (/_a x) 0)))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :use (Right-Inverse-Laws
		 (:theorem
		  (implies (and (aofp x)
				(equal (/_a x) 0))
			   (equal (*_a x (/_a x))
				  0)))))))

(local
 (defthm
   Zero-Divisor-Law-Lemma-1
   (implies (and (aofp x)
		 (aofp y)
		 (aofp z)
		 (equal (*_a x y) 0))
	    (equal (*_a x y z)
		   0))
   :rule-classes nil
   :hints (("Goal"
	    :use (:theorem
		  (implies (and (aofp x)
				(aofp y)
				(aofp z)
				(equal (*_a x y) 0))
			   (equal (*_a (*_a x y) z)
				  0))))
	   ("Subgoal 2"
	    :use associativity-Laws))))

(local
 (defthm
   Zero-Divisor-Law-Lemma-2
   (implies (and (aofp x)
		 (aofp y)
		 (equal (*_a x y) 0)
		 (not (equal y 0)))
	    (equal x 0))
   :rule-classes nil
   :hints (("Goal"
	    :use (:instance
		  Zero-Divisor-Law-Lemma-1
		  (z (/_a y)))))))

(defthm
  Zero-Divisor-Law
  (implies (and (aofp x)
		(aofp y))
	   (equal (equal (*_a x y) 0)
		  (or (equal x 0)
		      (equal y 0))))
  :hints (("Goal"
	   :use Zero-Divisor-Law-Lemma-2)))

(defthm
  Involution-Laws
  (implies (aofp x)
	   (and (equal (-_a (-_a x))
		       x)
		(implies (not (equal x 0))
			 (equal (/_a (/_a x))
				x))))
  :hints (("Goal"
	   :use ((:functional-instance
                  acl2-agp::Involution-of-inv
                  (acl2-agp::equiv equal)
                  (acl2-agp::pred aofp)
                  (acl2-agp::op binary-+_a)
                  (acl2-agp::id (lambda () 0))
                  (acl2-agp::inv unary--_a))
		 (:functional-instance
                  acl2-agp::Involution-of-inv
                  (acl2-agp::equiv equal)
                  (acl2-agp::pred (lambda (x)
                                    (and (aofp x)
                                         (not (equal x 0)))))
                  (acl2-agp::op binary-*_a)
                  (acl2-agp::id (lambda () 1))
                  (acl2-agp::inv unary-/_a))))))

(defthm
  Inverse-Distributive-Laws
  (implies (and (aofp x)
		(aofp y))
	   (and (equal (-_a (+_a x y))
		       (+_a (-_a x)(-_a y)))
		(implies (and (not (equal x 0))
			      (not (equal y 0)))
			 (equal (/_a (*_a x y))
				(*_a (/_a x)(/_a y))))))
  :hints (("Goal"
	   :use ((:functional-instance
                  acl2-agp::Distributivity-of-inv-over-op
                  (acl2-agp::equiv equal)
                  (acl2-agp::pred aofp)
                  (acl2-agp::op binary-+_a)
                  (acl2-agp::id (lambda () 0))
                  (acl2-agp::inv unary--_a))
		 (:functional-instance
                  acl2-agp::Distributivity-of-inv-over-op
                  (acl2-agp::equiv equal)
                  (acl2-agp::pred (lambda (x)
                                    (and (aofp x)
                                         (not (equal x 0)))))
                  (acl2-agp::op binary-*_a)
                  (acl2-agp::id (lambda () 1))
                  (acl2-agp::inv unary-/_a))))))

(defthm
  Inverse-Cancellation-Laws
  (implies (and (aofp x)
		(aofp y))
	   (and (equal (+_a x y (-_a x))
		       y)
		(equal (+_a x (-_a x) y)
		       y)
		(implies (not (equal x 0))
          			 (and (equal (*_a x y (/_a x))
				     y)
			      (equal (*_a x (/_a x) y)
				     y)))))
  :hints (("Goal"
	   :use ((:functional-instance
                  acl2-agp::inv-cancellation-on-right
                  (acl2-agp::equiv equal)
                  (acl2-agp::pred aofp)
                  (acl2-agp::op binary-+_a)
                  (acl2-agp::id (lambda () 0))
                  (acl2-agp::inv unary--_a))
		 (:functional-instance
                  acl2-agp::inv-cancellation-on-right
                  (acl2-agp::equiv equal)
                  (acl2-agp::pred (lambda (x)
                                    (and (aofp x)
                                         (not (equal x 0)))))
                  (acl2-agp::op binary-*_a)
                  (acl2-agp::id (lambda () 1))
                  (acl2-agp::inv unary-/_a))))))

(defthm
  Cancellation-Laws
  (implies (and (aofp x)
		(aofp y)
		(aofp z))
	   (and (equal (equal (+_a x z)(+_a y z))
		       (equal x y))
		(equal (equal (+_a z x)(+_a z y))
		       (equal x y))
		(equal (equal (+_a z x)(+_a y z))
		       (equal x y))
		(equal (equal (+_a x z)(+_a z y))
		       (equal x y))
		(equal (equal (*_a x z)(*_a y z))
		       (or (equal z 0)
			   (equal x y)))
		(equal (equal (*_a x z)(*_a z y))
		       (or (equal z 0)
			   (equal x y)))
		(equal (equal (*_a z x)(*_a y z))
		       (or (equal z 0)
			   (equal x y)))
		(equal (equal (*_a z x)(*_a z y))
		       (or (equal z 0)
			   (equal x y)))))
  :hints (("Goal"
	   :use ((:functional-instance
                  acl2-agp::Right-cancellation-for-op
                  (acl2-agp::equiv equal)
                  (acl2-agp::pred aofp)
                  (acl2-agp::op binary-+_a)
                  (acl2-agp::id (lambda () 0))
                  (acl2-agp::inv unary--_a))
		 (:functional-instance
                  acl2-agp::Right-cancellation-for-op
                  (acl2-agp::equiv equal)
                  (acl2-agp::pred (lambda (x)
                                    (and (aofp x)
                                         (not (equal x 0)))))
                  (acl2-agp::op binary-*_a)
                  (acl2-agp::id (lambda () 1))
                  (acl2-agp::inv unary-/_a))))))

(defthm
  Equal_-_a-zero
  (implies (aofp x)
	   (equal (equal 0 (-_a x))
		  (equal 0 x)))
  :hints (("Goal"
	   :in-theory (disable involution-laws)
	   :use (involution-laws
		 (:instance
		  (:theorem
		   (implies (equal x y)
			    (equal (-_a x)(-_a y))))
		  (x 0)(y (-_a x)))))))

(defthm
  Equal-Inverses-Laws
  (implies (and (aofp x)
		(aofp y))
	   (and (equal (equal (-_a x)(-_a y))
		       (equal x y))
		(implies (and (not (equal x 0))
			      (not (equal y 0)))
			 (equal (equal (/_a x)(/_a y))
				(equal x y)))))
  :hints (("Goal"
	   :in-theory (disable Involution-Laws)
	   :use (Involution-laws
		 (:instance
		  involution-Laws
		  (x y))
		 (:instance
		  (:theorem
		   (implies (equal x y)
			    (equal (-_a x)(-_a y))))
		  (x (-_a x))(y (-_a y)))
		 (:instance
		  (:theorem
		   (implies (equal x y)
			    (equal (/_a x)(/_a y))))
		  (x (/_a x))(y (/_a y)))))))

(defthm
  Idempotent-Law
  (implies (aofp x)
	   (equal (equal (+_a x x) x)
		  (equal x 0)))
  :hints (("Goal"
	   :use ((:functional-instance
                  acl2-agp::Uniqueness-of-id-as-op-idempotent
                  (acl2-agp::equiv equal)
                  (acl2-agp::pred aofp)
                  (acl2-agp::op binary-+_a)
                  (acl2-agp::id (lambda () 0))
                  (acl2-agp::inv unary--_a))))))

(defthm
  Projection-Laws
  (implies (and (aofp x)
		(aofp y))
	   (and (equal (equal (*_a x y) x)
		       (or (equal x 0)
			   (equal y 1)))
		(equal (equal (*_a y x) x)
		       (or (equal x 0)
			   (equal y 1)))))
  :hints (("Goal"
	   :in-theory (disable Cancellation-Laws)
	   :use (:instance
		 Cancellation-Laws
		 (z x)(x y)(y 1)))))

(defthm
  Unique-Inverse-Laws
  (implies (and (aofp x)
		(aofp y))
	   (equal (equal (*_a x y) 1)
		  (and (not (equal x 0))
		       (equal y (/_a x)))))
  :hints (("Goal"
	   :use ((:functional-instance
                  acl2-agp::Uniqueness-of-op-inverses
                  (acl2-agp::equiv equal)
                  (acl2-agp::pred (lambda (x)
                                    (and (aofp x)
                                         (not (equal x 0)))))
                  (acl2-agp::op binary-*_a)
                  (acl2-agp::id (lambda () 1))
                  (acl2-agp::inv unary-/_a))))))

(defthm
  Functional-Commutativity-Laws-1
  (implies (and (aofp x)
		(aofp y))
	   (and (equal (*_a x (-_a y))
		       (-_a (*_a x y)))
		(equal (*_a (-_a y) x)
		       (-_a (*_a y x)))))
  :hints (("Goal"
	   :use ((:functional-instance
                  acl2-crg::functional-commutativity-of-minus-times-right
                  (acl2-crg::equiv equal)
                  (acl2-crg::pred aofp)
                  (acl2-crg::plus binary-+_a)
                  (acl2-crg::times binary-*_a)
                  (acl2-crg::zero (lambda () 0))
                  (acl2-crg::minus unary--_a))))))

(local
 (defthm
   Functional-Commutativity-Law-2-lemma
   (implies (and (aofp x)
		 (not (equal x 0)))
	    (equal (*_a (-_a x)(-_a (/_a x)))
		   1))
   :rule-classes nil))

(defthm
  Functional-Commutativity-Law-2
  (implies (and (aofp x)
		(not (equal x 0)))
	   (equal (/_a (-_a x))
		  (-_a (/_a x))))
  :hints (("Goal"
	   :in-theory (disable Functional-Commutativity-Laws-1)
	   :use Functional-Commutativity-Law-2-lemma)))

(defthm
  Converse-Unique-Inverse-Laws
  (implies (and (aofp x)
		(aofp y)
		(not (equal x 0)))
	   (equal (equal (/_a x) y)
		  (equal 1 (*_a x y)))))

(in-theory (disable Unique-Inverse-Laws))

(theory-invariant (incompatible (:rewrite Unique-Inverse-Laws)
                                (:rewrite Converse-Unique-Inverse-Laws))
                  ;; Added for v2-7 by Matt K.
                  :key inv2)

(defthm
  Reflexivity-of-<=_a
  (implies (aofp x)
	   (<=_a x x))
; Matt K. mod: :doc is no longer supported for defthm after v7-1
  ;; :doc "Equivalent to irreflexivity of <_a."
  )

(defthm
  Transitivity-of-<=_a
  (implies (and (<=_a x y)
		(<=_a y z)
		(aofp x)
		(aofp y)
		(aofp z))
	   (<=_a x z))
  :hints (("Goal"
	   :use Antisymmetry-of-<=_a)))

(defthm
  Pos-not-zero
  (implies (and (>_a x 0)
		(aofp x))
	   (not (equal x 0)))
  :rule-classes :forward-chaining)

(defthm
  Neg-not-zero
  (implies (and (<_a x 0)
		(aofp x))
	   (not (equal x 0)))
  :rule-classes :forward-chaining)

(defthm
  Pos-Reciprocal-1
  (implies (and (aofp x)
		(>_a x 0))
	   (>_a (/_a x) 0))
  :hints (("Goal"
	   :use ((:instance
		  Antisymmetry-of-<=_a
		  (x (/_a x))(y 0))
		 (:instance
		  Compatibility-Laws
		  (y (/_a x))(z 0))))))

(local
 (defthm
   Pos-Reciprocal-lemma
   (implies (and (aofp x)
		 (not (equal x 0))
		 (>_a (/_a x) 0))
	    (>_a x 0))
   :hints (("Goal"
	    :use ((:instance
		   Pos-Reciprocal-1
		   (x (/_a x))))))))

(local
 (defthm
   iff-equal
   (implies (and (iff x y)
                 (booleanp x)
                 (booleanp y))
            (equal x y))
   :rule-classes nil))

(defthm
  Pos-Reciprocal-2
  (implies (and (aofp x)
		(not (equal x 0)))
	   (equal (>_a (/_a x) 0)
		  (>_a x 0)))
  :hints (("Goal"
	   :use (:instance
		 iff-equal
		 (x (>_a (/_a x) 0))
		 (y (>_a x 0))))))

(defthm
  Neg-Reciprocal-1
  (implies (and (aofp x)
		(<_a x 0))
	   (<_a (/_a x) 0))
  :hints (("Goal"
	   :use ((:instance
		  Antisymmetry-of-<=_a
		  (x (/_a x))
		  (y 0))))))

(local
 (defthm
   Neg-Reciprocal-lemma
   (implies (and (aofp x)
		 (not (equal x 0))
		 (<_a (/_a x) 0))
	    (<_a x 0))
   :hints (("Goal"
	    :use ((:instance
		   Neg-Reciprocal-1
		   (x (/_a x))))))))

(defthm
  Neg-Reciprocal-2
  (implies (and (aofp x)
		(not (equal x 0)))
	   (equal (<_a (/_a x) 0)
		  (<_a x 0)))
  :hints (("Goal"
	   :use (:instance
		 iff-equal
		 (x (<_a (/_a x) 0))
		 (y (<_a x 0))))))

(local
 (defthm
   <_a-Cancellation-Laws-for-+_a-lemma
   (implies (and (<_a (+_a x y)(+_a x z))
		 (aofp x)
		 (aofp y)
		 (aofp z))
	    (<_a y z))
   :hints (("Goal"
	    :use (:instance
		  Compatibility-laws
		  (x (-_a x))
		  (y (+_a x y))
		  (z (+_a x z)))))))

(defthm
  <_a-Cancellation-Laws-for-+_a
  (implies (and (aofp x)
		(aofp y)
		(aofp z))
	   (and (equal (<_a (+_a x y)(+_a x z))
		       (<_a y z))
		(equal (<_a (+_a x y)(+_a z x))
		       (<_a y z))
		(equal (<_a (+_a y x)(+_a x z))
		       (<_a y z))
		(equal (<_a (+_a y x)(+_a z x))
		       (<_a y z))))
  :hints (("Goal"
	   :use (:instance
		 iff-equal
		 (x (<_a (+_a x y)(+_a x z)))
		 (y (<_a y z))))))

(local
 (defthm
   -_a-inverts-<_a-lemma-1
   (implies (and (aofp x)
		 (aofp y)
		 (<_a x y))
	    (>_a (-_a x)(-_a y)))
   :hints (("Goal"
	    :use (:instance
		  Compatibility-laws
		  (x (+_a (-_a x)(-_a y)))
		  (y x)(z y))))))

(local
 (defthm
   -_a-inverts-<_a-lemma-2
   (implies (and (aofp x)
		 (aofp y)
		 (<_a (-_a x)(-_a y)))
	    (>_a x y))
   :hints (("Goal"
	    :use (:instance
		  -_a-inverts-<_a-lemma-1
		  (x (-_a x))(y (-_a y)))))))

(defthm
  -_a-inverts-<_a
  (implies (and (aofp x)
		(aofp y))
	   (equal (<_a (-_a x)(-_a y))
		  (>_a x y)))
  :hints (("Goal"
	   :use (:instance
		 iff-equal
		 (x (<_a (-_a x)(-_a y)))
		 (y (>_a x y))))))

(defthm
  Neg-minus-pos
  (implies (aofp x)
	   (equal (<_a (-_a x) 0)
		  (>_a x 0)))
  :hints (("Goal"
	   :use (:instance
		 -_a-inverts-<_a
		 (y 0)))))

(defthm
  Pos-minus-neg
  (implies (aofp x)
	   (equal (>_a (-_a x) 0)
		  (<_a x 0)))
  :hints (("Goal"
	   :use (:instance
		 -_a-inverts-<_a
		 (x 0)(y x)))))

(local
 (in-theory (disable pos-reciprocal-lemma
		     neg-reciprocal-lemma
		     -_a-inverts-<_a-lemma-2)))

(local
 (defthm
   <_a-Cancellation-Laws-for-*_a-lemma-1
   (implies (and (<_a (*_a x y)(*_a x z))
		 (aofp x)
		 (aofp y)
		 (aofp z)
		 (>_a x 0))
	    (<_a y z))
   :hints (("Goal"
	    :use (:instance
		  Compatibility-Laws
		  (x (/_a x))
		  (y (*_a x y))
		  (z (*_a x z)))))))

(local
 (defthm
   <_a-Cancellation-Laws-for-*_a-lemma-2
   (implies (and (aofp x)
		 (aofp y)
		 (aofp z)
		 (<_a x 0)
		 (>_a y z))
	    (<_a (*_a x y)(*_a x z)))
   :hints (("Goal"
	    :use (:instance
		  Compatibility-Laws
		  (x (-_a x))
		  (y z)
		  (z y))))))

(local
 (defthm
   <_a-Cancellation-Laws-for-*_a-lemma-3
   (implies (and (<_a (*_a x y)(*_a x z))
		 (aofp x)
		 (aofp y)
		 (aofp z)
		 (<_a x 0))
	    (>_a y z))
   :hints (("Goal"
	    :use (:instance
		  <_a-Cancellation-Laws-for-*_a-lemma-2
		  (x (/_a x))
		  (y (*_a x z))
		  (z (*_a x y)))))))

(defthm
  <_a-Cancellation-Laws-for-*_a
  (implies (and (aofp x)
		(aofp y)
		(aofp z))
	   (and (equal (<_a (*_a x y)(*_a x z))
		       (cond ((>_a x 0)
			      (<_a y z))
			     ((<_a x 0)
			      (>_a y z))
			     (t nil)))
		(equal (<_a (*_a x y)(*_a z x))
		       (cond ((>_a x 0)
			      (<_a y z))
			     ((<_a x 0)
			      (>_a y z))
			     (t nil)))
		(equal (<_a (*_a y x)(*_a x z))
		       (cond ((>_a x 0)
			      (<_a y z))
			     ((<_a x 0)
			      (>_a y z))
			     (t nil)))
		(equal (<_a (*_a y x)(*_a z x))
		       (cond ((>_a x 0)
			      (<_a y z))
			     ((<_a x 0)
			      (>_a y z))
			     (t nil)))))
  :hints (("Goal"
	   :use ((:instance
		  antisymmetry-of-<=_a
		  (y 0))
		 (:instance
		  iff-equal
		  (x (<_a (*_a x y)(*_a x z)))
		  (y (cond ((>_a x 0)
			    (<_a y z))
			   ((<_a x 0)
			    (>_a y z))
			   (t nil))))))))

(defthm
  Non-pos-Non-neg-Equal
  (implies (and (<=_a x 0)
		(>=_a x 0)
		(aofp x))
	   (equal x 0))
  :rule-classes :forward-chaining
  :hints (("Goal"
	   :use (:instance
		 antisymmetry-of-<=_a
		 (y 0)))))

(defthm
  Positive-*_a
  (implies (and (aofp x)
		(aofp y))
	   (equal (>_a (*_a x y) 0)
		  (and (not (equal x 0))
		       (not (equal y 0))
		       (iff (>_a x 0)
			    (>_a y 0)))))
  :hints (("Goal"
	   :use ((:instance
		  <_a-Cancellation-Laws-for-*_a
		  (y 0)(z y))
		 (:instance
		  iff-equal
		  (x (>_a (*_a x y) 0))
		  (y (and (not (equal x 0))
			  (not (equal y 0))
			  (iff (>_a x 0)
			       (>_a y 0)))))))))

(defthm
  Negative-*_a
  (implies (and (aofp x)
		(aofp y))
	   (equal (<_a (*_a x y) 0)
		  (and (not (equal x 0))
		       (not (equal y 0))
		       (iff (<_a x 0)
			    (>_a y 0)))))
  :hints (("Goal"
	   :use ((:instance
		  <_a-Cancellation-Laws-for-*_a
		  (z 0))
		 (:instance
		  iff-equal
		  (x (<_a (*_a x y) 0))
		  (y (and (not (equal x 0))
			  (not (equal y 0))
			  (iff (<_a x 0)
			       (>_a y 0)))))))))

(local
 (in-theory (disable
	     (:REWRITE <_A-CANCELLATION-LAWS-FOR-+_A-LEMMA))))

(local
 (defthm
   +_a-Compatibility-of-<=_a-lemma
   (implies (and (aofp x1)
		 (aofp y1)
		 (aofp y2)
		 (<=_a y1 y2))
	    (<=_a (+_a x1 y1)(+_a x1 y2)))
   :rule-classes nil))

(defthm
  +_a-Compatibility-of-<=_a
  (implies (and (aofp x1)
		(aofp x2)
		(aofp y1)
		(aofp y2)
		(<=_a x1 x2)
		(<=_a y1 y2))
	   (<=_a (+_a x1 y1)(+_a x2 y2)))
  :hints (("Goal"
	   :in-theory (disable <_A-CANCELLATION-LAWS-FOR-+_A)
	   :use (+_a-Compatibility-of-<=_a-lemma
		 (:instance
		  +_a-Compatibility-of-<=_a-lemma
		  (x1 y2)(y1 x1)(y2 x2))))))

(defthm
  <_a-+_a--_a-1
  (implies (and (aofp x)
		(aofp y)
		(aofp z))
	   (equal (<_a x (-_a y z))
		  (<_a (+_a x z) y)))
  :hints (("Goal"
	   :use (:instance
		 <_a-cancellation-laws-for-+_a
		 (x (-_a z))(y (+_a x z))(z y)))))

(defthm
  <_a-+_a--_a-2
  (implies (and (aofp x)
		(aofp y)
		(aofp z))
	   (equal (<_a x (+_a (-_a z) y))
		  (<_a (+_a x z) y))))

(defthm
  <_a-*_a-/_a-1
  (implies (and (aofp x)
		(aofp y)
		(aofp z)
		(>_a z 0))
	   (equal (<_a x (/_a y z))
		  (<_a (*_a x z) y)))
  :hints (("Goal"
	   :use (:instance
		 <_a-cancellation-laws-for-*_a
		 (x (/_a z))(y (*_a x z))(z y)))))

(defthm
  <_a-*_a-/_a-2
  (implies (and (aofp x)
		(aofp y)
		(aofp z)
		(>_a z 0))
	   (equal (<_a x (*_a (/_a z) y))
		  (<_a (*_a x z) y))))

(defthm
  +_a--_a-<_a-1
  (implies (and (aofp x)
		(aofp y)
		(aofp z))
	   (equal (<_a (-_a y z) x)
		  (<_a y (+_a x z))))
  :hints (("Goal"
	   :use (:instance
		 <_a-cancellation-laws-for-+_a
		 (x (-_a z))(z (+_a x z))))))

(defthm
  +_a--_a-<_a-2
  (implies (and (aofp x)
		(aofp y)
		(aofp z))
	   (equal (<_a (+_a (-_a z) y) x)
		  (<_a y (+_a x z)))))

(defthm
  *_a-/_a-<_a-1
  (implies (and (aofp x)
		(aofp y)
		(aofp z)
		(>_a z 0))
	   (equal (<_a (/_a y z) x)
		  (<_a y (*_a x z))))
  :hints (("Goal"
	   :use (:instance
		 <_a-cancellation-laws-for-*_a
		 (x (/_a z))(z (*_a x z))))))

(defthm
  *_a-/_a-<_a-2
  (implies (and (aofp x)
		(aofp y)
		(aofp z)
		(>_a z 0))
	   (equal (<_a (*_a (/_a z) y) x)
		  (<_a y (*_a x z)))))

(defthm
  Pos-difference-1
  (implies (and (aofp x)
		(aofp y))
	   (equal (>_a (-_a x y) 0)
		  (>_a x y))))

(defthm
  Neg-difference-1
  (implies (and (aofp x)
		(aofp y))
	   (equal (<_a (-_a x y) 0)
		  (<_a x y))))

(defthm
  Type-of-Nat-Int-Bound-rationalp
  (implies (rationalp x)
	   (integerp (nat-int-bound x)))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :use Type-of-Nat-Int-Bound)))

(defthm
  Nat-Int-Bound-is-a-bound-rationalp
  (implies (and (rationalp x)
		(>=  x 0))
	    (<= x (nat-int-bound x)))
  :rule-classes :linear
  :hints (("Goal"
	   :in-theory (disable Nat-Int-Bound-is-a-bound)
	   :use Nat-Int-Bound-is-a-bound)))

(in-theory (disable extension-laws))

(defthm
  Nonneg-Nat-Int-Bound
  (implies (and (aofp x)
		(>=_a x 0))
	   (>= (Nat-Int-Bound x) 0))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :in-theory (enable reverse-extension-laws))))

(in-theory (enable extension-laws))

(defun
  afix (x)
  (declare (xargs :guard t))
  (if (aofp x)
      x
      0))

(in-theory (disable (:executable-counterpart afix)))

; The encapsulate wrapper and local event in it were added by Matt K. for ACL2
; 2.7, since the first theory invariant is violated by the enable below.

(encapsulate
 ()

 (local (theory-invariant t :key inv1)) ; locally turn off theory invariant inv1

 (in-theory (enable reverse-extension-laws))

 (defthm
   <=-Nat-Int-Bound
   (implies (and (aofp x)
                 (>=_a x r)
                 (rationalp r)
                 (>=_a x 0))
            (<= r (Nat-Int-Bound x)))
   :rule-classes :linear
   :hints (("Goal"
            :in-theory (disable Nat-int-bound-is-a-bound
                                extension-laws)
            :use Nat-int-bound-is-a-bound)))

 (in-theory (disable reverse-extension-laws))

 )

(defun
  Least-nat-bound-loop (i x)
  (declare (xargs :guard (and (integerp i)
			      (aofp x))
		  :measure
		  (let ((i (ifix i))
			(x (afix x)))
		       (cond ((<_a x 0)
			      0)
			     ((>_a i x)
			      0)
			     (t
			      (+ 1
				 (Nat-Int-Bound x)(- i)))))))
  (let ((i (ifix i))
	(x (afix x)))
       (cond ((<_a x 0)
	      0)
	     ((>_a i x)
	      i)
	     (t
	      (Least-nat-bound-loop (+ 1 i) x)))))

(defun
  Least-nat-bound (x)

  "Return the least nonnegative
   integer larger than x."

  (declare (xargs :guard (aofp x)))
  (least-nat-bound-loop 0 x))

(defthm
  Least-nat-bound-is-a-bound
  (implies (aofp x)
	   (<_a x (Least-nat-bound-loop i x))))

(defthm
  <_a-+_a--_a-1a
  (implies (and (aofp x)
		(aofp y))
	   (equal (<_a x (+_a -1 y))
		  (<_a (+_a 1 x) y)))
  :hints (("Goal"
	   :use (:instance
		 <_a-+_a--_a-1
		 (z 1)))))

(local
 (defthm
   Least-nat-bound-loop-is-LEAST-bound-lemma
   (IMPLIES (AND (NOT (<_A X I))
		 (NOT (<_A I X))
		 (AOFP X)
		 (INTEGERP I)
		 (NOT (<_A X 0))
		 (<_A I (BINARY-+_A 1 X)))
	    (NOT (<_A (BINARY-+_A 1 X)
		      (LEAST-NAT-BOUND-LOOP (BINARY-+_A 1 I)
					    X))))
   :hints (("Goal"
	    :use (:instance
		  antisymmetry-of-<=_a
		  (y i))))))

(in-theory (disable extension-laws))

(in-theory (enable reverse-extension-laws))

(defthm
  Least-nat-bound-loop-is-LEAST-bound
  (implies (and (aofp x)
		(integerp i)
		(>=_a x 0)
		(<_a i (+_a x 1)))
	   (>=_a x
		 (- (Least-nat-bound-loop i x)
		    1))))

(in-theory (disable reverse-extension-laws))

(in-theory (enable extension-laws))

(defthm
  Increasing-successor
  (implies (aofp x)
	   (<_a x (+_a 1 x)))
  :hints (("Goal"
	   :use (:instance
		 compatibility-laws
		 (y 0)(z 1)))))

(defthm
  Nonneg-successor-pos
  (implies (and (aofp x)
		(>=_a x 0))
	   (>_a (+_a 1 x) 0))
  :hints (("Goal"
	   :in-theory (disable transitivity-of-<_a)
	   :use (:instance
		 transitivity-of-<_a
		 (x 0)(y x)(z (+_a 1 x))))))

(defthm
  Least-nat-bound-is-LEAST-bound
  (implies (and (integerp n)
		(aofp x)
		(>=_a x 0)
		(>_a n x))
	   (<= (Least-nat-bound-loop 0 x)
	       n))
  :hints (("Goal"
	   :in-theory (disable Transitivity-of-<=_a)
	   :use ((:instance
		  Least-nat-bound-loop-is-LEAST-bound
		  (i 0))
		 (:instance
		  Transitivity-of-<=_a
		  (x (- (Least-nat-bound-loop 0 x)
			1))
		  (y x)
		  (z n))))))

(defthm
  <=-rationalp-Least-nat-bound-loop
  (implies (and (aofp x)
		(integerp i)
		(rationalp r)
		(>=_a x r))
	   (<= r (least-nat-bound-loop i x))))

(defthm
  Nonneg-Least-nat-bound
  (implies (aofp x)
	   (>= (least-nat-bound-loop 0 x) 0))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :in-theory (disable
		       <=-rationalp-Least-nat-bound-loop)
	   :use (:instance
		 <=-rationalp-Least-nat-bound-loop
		 (r 0)(i 0)))))

(defthm
  <-rationalp-Least-nat-bound-loop
  (implies (and (aofp x)
		(integerp i)
		(rationalp r)
		(>=_a x r))
	   (< r (least-nat-bound-loop i x)))
  :hints (("Goal"
	   :in-theory (disable
		       <=-rationalp-Least-nat-bound-loop)
	   :use <=-rationalp-Least-nat-bound-loop)))

(defthm
  Pos-Least-nat-bound
  (implies (and (aofp x)
		(>=_a x 0))
	   (> (least-nat-bound-loop 0 x) 0))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :in-theory (disable
		       <-rationalp-Least-nat-bound-loop)
	   :use (:instance
		 <-rationalp-Least-nat-bound-loop
		 (r 0)(i 0)))))

(defthm
  Least-nat-bound-is-nondecreasing
  (implies (and (<=_a x1 x2)
		(aofp x1)
		(aofp x2)
		(integerp i))
	   (<= (Least-nat-bound-loop i x1)
	       (Least-nat-bound-loop i x2))))

(defthm
  Least-nat-bound-is-increasing-1
  (implies (and (<_a x1 0)
		(>=_a x2 0)
		(aofp x1)
		(aofp x2))
	   (< (Least-nat-bound-loop 0 x1)
	      (Least-nat-bound-loop 0 x2))))

(local
 (defthm
   Least-nat-bound-is-increasing-2-lemma-a
   (implies (and (aofp x1)
		 (aofp x2)
		 (>=_a (-_a x2 1) x1))
	    (>_a (-_a (least-nat-bound-loop 0 x2) 1)
		 x1))
   :rule-classes nil
   :hints (("Goal"
	    :use (:instance
		  compatibility-laws
		  (x -1)(z (least-nat-bound-loop 0 x2))
		  (y x2))))))

(local
 (defthm
   Least-nat-bound-is-increasing-2-lemma
   (implies (and (aofp x1)
		 (aofp x2)
		 (>=_a x1 0)
		 (>=_a (-_a x2 1) x1))
	    (>=_a (-_a (least-nat-bound-loop 0 x2) 1)
		  (least-nat-bound-loop 0 x1)))
   :rule-classes nil
   :hints (("Goal"
	    :use Least-nat-bound-is-increasing-2-lemma-a))))

(defthm
  Least-nat-bound-is-increasing-2
  (implies (and (>=_a x1 0)
		(>=_a (-_a x2 1) x1)
		(aofp x1)
		(aofp x2))
	   (< (Least-nat-bound-loop 0 x1)
	      (Least-nat-bound-loop 0 x2)))
  :hints (("Goal"
	   :use Least-nat-bound-is-increasing-2-lemma)))

(in-theory (disable Extension-Laws))

(in-theory (enable Reverse-Extension-Laws))

(defthm
  *_a-neg-rat
  (implies (and (syntaxp (quotep x))
		(rationalp x)
		(aofp y)
		(< x 0))
	   (and (equal (*_a x y)
		       (-_a (*_a (- x) y)))
		(equal (*_a y x)
		       (-_a (*_a y (- x)))))))

(in-theory (disable Reverse-Extension-Laws))

(in-theory (enable Extension-Laws))

(defthm
  Nonneg-difference-quotient
  (implies (and (aofp x)
		(aofp y)
		(aofp z)
		(<=_a x y)
		(>_a z 0))
	   (>=_a (/_a (-_a y x) z) 0))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (aofp x)
				(aofp y)
				(aofp z)
				(<=_a x y)
				(>_a z 0))
			   (>=_a (-_a (/_a y z)
				      (*_a (/_a z) x))
				 0)))))
