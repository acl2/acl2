; ACL2 Univariate Polynomials over a Field books -- Coefficients

;; The ACL2 Coeficientes abstractos book, in coeficiente.lisp, is modified
;; by replacing equality between coefficients with an equivalence relation
;; which satisfies the appropriate congruence theorems. Also the axioms for
;; a Ring are replaced with the axioms for a Field
; Copyright (C) 2006  John R. Cowles and Ruben A. Gamboa, University of
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

;; Modified by
;;   John Cowles
;;   Department of Computer Science
;;   University of Wyoming
;;   Laramie, WY 82071-3682 U.S.A.

;;   Modified June 2006.
;;   Last modified July 2006 (for ACL2 Version 3.0).

; Modified by Matt Kaufmann for ACL2 Version 3.1 because
; SBCL complains about LISP::.

;;  Based on
;;; ------------------------------------------------------------------
;;; Coeficientes abstractos
;;;
;;; Autores:
;;;
;;; Inmaculada Medina Bulo
;;; Francisco Palomo Lozano
;;;
;;; Descripción:
;;;
;;; Anillo abeliano de coeficientes. El conjunto de los coeficientes
;;; se representa como un anillo abeliano abstracto mediante un
;;; encapsulado. El conjunto de los números de ACL2 con su
;;; interpretación habitual sirve como modelo de la teoría generada.
;;;
;;; Notas generales:
;;;
;;; Puede ser interesante comparar esta formalización con la que
;;; aparece en los libros sobre aritmética de Kaufmann, Brock y
;;; Cowles.
;;;
;;; Se han incluido algunos teoremas que se deducen inmediatamente de
;;; otros por aplicación directa de la conmutatividad. Estos teoremas
;;; son innecesarios desde un punto de vista lógico, pero evitan el
;;; abuso de la conmutatividad.
;;; ------------------------------------------------------------------
#|
To certify this book, first, create a world with the following package:

(in-package "ACL2")

(defconst *import-symbols*
  (set-difference-eq
   (union-eq *acl2-exports*
	     *common-lisp-symbols-from-main-lisp-package*)
     '(null + * - < = / commutativity-of-* associativity-of-*
	    commutativity-of-+ associativity-of-+ distributivity)))

(defpkg "FLD"
  *import-symbols*)

(certify-book "coe-fld"
	      2
	      nil ;;compile-flg
	      )
|#
(in-package "FLD")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A Field is a nonempty set with two binary operations, addition and
;; multiplication, two unary operations, minus and inverse, and two field
;; elements, zero and one, such that

;; (1) the binary operations are commutative and associative,
;; (2) multiplication distributes over addition,
;; (3) zero is an identity for addition,
;; (4) minus produces an additive inverse,
;; (5) one is an identity for addition, and
;; (6) inverse produces a multiplicative inverse
;;             for non-zero field elements.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Equality between ring elements is replaced with an equivalence relation
;; that satisfies the appropriate congruence theorems.

;; There is also a ``choice'' function on the equivalence classes that
;; chooses an element from each equivalence class. In case new operations
;; on the field are defined by future users of this book, this choice
;; function may aid in defining these new operations, so as to ensure that
;; the congruence theorems for the new operations hold.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate

  ;;; ---------
  ;;; Signatura
  ;;; ---------

;;   ((coeficientep (a) boolean)
;;    (+ (a b) coeficiente)
;;    (* (a b) coeficiente)
;;    (- (a) coeficiente)
;;    (nulo () coeficiente)
;;    (identidad () coeficiente))

 ((fdp (x) x)        ; x is in the field iff (fdg x).
  (+ (a b) f)        ; Addition in Field.
  (* (a b) f)        ; Multiplication in Field.
  (- (f) f)          ; Unary minus in Field.
  (/ (f) f)          ; Unary recipical in Field
  (0_f () f)         ; 0 element in Field.
  (1_f () f)         ; 1 element in Field.
  (= (a b) Boolean)  ; Equality predicate for Field elements.
  (C_= (f) f))       ; Choose unique equivalence class representative for =.

  ;;; ----------------
  ;;; Testigos locales
  ;;; ----------------

  ;;; Reconocedor

;;   (local
;;     (defun coeficientep (a)
;;       (acl2-numberp a)))

 (local (defun
	  fdp (a)
	  (acl2-numberp a)))

  ;;; Primera operación

 (local
  (defun + (a b)
;   (declare (xargs :guard (and (coeficientep a) (coeficientep b))))
    (ACL2::+ a b)))

  ;;; Segunda operación

 (local
  (defun * (a b)
;   (declare (xargs :guard (and (coeficientep a) (coeficientep b))))
    (ACL2::* a b)))

  ;;; Inverso de la primera operación

 (local
  (defun - (a)
;   (declare (xargs :guard (coeficientep a)))
    (ACL2::- a)))

 (local
  (defun / (a)
;   (declare (xargs :guard (coeficientep a)))
    (ACL2::/ a)))

  ;;; Neutro de la primera operación

;;   (local
;;     (defun nulo ()
;;       0))

 (local (defun 0_f ()
	  0))

  ;;; Neutro de la segunda operación

;;   (local
;;     (defun identidad ()
;;       1))

 (local (defun 1_f ()
	  1))

  ;;; Igualdad sintáctica

;;   (defmacro = (a b)
;;     `(equal ,a ,b))

 (local (defun = (a b)
	  (equal a b)))

 (local (defun C_= (x)
	  (identity x)))

  ;;; -------
  ;;; Axiomas
  ;;; -------
  ;;; Field Axioms:

 ;;; El reconocedor es una función booleana

;;   (defthm booleanp-coeficientep
;;     (booleanp (coeficientep a))
;;     :rule-classes :type-prescription)

 (defthm booleanp-fdp
   (booleanp (fdp a))
   :rule-classes :type-prescription)

  ;;; Clausura de las operaciones

 (defthm
   Closure-Laws
   (and (implies (fdp a)
		 (and (implies (fdp b)
			       (and (fdp (+ a b))
				    (fdp (* a b))))
		      (fdp (- a))
		      (fdp (C_= a))
		      (implies (not (= a (0_f)))
			       (fdp (/ a)))))
	(fdp (0_f))
	(fdp (1_f)))
   :rule-classes nil)

 (defthm
    Equivalence-Law
    (and (booleanp (= x y))
	 (= x x)
	 (implies (= x y)
		  (= y x))
	 (implies (and (= x y)
		       (= y z))
		  (= x z)))
    :rule-classes :equivalence)

 (defthm
   Congruence-Laws
   (implies (= y1 y2)
	    (and (iff (fdp y1)
		      (fdp y2))
		 (= (+ x y1)
		    (+ x y2))
		 (= (* x y1)
		    (* x y2))
		 (= (+ y1 z)
		    (+ y2 z))
		 (= (* y1 z)
		    (* y2 z))
		 (= (- y1)
		    (- y2))
		 (= (/ y1)
		    (/ y2))))
   :rule-classes nil)

 (defthm
   Equivalence-class-Laws
   (and (implies (fdp x)
		 (= (C_= x) x))
	(implies (= y1 y2)
		 (equal (C_= y1)
			(C_= y2))))
   :rule-classes nil)

;;   (defthm |0 != 1|
;;     (not (equal (nulo) (identidad))))

 (defthm  |0 != 1|
   (not (= (0_f)(1_f))))

 (defthm
   Commutativity-Laws
   (implies (and (fdp a)
		 (fdp b))
	    (and (= (+ a b)
		    (+ b a))
		 (= (* a b)
		    (* b a))))
   :rule-classes nil)

 (defthm
   Associativity-Laws
   (implies (and (fdp a)
		 (fdp b)
		 (fdp c))
	    (and (= (+ (+ a b) c)
		    (+ a (+ b c)))
		 (= (* (* a b) c)
		    (* a (* b c)))))
   :rule-classes nil)

 (defthm
   Left-Distributivity-Law
   (implies (and (fdp a)
		 (fdp b)
		 (fdp c))
	    (= (* a (+ b c))
	       (+ (* a b)
		  (* a c))))
   :rule-classes nil)

 (defthm
   Left-Unicity-Laws
   (implies (fdp a)
	    (and (= (+ (0_f) a)
		    a)
		 (= (* (1_f) a)
		    a)))
   :rule-classes nil)

 (defthm
   Right-Inverse-Laws
   (implies (fdp a)
	    (and (= (+ a (- a))
		    (0_f))
		 (implies (not (= a (0_f)))
			  (= (* a (/ a))
			     (1_f)))))
   :rule-classes nil)
 ) ;;end encapsulate

;;   (defthm coeficientep-+
;;     (implies (and (coeficientep a) (coeficientep b))
;; 	     (coeficientep (+ a b)))
;;     :rule-classes :type-prescription)

(defthm
  Fdp-+
  (implies (and (fdp a)(fdp b))
	   (fdp (+ a b)))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :use Closure-Laws)))

;;   (defthm coeficientep-*
;;     (implies (and (coeficientep a) (coeficientep b))
;; 	     (coeficientep (* a b)))
;;     :rule-classes :type-prescription)

(defthm
  Fdp-*
  (implies (and (fdp a)(fdp b))
	   (fdp (* a b)))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :use Closure-Laws)))

;;   (defthm coeficientep--
;;     (implies (coeficientep a)
;; 	     (coeficientep (- a)))
;;     :rule-classes :type-prescription)

(defthm
  Fdp_-
  (implies (fdp a)
	   (fdp (- a)))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :use Closure-Laws)))

(defthm
  Fdp-/
  (implies (and (fdp a)
		(not (= a (0_f))))
	   (fdp (/ a)))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :use Closure-Laws)))

;;   (defthm coeficientep-nulo
;;     (coeficientep (nulo))
;;     :rule-classes :type-prescription)

(defthm
  Fdp-0_f
  (fdp (0_f))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :use Closure-Laws)))

;;   (defthm coeficientep-identidad
;;     (coeficientep (identidad))
;;     :rule-classes :type-prescription)

(defthm
  Fdp-1_f
  (fdp (1_f))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :use Closure-Laws)))

(defthm
  Fdp-C_=
  (implies (fdp a)
	   (fdp (C_= a)))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :use Closure-Laws)))

(defthm
  =-implies-iff-fdp
  (implies (= y1 y2)
	   (iff (fdp y1)
		(fdp y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-Laws)))

(defthm
  =-implies-=-+-1
  (implies (= y1 y2)
	   (= (+ y1 z)
	      (+ y2 z)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-Laws)))

(defthm
  =-implies-=-+-2
  (implies (= y1 y2)
	   (= (+ x y1)
	      (+ x y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-Laws)))

(defthm
  =-implies-=-*-1
  (implies (= y1 y2)
	   (= (* y1 z)
	      (* y2 z)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-Laws)))

(defthm
  =-implies-=-*-2
  (implies (= y1 y2)
	   (= (* x y1)
	      (* x y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-Laws)))

(defthm
  =-implies-=_-
  (implies (= y1 y2)
	   (= (- y1)
	      (- y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-Laws)))

(defthm
  =-implies-=-/
  (implies (= y1 y2)
	   (= (/ y1)
	      (/ y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Congruence-Laws)))

  ;;; Conmutatividad de la primera operación

;;   (defthm |a + b = b + a|
;;     (implies (and (coeficientep a) (coeficientep b))
;; 	     (= (+ a b) (+ b a))))

(defthm |a + b = b + a|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b)))
	   (= (+ a b) (+ b a)))
  :hints (("Goal"
	   :use Commutativity-Laws)))

  ;;; Asociatividad de la primera operación

;;   (defthm |(a + b) + c = a + (b + c)|
;;     (implies (and (coeficientep a) (coeficientep b) (coeficientep c))
;; 	     (= (+ (+ a b) c) (+ a (+ b c)))))

(defthm |(a + b) + c = a + (b + c)|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b))
		(fdp (double-rewrite c)))
	   (= (+ (+ a b) c) (+ a (+ b c))))
  :hints (("Goal"
	   :use Associativity-Laws)))

  ;;; Neutro de la primera operación

;;   (defthm |0 + a = a|
;;     (implies (coeficientep a)
;; 	     (= (+ (nulo) a) a)))

(defthm |0 + a = a|
  (implies (fdp (double-rewrite a))
	   (= (+ (0_f) a) a))
  :hints (("Goal"
	   :use Left-Unicity-Laws)))

  ;;; Conmutatividad de la segunda operación

;;   (defthm |a * b = b * a|
;;     (implies (and (coeficientep a) (coeficientep b))
;; 	     (= (* a b) (* b a))))

(defthm |a * b = b * a|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b)))
	   (= (* a b) (* b a)))
  :hints (("Goal"
	   :use Commutativity-Laws)))

  ;;; Asociatividad de la segunda operación

;;   (defthm |(a * b) * c = a * (b * c)|
;;      (implies (and (coeficientep a) (coeficientep b) (coeficientep c))
;; 	      (= (* (* a b) c) (* a (* b c)))))

(defthm |(a * b) * c = a * (b * c)|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b))
		(fdp (double-rewrite c)))
	   (= (* (* a b) c) (* a (* b c))))
  :hints (("Goal"
	   :use Associativity-Laws)))

  ;;; Neutro de la segunda operación

;;   (defthm |1 * a = a|
;;     (implies (coeficientep a)
;; 	     (= (* (identidad) a) a)))

(defthm |1 * a = a|
  (implies (fdp (double-rewrite a))
	   (= (* (1_f) a) a))
  :hints (("Goal"
	   :use Left-Unicity-Laws)))

  ;;; Inverso de la primera operación

;;   (defthm |a + (- a) = 0|
;;     (implies (coeficientep a)
;; 	     (= (+ a (- a)) (nulo))))

(defthm |a + (- a) = 0|
  (implies (fdp (double-rewrite a))
	   (= (+ a (- a)) (0_f)))
  :hints (("Goal"
	   :use Right-Inverse-Laws)))

(defthm |a * (/ a) = 1|
  (implies (and (fdp (double-rewrite a))
		(not (= (double-rewrite a) (0_f))))
	   (= (* a (/ a)) (1_f)))
  :hints (("Goal"
	   :use Right-Inverse-Laws)))

  ;;; Distributividad de la segunda operación respecto a la primera

;;   (defthm |a * (b + c) = (a * b) + (a * c)|
;;     (implies (and (coeficientep a) (coeficientep b) (coeficientep c))
;; 	     (= (* a (+ b c)) (+ (* a b) (* a c))))))

(defthm |a * (b + c) = (a * b) + (a * c)|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b))
		(fdp (double-rewrite c)))
	   (= (* a (+ b c)) (+ (* a b) (* a c))))
  :hints (("Goal"
	   :use Left-Distributivity-Law)))

;;; -----------------------------------------------------------------------
;;; El inverso debe ser invisible para la primera operación y para sí mismo
;;; -----------------------------------------------------------------------

;; (ACL2::set-invisible-fns-table ((+ -) (- -)))
(set-invisible-fns-table ((+ -) (- -) (* /) (/ /)))

;;; --------
;;; Teoremas
;;; --------

(defthm
  =-C_=
  (implies (fdp (double-rewrite x))
	   (= (C_= x) x))
  :hints (("Goal"
	   :use Equivalence-class-Laws)))

(defthm
  =-implies-equal-C_=
  (implies (= y1 y2)
	   (equal (C_= y1)
		  (C_= y2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use Equivalence-class-Laws)))

;;; Teoremas que resultan de aplicar la conmutatividad a los axiomas

;; (defthm |a + 0 = a|
;;   (implies (coeficientep a)
;; 	   (= (+ a (nulo)) a)))

(defthm |a + 0 = a|
  (implies (fdp (double-rewrite a))
	   (= (+ a (0_f)) a)))

;; (defthm |a * 1 = a|
;;   (implies (coeficientep a)
;; 	   (= (* a (identidad)) a)))

(defthm |a * 1 = a|
  (implies (fdp (double-rewrite a))
	   (= (* a (1_f)) a)))

;; (defthm |(- a) + a = 0|
;;   (implies (coeficientep a)
;; 	   (= (+ (- a) a) (nulo))))

(defthm |(- a) + a = 0|
  (implies (fdp (double-rewrite a))
	   (= (+ (- a) a) (0_f))))

(defthm |(/ a) * a = 1|
  (implies (and (fdp (double-rewrite a))
		(not (= (double-rewrite a) (0_f))))
	   (= (* (/ a) a) (1_f))))

;; (defthm |(a + b) * c = (a * c) + (b * c)|
;;   (implies (and (coeficientep a) (coeficientep b) (coeficientep c))
;; 	   (= (* (+ a b) c) (+ (* a c) (* b c)))))

(defthm |(a + b) * c = (a * c) + (b * c)|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b))
		(fdp (double-rewrite c)))
	   (= (* (+ a b) c) (+ (* a c) (* b c)))))

;;; Teorema de cancelación

;; (defthm |a + c = b + c <=> a = b|
;;   (implies (and (coeficientep a) (coeficientep b) (coeficientep c))
;; 	   (iff (= (+ a c) (+ b c)) (= a b)))
;;   :hints (("Goal"
;; 	   :in-theory (disable |a + b = b + a| |a + 0 = a|)
;; 	   :use ((:instance |a + b = b + a| (a (+ a c)) (b (- c)))
;; 	         (:instance |a + b = b + a| (a (- c)) (b (+ b c)))
;; 		 (:instance |a + 0 = a| (a b))
;; 		 |a + 0 = a|))))

(defthm |a + c = b + c <=> a = b|
  (implies (and (fdp a) (fdp b) (fdp c))
	   (iff (= (+ a c) (+ b c)) (= a b)))
  :hints (("Goal"
	   :in-theory (disable |a + b = b + a| |a + 0 = a|)
	   :use ((:instance |a + b = b + a| (a (+ a c)) (b (- c)))
	         (:instance |a + b = b + a| (a (- c)) (b (+ b c)))
		 (:instance |a + 0 = a| (a b))
		 |a + 0 = a|))))

;;; NOTA:
;;;
;;; Estos teoremas son innecesarios desde un punto de vista lógico
;;; pero son útiles en las subsecuentes demostraciones.

;; (local
;;   (defthm |a + b = b <=> a = 0|
;;     (implies (and (coeficientep a) (coeficientep b))
;; 	     (iff (= (+ a b) b) (= a (nulo))))
;;     :hints (("Goal"
;; 	     :in-theory (disable |a + c = b + c <=> a = b|)
;; 	     :use (:instance |a + c = b + c <=> a = b| (b (nulo)) (c b))))))

(local
  (defthm |a + b = b <=> a = 0|
    (implies (and (fdp a) (fdp b))
	     (iff (= (+ a b) b) (= a (0_f))))
    :hints (("Goal"
	     :in-theory (disable |a + c = b + c <=> a = b|)
	     :use (:instance |a + c = b + c <=> a = b| (b (0_f)) (c b))))))

;; (local
;;   (defthm |a + b = 0 <=> b = - a|
;;     (implies (and (coeficientep a) (coeficientep b))
;; 	     (iff (= (+ a b) (nulo)) (= b (- a))))
;;     :hints (("Goal"
;; 	     :in-theory (disable |a + c = b + c <=> a = b|)
;; 	     :use (:instance |a + c = b + c <=> a = b| (a b) (b (- a)) (c a))))))

(local
  (defthm |a + b = 0 <=> b = - a|
    (implies (and (fdp a) (fdp b))
	     (iff (= (+ a b) (0_f)) (= b (- a))))
    :hints (("Goal"
	     :in-theory (disable |a + c = b + c <=> a = b|)
	     :use (:instance |a + c = b + c <=> a = b| (a b) (b (- a)) (c a))))))

;;; Complemento a la conmutatividad y la asociatividad de la primera operación

;;; NOTA:
;;;
;;; Dada una operación, las reglas generadas por este teorema y los
;;; axiomas de conmutatividad y asociatividad permiten decidir una
;;; igualdad de dos términos en los que sólo intervienen símbolos sin
;;; interpretación y dicha operación. Esto se debe a que ACL2 emplea
;;; un sistema de reescritura ordenada. Véase «Ordered Rewriting and
;;; Confluence», por Martin y Nipkow.

;; (defthm |a + (b + c) = b + (a + c)|
;;   (implies (and (coeficientep a) (coeficientep b) (coeficientep c))
;; 	   (= (+ a (+ b c)) (+ b (+ a c))))
;;   :hints (("Goal"
;; 	   :in-theory (disable |(a + b) + c = a + (b + c)|)
;; 	   :use (|(a + b) + c = a + (b + c)|
;; 		 (:instance |(a + b) + c = a + (b + c)| (a b) (b a))))))

(defthm |a + (b + c) = b + (a + c)|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b))
		(fdp (double-rewrite c)))
	   (= (+ a (+ b c)) (+ b (+ a c))))
  :hints (("Goal"
	   :in-theory (disable |(a + b) + c = a + (b + c)|)
	   :use (|(a + b) + c = a + (b + c)|
		 (:instance |(a + b) + c = a + (b + c)| (a b) (b a))))))

;;; Complemento a la conmutatividad y la asociatividad de la segunda operación

;;; NOTA:
;;;
;;; Se aplican comentarios análogos a los del caso anterior.

;; (defthm |a * (b * c) = b * (a * c)|
;;   (implies (and (coeficientep a) (coeficientep b) (coeficientep c))
;; 	   (= (* a (* b c)) (* b (* a c))))
;;   :hints (("Goal"
;; 	   :in-theory (disable |(a * b) * c = a * (b * c)|)
;; 	   :use (|(a * b) * c = a * (b * c)|
;; 		 (:instance |(a * b) * c = a * (b * c)| (a b) (b a))))))

(defthm |a * (b * c) = b * (a * c)|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b))
		(fdp (double-rewrite c)))
	   (= (* a (* b c)) (* b (* a c))))
  :hints (("Goal"
	   :in-theory (disable |(a * b) * c = a * (b * c)|)
	   :use (|(a * b) * c = a * (b * c)|
		 (:instance |(a * b) * c = a * (b * c)| (a b) (b a))))))

;;; Idempotencia del inverso

;; (defthm |- (- a) = a|
;;   (implies (coeficientep a)
;; 	   (= (- (- a)) a))
;;   :hints (("Goal"
;; 	   :in-theory (disable |a + b = 0 <=> b = - a|)
;; 	   :use (:instance |a + b = 0 <=> b = - a| (a (- a)) (b a)))))

(defthm |- (- a) = a|
  (implies (fdp (double-rewrite a))
	   (= (- (- a)) a))
  :hints (("Goal"
	   :in-theory (disable |a + b = 0 <=> b = - a|)
	   :use (:instance |a + b = 0 <=> b = - a| (a (- a)) (b a)))))

;;; Distributividad de la inversa sobre la primera operación

;; (defthm |- (a + b) = (- a) + (- b)|
;;   (implies (and (coeficientep a) (coeficientep b))
;; 	   (= (- (+ a b)) (+ (- a) (- b))))
;;   :hints (("Goal"
;; 	   :in-theory (disable |a + b = 0 <=> b = - a|)
;; 	   :use (:instance |a + b = 0 <=> b = - a| (a (+ a b)) (b (+ (- a) (- b)))))))

(defthm |- (a + b) = (- a) + (- b)|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b)))
	   (= (- (+ a b)) (+ (- a) (- b))))
  :hints (("Goal"
	   :in-theory (disable |a + b = 0 <=> b = - a|)
	   :use (:instance |a + b = 0 <=> b = - a|
			   (a (+ a b)) (b (+ (- a) (- b)))))))

;;; Inverso del neutro de la primera operación

;; (defthm |- 0 = 0|
;;   (= (- (nulo)) (nulo))
;;   :hints (("Goal"
;; 	   :in-theory (disable |a + b = 0 <=> b = - a|)
;; 	   :use (:instance |a + b = 0 <=> b = - a| (a (nulo)) (b (nulo))))))

(defthm |- 0 = 0|
  (= (- (0_f)) (0_f))
  :hints (("Goal"
	   :in-theory (disable |a + b = 0 <=> b = - a|)
	   :use (:instance |a + b = 0 <=> b = - a| (a (0_f)) (b (0_f))))))

;;; Generalización de |a + (- a) = 0|

;; (defthm |a + ((- a) + b) = b|
;;   (implies (and (coeficientep a) (coeficientep b))
;; 	   (= (+ a (+ (- a) b)) b))
;;   :hints (("Goal"
;; 	   :in-theory (disable |a + (b + c) = b + (a + c)|)
;; 	   :use (:instance |a + (b + c) = b + (a + c)| (c (- a))))))

(defthm |a + ((- a) + b) = b|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b)))
	   (= (+ a (+ (- a) b)) b))
  :hints (("Goal"
	   :in-theory (disable |a + (b + c) = b + (a + c)|)
	   :use (:instance |a + (b + c) = b + (a + c)| (c (- a))))))

;; (defthm |a + (b + (- a)) = b|
;;     (implies (and (coeficientep a) (coeficientep b))
;; 	     (= (+ a (+ b (- a))) b)))

(defthm |a + (b + (- a)) = b|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b)))
	   (= (+ a (+ b (- a))) b)))

;;; Elemento cancelador de la segunda operación

;; (defthm |0 * a = 0|
;;   (implies (coeficientep a)
;; 	   (= (* (nulo) a) (nulo)))
;;   :hints (("Goal"
;; 	   :in-theory (disable |a * (b + c) = (a * b) + (a * c)|)
;; 	   :use (:instance |a * (b + c) = (a * b) + (a * c)|
;;               (b (nulo)) (c (nulo))))))

(defthm |0 * a = 0|
  (implies (fdp (double-rewrite a))
	   (= (* (0_f) a) (0_f)))
  :hints (("Goal"
	   :in-theory (disable |a * (b + c) = (a * b) + (a * c)|
			       |a + b = b <=> a = 0|)
	   :use ((:instance |a * (b + c) = (a * b) + (a * c)|
			    (b (0_f)) (c (0_f)))
		 (:instance |a + b = b <=> a = 0|
			    (a (* a (0_f)))(b (* a (0_f))))))))

;; (defthm |a * 0 = 0|
;;   (implies (coeficientep a)
;; 	   (= (* a (nulo)) (nulo))))

(defthm |a * 0 = 0|
  (implies (fdp (double-rewrite a))
	   (= (* a (0_f)) (0_f))))

;;; Extracción del inverso

;; (defthm |a * (- b) = - (a * b)|
;;   (implies (and (coeficientep a) (coeficientep b))
;; 	   (= (* a (- b)) (- (* a b))))
;;   :hints (("Goal"
;; 	   :in-theory (disable |a * (b + c) = (a * b) + (a * c)|)
;; 	   :use (:instance |a * (b + c) = (a * b) + (a * c)| (b (- b)) (c b)))))

(defthm |a * (- b) = - (a * b)|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b)))
	   (= (* a (- b)) (- (* a b))))
  :hints (("Goal"
	   :in-theory (disable |a * (b + c) = (a * b) + (a * c)|
			       |a + b = 0 <=> b = - a|)
	   :use ((:instance |a * (b + c) = (a * b) + (a * c)| (b (- b)) (c b))
		 (:instance |a + b = 0 <=> b = - a| (a (* a b))(b (* a (- b))))))))

;; (defthm |(- a) * b = - (a * b)|
;;   (implies (and (coeficientep a) (coeficientep b))
;; 	   (= (* (- a) b) (- (* a b)))))

(defthm |(- a) * b = - (a * b)|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b)))
	   (= (* (- a) b) (- (* a b)))))

;;; Generalización de |- 0 = 0|

;; (defthm |- a = 0 <=> a = 0|
;;   (implies (coeficientep a)
;; 	   (iff (= (- a) (nulo)) (= a (nulo))))
;;   :hints (("Goal"
;; 	   :in-theory (disable |a + b = 0 <=> b = - a|)
;; 	   :use (:instance |a + b = 0 <=> b = - a| (b (nulo))))))

(defthm |- a = 0 <=> a = 0|
  (implies (fdp a)
	   (iff (= (- a) (0_f)) (= a (0_f))))
  :hints (("Goal"
	   :in-theory (disable |a + b = 0 <=> b = - a|)
	   :use (:instance |a + b = 0 <=> b = - a| (b (0_f))))))

(defthm |a * c = b * c <=> a = b or c = 0|
  (implies (and (fdp a)
		(fdp b)
		(fdp c))
	   (iff (= (* a c) (* b c))
		(or (= a b)
		    (= c (0_f)))))
  :hints (("Subgoal 3"
	   :in-theory (disable =-implies-=-*-1)
	   :use (:instance
		 =-implies-=-*-1
		 (y1 (* a c))
		 (y2 (* b c))
		 (z (/ c))))))

(local
  (defthm |a * b = b <=> a = 1|
    (implies (and (fdp a)
		  (fdp b)
		  (not (= b (0_f))))
	     (iff (= (* a b) b)
		  (= a (1_f))))
    :hints (("Goal"
	     :in-theory (disable |a * c = b * c <=> a = b or c = 0|)
	     :use (:instance |a * c = b * c <=> a = b or c = 0|
			     (b (1_f)) (c b))))))

(local
  (defthm |a != 0 implies a * b = 1 <=> b = (/ a)|
    (implies (and (fdp a)
		  (fdp b)
		  (not (= a (0_f))))
	     (iff (= (* a b) (1_f)) (= b (/ a))))
    :hints (("Goal"
	     :in-theory (disable |a * c = b * c <=> a = b or c = 0|)
	     :use (:instance |a * c = b * c <=> a = b or c = 0|
			     (a b) (b (/ a)) (c a))))))

(defthm
  |/ a != 0|
  (implies (and (fdp a)
		(not (= a (0_f))))
	   (not (= (/ a)(0_f))))
  :hints (("Goal"
	   :in-theory (disable |a * 0 = 0|
			       |a * (/ a) = 1|)
	   :use (|a * 0 = 0|
		 |a * (/ a) = 1|))))

(defthm |/ (/ a) = a|
  (implies (and (fdp (double-rewrite a))
		(not (= (double-rewrite a) (0_f))))
	   (= (/ (/ a)) a))
  :hints (("Goal"
	   :in-theory (disable |a != 0 implies a * b = 1 <=> b = (/ a)|)
	   :use (:instance |a != 0 implies a * b = 1 <=> b = (/ a)|
			  (a (/ a)) (b a)))))

(defthm
  |a * b = 0 iff a = 0 or b = 0|
  (implies (and (fdp a)
		(fdp b))
	   (equal (= (* a b)(0_f))
		  (or (= a (0_f))
		      (= b (0_f)))))
  :hints (("Subgoal 1"
	   :in-theory (disable |a * c = b * c <=> a = b or c = 0|)
	   :use (:instance
		 |a * c = b * c <=> a = b or c = 0|
		 (a b)(b (0_f))(c a)))))

(defthm |/ (a * b) = (/ a) * (/ b)|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b))
		(not (= (double-rewrite a)(0_f)))
		(not (= (double-rewrite b)(0_f))))
	   (= (/ (* a b)) (* (/ a) (/ b))))
  :hints (("Goal"
	   :in-theory (disable |a != 0 implies a * b = 1 <=> b = (/ a)|)
	   :use (:instance |a != 0 implies a * b = 1 <=> b = (/ a)|
			   (a (* a b)) (b (* (/ a) (/ b)))))))

(defthm
  |1 != 0|
  (not (= (1_f)(0_f)))
  :hints (("Goal"
	   :use |0 != 1|)))

(defthm |/ 1 = 1|
  (= (/ (1_f))(1_f))
  :hints (("Goal"
	   :in-theory (disable |a != 0 implies a * b = 1 <=> b = (/ a)|)
	   :use (:instance |a != 0 implies a * b = 1 <=> b = (/ a)|
			   (a (1_f)) (b (1_f))))))

(defthm |a * ((/ a) * b) = b|
  (implies (and (fdp (double-rewrite a))
		(not (= (double-rewrite a)(0_f)))
		(fdp (double-rewrite b)))
	   (= (* a (* (/ a) b)) b))
  :hints (("Goal"
	   :in-theory (disable |a * (b * c) = b * (a * c)|)
	   :use (:instance |a * (b * c) = b * (a * c)| (c (/ a))))))

(defthm |a * (b * (/ a)) = b|
  (implies (and (fdp (double-rewrite a))
		(not (= (double-rewrite a)(0_f)))
		(fdp (double-rewrite b)))
	   (= (* a (* b (/ a))) b)))

(defthm |/ a = 1 <=> a = 1|
  (implies (and (fdp a)
		(not (= a (0_f))))
	   (iff (= (/ a)(1_f))(= a (1_f))))
  :hints (("Goal"
	   :in-theory (disable |a != 0 implies a * b = 1 <=> b = (/ a)|)
	   :use (:instance |a != 0 implies a * b = 1 <=> b = (/ a)|
			   (b (1_f))))))

;;; -----------------
;;; Otras propiedades
;;; -----------------

;;; NOTA:
;;;
;;; El lado izquierdo puede aparecer por varias razones, sin
;;; descartar una aplicación de |- (a + b) = (- a) + (- b)| en un
;;; contexto en el que aparece |- (a + b) = c| y posteriormente se
;;; establece que |c = 0|. Esto podría evitarse postponiendo la
;;; definición de dicha regla.

;; (defthm |(- a) + (- b) = 0 <=> a + b = 0|
;;   (implies (and (coeficientep a) (coeficientep b))
;; 	   (iff (= (+ (- a) (- b)) (nulo)) (= (+ a b) (nulo)))))

(defthm |(- a) + (- b) = 0 <=> a + b = 0|
  (implies (and (fdp a) (fdp b))
	   (iff (= (+ (- a) (- b))(0_f))(= (+ a b)(0_f)))))

(defthm |(/ a) * (/ b) = 1 <=> a * b = 1|
  (implies (and (fdp a)
		(not (= a (0_f)))
		(fdp b)
		(not (= b (0_f))))
	   (iff (= (* (/ a)(/ b))(1_f))(= (* a b)(1_f)))))

;;; NOTA:
;;;
;;; En un anillo el recíproco no es, en general, cierto.

;; (defthm |b + c = 0 => (a * b) + (a * c) = 0|
;;   (implies (and (coeficientep a) (coeficientep b) (coeficientep c)
;; 		(= (+ b c) (nulo)))
;; 	   (= (+ (* a b) (* a c)) (nulo))))

(defthm |b + c = 0 => (a * b) + (a * c) = 0|
  (implies (and (fdp (double-rewrite a))
		(fdp (double-rewrite b))
		(fdp (double-rewrite c))
		(= (+ (double-rewrite b)
		      (double-rewrite c))
		   (0_f)))
	   (= (+ (* a b) (* a c))(0_f))))
