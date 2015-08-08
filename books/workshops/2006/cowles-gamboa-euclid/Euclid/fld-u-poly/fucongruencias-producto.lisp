; ACL2 Univariate Polynomials over a Field books -- Product Congruences
;; Congruences for Products of Univariate Polynomials over a Field
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

;; Modified by J. Cowles

;;   Last modified July 2006 (for ACL2 Version 3.0).

;; Based on
;;; -----------------------------------------------------------------
;;; Congruencias de la igualdad con el producto de polinomios
;;;
;;; Autores:
;;;
;;; Inmaculada Medina Bulo
;;; Francisco Palomo Lozano
;;;
;;; Descripción:
;;;
;;; Demostración de las congruencias de la igualdad de polinomios con
;;; el producto externo y el producto.
;;; -----------------------------------------------------------------
#|
To certify this book, first, create a world with the following packages:

(in-package "ACL2")

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

(certify-book "fucongruencias-producto"
	      5
	      nil ;;compile-flg
	      )
|#
(in-package "FUPOL")

;; (include-book "producto")
(include-book "fuproducto"
	      :load-compiled-file nil)

;;; --------------------------------------------------------
;;; Éstas son las propiedades de "polinomio" que lo abstraen
;;; --------------------------------------------------------

(defthm |m +M p != 0|
  (implies (monomiop m)
	   (consp (+M m p)))
  :rule-classes :type-prescription)

(defthm |mp(m +M p) = m|
  (implies (monomiop (double-rewrite m))
	   (equal (primero (+M m p)) m)))

(defthm |resto(m +M p) = p|
  (implies (and (monomiop (double-rewrite m))
		(polinomiop (double-rewrite p)))
	   (equal (resto (+M m p)) p)))

;;; ++++++++++++++++++++++++++
;;; + Barrera de abstracción +
;;; ++++++++++++++++++++++++++

(in-theory (disable +M))

;;; ---------------------------------------------------------------
;;; Distributividad del producto externo respecto a la suma externa
;;; ---------------------------------------------------------------

;;; Propiedades sintácticas de la suma de monomio y polinomio y la
;;; normalización.

;; (defthm |fn(m +Mo fn(p)) = fn(m +Mo p)|
;;   (equal (fn (+-monomio m (fn p)))
;; 	 (fn (+-monomio m p))))

(defthm |fn(m +Mo fn(p)) =P fn(m +Mo p)|
  (=P (fn (+-monomio m (fn p)))
      (fn (+-monomio m p)))
  :hints (("Subgoal *1/8"
	   :in-theory (enable +M))))

;; (defthm |(m +Mo fn(p)) = fn(m +Mo p)|
;;   (equal (+-monomio m (fn p))
;; 	 (fn (+-monomio m p))))

(defthm |(m +Mo fn(p)) =P fn(m +Mo p)|
  (=P (+-monomio m (fn p))
      (fn (+-monomio m p)))
  :hints (("Subgoal *1/8"
	   :in-theory (enable +M))))

;;; Este es un caso particular de la definición de "+-monomio".

(defthm |n +Mo p = p_p +M (n +Mo p_r)|
  (implies (and (monomiop (double-rewrite n))
		(polinomiop (double-rewrite p))
		(not (nulop p))
		(FUTER::< (termino n) (termino (primero p))))
	   (equal (+-monomio n p)
		  (+M (primero p) (+-monomio n (resto p)))))
  :hints (("Goal" :do-not '(generalize))))

;;; Esta propiedad sintáctica establece la relación entre La suma de
;;; monomios y polinomios, el constructor de los polinomios y la
;;; función de normalización.

(defthm |m +Mo fn(p) = fn(m +M p)|
  (implies (and (monomiop (double-rewrite m))
		(polinomiop (double-rewrite p)))
	   (equal (+-monomio m (fn p))
		  (fn (+M m p)))))

(in-theory (disable |m +Mo fn(p) = fn(m +M p)|
		    FLD::|b + c = 0 => (a * b) + (a * c) = 0|))

;;; NOTA:
;;;
;;; Este teorema es tremendamente complicado. Nótese que la igualdad a
;;; la que apela es sintáctica. El problema es una explosión
;;; combinatoria en el número de casos debido, principalmente, a la
;;; gran cantidad de casos existente en la definición de
;;; "+-monomio". Por otro lado, no parece factible simplificar dicha
;;; definición, ya que esto obligaría a añadir hipótesis a muchos
;;; teoremas que son necesarios para demostrar la congruencia
;;; (recuérdese que las congruencias son incondicionales). La
;;; consecuencia es una prueba muy extensa, poco automatizada y muy
;;; sensible al entorno.

(defun esquema-de-induccion-1 (n p)
  (declare (xargs :verify-guards nil))
  (if (and (not (nulop p)) (FUTER::< (termino n) (termino (primero p))))
      (esquema-de-induccion-1 n (resto p))
    t))

(in-theory (enable FUMON::*))

;; (defthm |fn(m *M (n +Mo p)) = fn((m * n) +Mo (m *M p))|
;;   (implies (and (monomiop m) (monomiop n) (polinomiop p))
;; 	   (equal (fn (*-monomio m (+-monomio n p)))
;; 		  (fn (+-monomio (UMON::* m n) (*-monomio m p)))))
;;   :hints (("Goal"
;; 	   :do-not '(eliminate-destructors generalize)
;; 	   :induct (esquema-de-induccion-1 n p))
;; ;;; Caso base
;; 	  ("Subgoal *1/2.1"
;; 	   :expand (+-monomio n p))
;; 	  ("Subgoal *1/2.1.1"
;; 	   :in-theory (disable MON::monomio-coeficiente-termino)
;; 	   :use ((:instance COE::|b + c = 0 => (a * b) + (a * c) = 0|
;; 			    (COE::a (coeficiente m)) (COE::b (coeficiente n))
;; 			    (COE::c (coeficiente (primero p))))))
;; ;;; Caso inductivo
;; 	  ("Subgoal *1/1"
;; 	   :in-theory (disable +-monomio
;; 			       UMON::*
;; 			       fnp-fn fn
;; 			       |fn(m +Mo fn(p)) = fn(m +Mo p)|
;; 			       |(m +Mo fn(p)) = fn(m +Mo p)|
;; 			       |m1 +Mo (m2 +Mo p) =e m2 +Mo (m1 +Mo p)|
;; 			       fn-ordenado fnp-iff-ordenadop ordenadop-fn)
;; 	   :use (:instance fnp-fn (p (*-monomio m (+-monomio n p)))))
;; 	  ("Subgoal *1/1'5'"
;; 	   :expand (fn (+M (UMON::* m (primero p))
;; 				  (*-monomio m (+-monomio n (resto p))))))
;; 	  ("Subgoal *1/1'7'"
;; 	   :use (:instance |(m +Mo fn(p)) = fn(m +Mo p)|
;; 			   (m (UMON::* M N))
;; 			   (p (*-monomio m (resto p)))))
;; 	  ("Subgoal *1/1'9'"
;; 	   :use ((:instance ordenadop-fn
;; 			    (p (*-monomio m (resto p))))
;; 		 (:instance |m1 +Mo (m2 +Mo p) =e m2 +Mo (m1 +Mo p)|
;; 			    (m1 (MON::* m (primero p)))
;; 			    (m2 (MON::* m n))
;; 			    (p (fn (*-monomio m (resto p)))))))
;; 	  ("Subgoal *1/1'11'"
;; 	   :use ((:instance |m +Mo fn(p) = fn(m +M p)|
;; 			    (m  (MON::* M (primero p)))
;; 			    (p (*-monomio m  (resto p))))))
;; 	  ("Subgoal *1/1'14'"
;; 	   :use ((:instance |fn(m +Mo fn(p)) = fn(m +Mo p)|
;; 			    (m  (MON::* m n))
;; 			    (p (+M (MON::* M (primero P))
;; 					  (*-monomio m  (resto p)))))))))
;; )

(defthm |fn(m *M (n +Mo p)) =P fn((m * n) +Mo (m *M p))|
  (implies (and (monomiop (double-rewrite m))
		(monomiop (double-rewrite n))
		(polinomiop (double-rewrite p)))
	   (=P (fn (*-monomio m (+-monomio n p)))
	       (fn (+-monomio (FUMON::* m n) (*-monomio m p)))))
  :hints (("Goal"
	   :do-not '(eliminate-destructors generalize)
	   :induct (esquema-de-induccion-1 n p))
;;; Caso base
	  ("Subgoal *1/2.1"
	   :expand (+-monomio n p))
	  ("Subgoal *1/2.1.1"
	   :in-theory (disable FUMON::monomio-coeficiente-termino)
	   :use ((:instance FLD::|b + c = 0 => (a * b) + (a * c) = 0|
			    (FLD::a (coeficiente m)) (FLD::b (coeficiente n))
			    (FLD::c (coeficiente (primero p))))))
;;; Caso inductivo
	  ("Subgoal *1/1"
	   :in-theory (disable +-monomio
			       FUMON::*
			       fnp-fn fn
			       |fn(m +Mo fn(p)) =P fn(m +Mo p)|
			       |(m +Mo fn(p)) =P fn(m +Mo p)|
			       |m1 +Mo (m2 +Mo p) =P m2 +Mo (m1 +Mo p)|
			       |m1 +Mo (m2 +Mo p) = m2 +Mo (m1 +Mo p)|
			       fn-ordenado fnp-iff-ordenadop ordenadop-fn)
	   :use (:instance fnp-fn (p (*-monomio m (+-monomio n p)))))
	  ("Subgoal *1/1'5'"
	   :expand (fn (+M (FUMON::* m (primero p))
				  (*-monomio m (+-monomio n (resto p))))))
	  ("Subgoal *1/1'6'"
	   :use (:instance |(m +Mo fn(p)) =P fn(m +Mo p)|
			   (m (FUMON::* M N))
			   (p (*-monomio m (resto p)))))
	  ("Subgoal *1/1'8'"
	   :use ((:instance ordenadop-fn
			    (p (*-monomio m (resto p))))
		 (:instance |m1 +Mo (m2 +Mo p) = m2 +Mo (m1 +Mo p)|
			    (m1 (FUMON::* m (primero p)))
			    (m2 (FUMON::* m n))
			    (p (fn (*-monomio m (resto p)))))))
	  ("Subgoal *1/1'11'"
	   :use ((:instance |m +Mo fn(p) = fn(m +M p)|
			    (m  (FUMON::* M (primero p)))
			    (p (*-monomio m  (resto p))))))
	  ("Subgoal *1/1'14'"
	   :use ((:instance |fn(m +Mo fn(p)) =P fn(m +Mo p)|
			    (m  (FUMON::* m n))
			    (p (+M (FUMON::* M (primero P))
				   (*-monomio m  (resto p)))))))
	  ("Subgoal *1/1'19'"
	   :in-theory (disable =P-implies-=P-+-monomio-2b)
	   :use ((:instance ordenadop-fn
			    (p (*-monomio m (+-monomio n (cdr p)))))
		 (:instance
		  =P-implies-=P-+-monomio-2b
		  (m (FUMON::* m (car p)))
		  (p1 (+-monomio (FUMON::* m n)(fn (*-monomio m (cdr p)))))
		  (p2 (fn (*-monomio m (+-monomio n (cdr p))))))))))

(in-theory (disable FUMON::*
		    |fn(m +Mo fn(p)) =P fn(m +Mo p)|
		    |(m +Mo fn(p)) =P fn(m +Mo p)|
		    |n +Mo p = p_p +M (n +Mo p_r)|))

;;; NOTA:
;;;
;;; En realidad, este es el teorema que realmente queremos demostrar
;;; pero, para ello, hemos necesitado el anterior. Se emplea en la
;;; demostración de que "m *M p = m *M fn(p)", que permite establecer
;;; la congruencia con el producto externo.

(in-theory (disable |fn(m *M (n +Mo p)) =P fn((m * n) +Mo (m *M p))|))

(defthm |m *M (n +Mo p) = (m * n) +Mo (m *M p)|
  (implies (and (monomiop (double-rewrite m))
		(monomiop (double-rewrite n))
		(polinomiop (double-rewrite p)))
	   (= (*-monomio m (+-monomio n p))
	      (+-monomio (FUMON::* m n) (*-monomio m p))))
  :hints (("Goal"
	   :use |fn(m *M (n +Mo p)) =P fn((m * n) +Mo (m *M p))|)))

;; (in-theory (disable |fn(m *M (n +Mo p)) = fn((m * n) +Mo (m *M p))|))

;;; ++++++++++++++++++++++++++
;;; + Barrera de abstracción +
;;; ++++++++++++++++++++++++++

(in-theory (disable = (=)))

;;; -----------------------------------------------------------------
;;; Congruencias de la igualdad de polinomios con el producto externo
;;; -----------------------------------------------------------------

;;; Primer parámetro

;; (defcong MON::= = (*-monomio m p) 1
;;   :hints (("Goal" :in-theory (enable MON::=))))

(defthm
  |FUMON::=-implies-=-*-monomio-1|
  (implies (FUMON::= m1 m2)
	   (= (*-monomio m1 p)
	      (*-monomio m2 p)))
  :rule-classes :congruence)

;;; Segundo parámetro

;;; NOTA:
;;;
;;; Esta propiedad es expansiva; restringimos su aplicación sintácticamente

(local
  (defthm |m +M p = m +Mo p|
    (implies (and (monomiop (double-rewrite m))
		  (polinomiop (double-rewrite p)))
	     (= (+M m p) (+-monomio m p)))
    :hints (("Goal" :in-theory (enable =)
	     :use (|m +Mo fn(p) = fn(m +M p)|
		   |(m +Mo fn(p)) =P fn(m +Mo p)|)))))

(local
  (defthm |m *M p = m *M fn(p)|
    (implies (syntaxp (not (and (consp p) (eq (primero p) 'fn))))
	     (= (*-monomio m p) (*-monomio m (fn p))))))

(local
 (in-theory (disable |m *M p = m *M fn(p)|)))

(defthm
  =P-implies-=P-*-monomio-2
  (implies (=P p1 p2)
	   (=P (*-monomio m p1)
	       (*-monomio m p2)))
  :rule-classes :congruence)

(defthm
  =-implies-=-*-monomio-fn-2
  (implies (= (double-rewrite p1)
	      (double-rewrite p2))
	   (equal (= (*-monomio m (fn p1))
		     (*-monomio m (fn p2)))
		  t))
  :hints (("Goal"
	   :in-theory (enable =))))

(local
 (in-theory (enable |m *M p = m *M fn(p)|)))

;; (defcong = = (*-monomio m p) 2)

(defthm
  =-implies-*-monomio-2
  (implies (= p1 p2)
	   (= (*-monomio m p1)
	      (*-monomio m p2)))
  :rule-classes :congruence)

;;; --------------------------------------------------------
;;; Congruencia de la igualdad de polinomios con el producto
;;; --------------------------------------------------------

;;; Segundo parámetro

(defthm |p * fn(q) = p * q|
  (= (* p (fn q)) (* p q)))

;; (defcong = = (* p q) 2)
(defthm
  =-implies-=-*-2
  (implies (= q1 q2)
	   (= (* p q1)
	      (* p q2)))
  :rule-classes :congruence)

;;; Primer parámetro

(defthm |fn(p) * q = p * q|
  (= (* (fn p) q) (* p q)))

;; (defcong = = (* p q) 1
;;   :hints (("Goal"
;; 	   :in-theory (disable |p * q = q * p|)
;; 	   :use (|p * q = q * p|
;; 		 (:instance |p * q = q * p| (p p-equiv))))))
(defthm
  =-implies-=-*-1
  (implies (= p1 p2)
	   (= (* p1 q)
	      (* p2 q)))
  :rule-classes :congruence
  :hints (("Goal"
	   :in-theory (disable |p * q = q * p|)
	   :use ((:instance |p * q = q * p| (p p1))
		 (:instance |p * q = q * p| (p p2))))))

;;; NOTA:
;;;
;;; Esta propiedad es consecuencia inmediata de las dos propiedades
;;; auxiliares anteriores

(defthm |fn(p) * fn(q) = p * q|
  (= (* (fn p) (fn q)) (* p q)))

(in-theory (disable |p * fn(q) = p * q|
		    |fn(p) * q = p * q|
		    |fn(p) * fn(q) = p * q|))
