; ACL2 Univariate Polynomials over a Field books -- Normal Form
;; Normal form for Univariate Polynomials over a Field
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
;;; Forma normal de polinomios
;;;
;;; Autores:
;;;
;;; Inmaculada Medina Bulo
;;; Francisco Palomo Lozano
;;;
;;; Descripción:
;;;
;;; Desarrollo de la función de normalización que permite reducir la
;;; comprobación de la igualdad semántica de dos polinomios a la de
;;; una igualdad sintáctica de sus formas normales. Se define primero
;;; una suma externa de un monomio con un polinomio ordenado, teniendo
;;; en cuenta una posible cancelación. A partir de aquí se define la
;;; forma normal y su relación de equivalencia inducida. Se demuestran
;;; algunas propiedades importantes como la idempotencia de la
;;; normalización.
;;; ------------------------------------------------------------------
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

(certify-book "fuforma-normal"
	      5
	      nil ;;compile-flg
	      )
|#
(in-package "FUPOL")

;;(include-book "polinomio")
(include-book "fupolinomio"
	      :load-compiled-file nil)

;;; --------------------
;;; Polinomios ordenados
;;; --------------------

;;; Esta función permite averiguar si un monomio debe preceder al
;;; monomio principal de un polinomio ordenado

(defmacro termino-mayor-termino-principal (m p)
  `(or (nulop ,p)
       (FUTER::< (termino (primero ,p)) (termino ,m))))

;;; Reconocedor de polinomios estrictamente ordenado mediante un orden
;;; de términos decreciente y que no poseen monomios nulos

(defun ordenadop (p)
  (and (polinomiop p)
       (or (nulop p)
	   (and (not (FUMON::nulop (primero p)))
		(termino-mayor-termino-principal (primero p) (resto p))
		(ordenadop (resto p))))))

;;; ------------------------------------
;;; Adición de un monomio y un polinomio
;;; ------------------------------------

;;; Suma un monomio a un polinomio

(defun +M (m p)
  (cond ((and (not (monomiop m)) (not (polinomiop p)))
         (nulo))
        ((not (polinomiop p))
         (list m))
        ((not (monomiop m))
         p)
        (t
         (cons m p))))

(defthm |polinomiop(m +M p)|
  (polinomiop (+M m p))
  :rule-classes :type-prescription)

;;; Suma un monomio a un polinomio ordenado

;;; NOTA:
;;;
;;; Hay que garantizar (cosa que probaremos en breve) que si el
;;; polinomio está normalizado, el resultado también.

;; (defun +-monomio (m p)
;;   (cond ((and (not (monomiop m)) (not (polinomiop p)))
;; 	 (nulo))
;; 	((not (monomiop m))
;; 	 p)
;; 	((and (not (polinomiop p)) (MON::nulop m))
;; 	 (nulo))
;; 	((not (polinomiop p))
;; 	 (+M m (nulo)))
;; 	((MON::nulop m)
;; 	 p)
;; 	((nulop p)
;; 	 (+M m (nulo)))
;; 	((TER::= (termino m) (termino (primero p)))
;; 	 (let ((c (COE::+ (coeficiente m) (coeficiente (primero p)))))
;; 	   (if (COE::= c (COE::nulo))
;; 	       (resto p)
;; 	     (+M (MON::+ (primero p) m) (resto p)))))
;; 	((TER::< (termino (primero p)) (termino m))
;; 	 (+M m p))
;; 	(t
;; 	 (+M (primero p) (+-monomio m (resto p))))))

(defun +-monomio (m p)
  (cond ((and (not (monomiop m)) (not (polinomiop p)))
	 (nulo))
	((not (monomiop m))
	 p)
	((and (not (polinomiop p)) (FUMON::nulop m))
	 (nulo))
	((not (polinomiop p))
	 (+M m (nulo)))
	((FUMON::nulop m)
	 p)
	((nulop p)
	 (+M m (nulo)))
	((FUTER::= (termino m) (termino (primero p)))
	 (let ((c (FLD::+ (coeficiente m) (coeficiente (primero p)))))
	   (if (FLD::= c (FLD::0_f))
	       (resto p)
	       (+M (FUMON::+ (primero p) m) (resto p)))))
	((FUTER::< (termino (primero p)) (termino m))
	 (+M m p))
	(t
	 (+M (primero p) (+-monomio m (resto p))))))

;;; Clausura

(defthm polinomiop-+-monomio
  (polinomiop (+-monomio m p))
  :rule-classes (:type-prescription :rewrite))

;;; La suma de un monomio a un polinomio ordenado preserva el orden

(defthm ordenadop-+-monomio-polinomio-ordenado
  (implies (ordenadop p)
	   (ordenadop (+-monomio m p)))
  :rule-classes (:type-prescription :rewrite))

;;; El orden de las operaciones no altera la suma de monomios a un
;;; polinomio ordenado

(defmacro polinomio (m)
  `(list ,m))

(defun  ;;===
  =P (x y)
  "A polynomial is a true list of momomials.
   Determine if x and y are the same list of monomials,
   upto monomial equivalence."
  (if (consp x)
      (and (consp y)
	   (FUMON::= (primero x)
		   (primero y))
	   (=P (resto x)
	       (resto y)))
      (equal x y)))

(defthm
  =P-is-an-equivalence
  (and (booleanp (=P x y))
       (=P x x)
       (implies (=P x y)
		(=P y x))
       (implies (and (=P x y)
		     (=P y z))
		(=P x z)))
  :rule-classes :equivalence)

(defthm
  =P-implies-equal-polinomiop
  (implies (=P p1 p2)
	   (equal (polinomiop p1)
		  (polinomiop p2)))
  :rule-classes :congruence)

(defthm
  |FUMON::=-implies-=P-+M-1|
  (implies (FUMON::= m1 m2)
	   (=P (+M m1 p)
	       (+M m2 p)))
  :rule-classes :congruence)

(defthm
  =P-implies-=P-+M-2
  (implies (=P p1 p2)
	   (=P (+M m p1)
	       (+M m p2)))
  :rule-classes :congruence)

(defthm
  |FUMON::=-implies-=P-+-monomio-1|
  (implies (FUMON::= m1 m2)
	   (=P (+-monomio m1 p)
	       (+-monomio m2 p)))
  :rule-classes :congruence
  :hints (("Subgoal *1/10"
	   :in-theory (disable FUMON::|=-implies-equal-FUTER::<-termino-2b|)
	   :use (:instance FUMON::|=-implies-equal-FUTER::<-termino-2b|
			   (FUMON::x (car p))(FUMON::y1 m1)(FUMON::y2 m2)))
	  ("Subgoal *1/9"
	   :in-theory (disable FUMON::|=-implies-equal-FUTER::<-termino-2b|)
	   :use (:instance FUMON::|=-implies-equal-FUTER::<-termino-2b|
			   (FUMON::x (car p))(FUMON::y1 m1)(FUMON::y2 m2)))))

(defthm
  =P-implies-iff-ordenadop
  (implies (=P p1 p2)
	   (iff (ordenadop p1)
		(ordenadop p2)))
  :rule-classes nil
  :hints (("Subgoal *1/3"
	   :in-theory (disable
		       FUMON::|=-implies-equal-FUTER::<-termino-1a|
		       FUMON::|=-implies-equal-FUTER::<-termino-1b|
		       FUMON::|=-implies-equal-FUTER::<-termino-2a|
		       FUMON::|=-implies-equal-FUTER::<-termino-2b|)
	   :use ((:instance
		  FUMON::|=-implies-equal-FUTER::<-termino-1a|
		  (FUMON::z (car p2))
		  (FUMON::y1 (cadr p1))
		  (FUMON::y2 (cadr p2)))
		 (:instance
		  FUMON::|=-implies-equal-FUTER::<-termino-2a|
		  (FUMON::x (cadr p1))
		  (FUMON::y1 (car p1))
		  (FUMON::y2 (car p2)))))
	  ("Subgoal *1/2"
	   :in-theory (disable
		       FUMON::|=-implies-equal-FUTER::<-termino-1a|
		       FUMON::|=-implies-equal-FUTER::<-termino-1b|
		       FUMON::|=-implies-equal-FUTER::<-termino-2a|
		       FUMON::|=-implies-equal-FUTER::<-termino-2b|)
	   :use ((:instance
		  FUMON::|=-implies-equal-FUTER::<-termino-1a|
		  (FUMON::z (car p2))
		  (FUMON::y1 (cadr p1))
		  (FUMON::y2 (cadr p2)))
		 (:instance
		  FUMON::|=-implies-equal-FUTER::<-termino-2a|
		  (FUMON::x (cadr p1))
		  (FUMON::y1 (car p1))
		  (FUMON::y2 (car p2)))))))

(defthm
  =P-implies-equal-ordenadop
  (implies (=P p1 p2)
	   (equal (ordenadop p1)
		  (ordenadop p2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use =P-implies-iff-ordenadop)))

(defthm
  =P-implies-=P-+-monomio-2a
  (implies (and (=P (double-rewrite p1)
		    (double-rewrite p2))
		(ordenadop (double-rewrite p1)))
	   (equal (=P (+-monomio m p1)
		      (+-monomio m p2))
		  t))
  :hints (("Subgoal *1/12"
	   :in-theory (disable FUMON::=-implies-equal-termino-1
			       FUMON::=-implies-equal-termino-2)
	   :use (:instance
		 FUMON::=-implies-equal-termino-1
		 (FUMON::y1 (car p1))
		 (FUMON::y2 (car p2))))
	  ("Subgoal *1/9"
	   :in-theory (disable FUMON::=-implies-equal-termino-1
			       FUMON::=-implies-equal-termino-2)
	   :use (:instance
		 FUMON::=-implies-equal-termino-1
		 (FUMON::y1 (car p1))
		 (FUMON::y2 (car p2))))
	  ("Subgoal *1/8"
	   :in-theory (disable FUMON::=-implies-equal-termino-1
			       FUMON::=-implies-equal-termino-2)
	   :use (:instance
		 FUMON::=-implies-equal-termino-1
		 (FUMON::y1 (car p1))
		 (FUMON::y2 (car p2))))
	  ("Subgoal *1/7"
	   :in-theory (disable FUMON::=-implies-equal-termino-1
			       FUMON::=-implies-equal-termino-2)
	   :use (:instance
		 FUMON::=-implies-equal-termino-1
		 (FUMON::y1 (car p1))
		 (FUMON::y2 (car p2))))))

(defthm
  =P-implies-=P-+-monomio-2b
  (implies (and (=P (double-rewrite p1)
		    (double-rewrite p2))
		(ordenadop (double-rewrite p2)))
	   (equal (=P (+-monomio m p1)
		      (+-monomio m p2))
		  t)))

;; (defthm |m1 +Mo (m2 +Mo 0) =e m2 +Mo (m1 +Mo 0)|
;;   (implies (nulop p)
;; 	   (equal (+-monomio m1 (+-monomio m2 p))
;; 		  (+-monomio m2 (+-monomio m1 p)))))

(defthm |m1 +Mo (m2 +Mo 0) =P m2 +Mo (m1 +Mo 0)|
  (implies (nulop p)
	   (=P (+-monomio m1 (+-monomio m2 p))
	       (+-monomio m2 (+-monomio m1 p)))))

;; (defthm |t(m1) = t(mp(p)) => m1 +Mo (m2 +Mo p) =e m2 +Mo (m1 +Mo p)|
;;   (implies (and (monomiop m1) (ordenadop p)
;; 		(equal (termino m1) (termino (car p))))
;; 	   (equal (+-monomio m1 (+-monomio m2 p))
;; 		  (+-monomio m2 (+-monomio m1 p)))))

(defthm |t(m1) = t(mp(p)) => m1 +Mo (m2 +Mo p) =P m2 +Mo (m1 +Mo p)|
  (implies (and (monomiop (double-rewrite m1))
		(ordenadop (double-rewrite p))
		(equal (termino m1) (termino (car p))))
	   (=P (+-monomio m1 (+-monomio m2 p))
	       (+-monomio m2 (+-monomio m1 p)))))

;; (defthm |t(mp(p)) < t(m1) => m1 +Mo (m2 +Mo p) =e m2 +Mo (m1 +Mo p)|
;;   (implies (and (monomiop m1) (ordenadop p)
;; 		(TER::< (termino (car p)) (termino m1)))
;; 	   (equal (+-monomio m1 (+-monomio m2 p))
;; 		  (+-monomio m2 (+-monomio m1 p)))))

(defthm |t(mp(p)) < t(m1) => m1 +Mo (m2 +Mo p) =P m2 +Mo (m1 +Mo p)|
  (implies (and (monomiop (double-rewrite m1))
		(ordenadop (double-rewrite p))
		(FUTER::< (termino (car p)) (termino m1)))
	   (=P (+-monomio m1 (+-monomio m2 p))
	       (+-monomio m2 (+-monomio m1 p)))))

;; (defthm |m1 +Mo (m2 +Mo p) =e m2 +Mo (m1 +Mo p)|
;;   (implies (ordenadop p)
;; 	   (equal (+-monomio m1 (+-monomio m2 p))
;; 		  (+-monomio m2 (+-monomio m1 p))))
;;   :hints (("Subgoal *1/9" :in-theory (disable +-monomio))
;; 	  ("Subgoal *1/8" :in-theory (disable +-monomio))
;; 	  ("Subgoal *1/7" :in-theory (disable +-monomio))
;; 	  ("Subgoal *1/6" :in-theory (disable +-monomio))))

(defthm |m1 +Mo (m2 +Mo p) =P m2 +Mo (m1 +Mo p)|
  (implies (ordenadop (double-rewrite p))
	   (=P (+-monomio m1 (+-monomio m2 p))
	       (+-monomio m2 (+-monomio m1 p))))
  :hints (("Subgoal *1/9" :in-theory (disable +-monomio))
	  ("Subgoal *1/8" :in-theory (disable +-monomio))
	  ("Subgoal *1/7" :in-theory (disable +-monomio))
	  ("Subgoal *1/6" :in-theory (disable +-monomio))))

;;; ------------
;;; Forma normal
;;; ------------

;;; Normalización de un polinomio meidante adición de monomios.

;;; NOTA:
;;;
;;; Este es un punto en el que en un futuro se podría trabajar para
;;; mejorar la eficiencia de los algoritmos. Básicamente podemos
;;; entender la normalización de un polinomio como un proceso de
;;; ordenación (con algunas diferencias importantes) y, con éste
;;; símil, el algoritmo que se presenta a continuación correspondería
;;; con un método directo (inserción directa). Cabría la posibilidad
;;; de adaptar algoritmos de ordenación más eficientes (los de Hoare y
;;; Williams serían buenas opciones) para normalizar polinomios.

(defun fn (p)
  (cond ((or (not (polinomiop p)) (nulop p))
	 (nulo))
	(t
	 (+-monomio (primero p) (fn (resto p))))))

;;; Clausura

(defthm polinomiop-fn
  (polinomiop (fn p))
  :rule-classes (:type-prescription :rewrite))

;;; Reconocedor de polinomios normalizados
;;;
;;; NOTA:
;;;
;;; Un polinomio normalizado coincide sintácticamente con su forma
;;; normal.

(defmacro fnp (p)
  `(equal (fn ,p) ,p))

;;; La forma normal de un polinomio es un polinomio ordenado

(defthm ordenadop-fn
  (ordenadop (fn p))
  :rule-classes (:type-prescription :rewrite))

;;; Si un polinomio está ordenado entonces está en forma normal

(defthm fn-ordenado
  (implies (ordenadop (double-rewrite p))
	   (equal (fn p) p)))

;;; Un polinomio está en forma normal si, y sólo si, está ordenado

;;; NOTA:
;;;
;;; Este teorema establece la corrección de la función de
;;; normalización frente a la especificación dada por el hecho de que
;;; un polinomio en forma normal debe tener sus monomios ordenados
;;; decrecientemente y no puede poseer monomios nulos. Al ser la
;;; ordenación estricta, se evita la posibilidad de que aparezcan
;;; monomios con el mismo término.

(defthm fnp-iff-ordenadop
  (iff (fnp p) (ordenadop p)))

;;; El reconocedor de polinomios normalizados reconoce las formas
;;; normales

(defthm fnp-fn
  (fnp (fn p)))

;;; ------------------
;;; Igualdad semántica
;;; ------------------

;;; Igualdad semántica

;;; NOTA:
;;;
;;; Aquí radica una de las aplicaciones de la forma normal: permitir
;;; comprobar si dos polinomios son iguales módulo formas normales.

;; (defun = (p1 p2)
;;   (equal (fn p1) (fn p2)))

(defun = (p1 p2)
  (=P (fn p1) (fn p2)))

;;; La igualdad semántica es una relación de equivalencia

;;; NOTA:
;;;
;;; Esto abre paso al establecimiento de las congruencias entre la
;;; igualdad semántica y las operaciones.

(defthm
  =-is-an-equivalence
  (and (booleanp (= x y))
       (= x x)
       (implies (= x y)
		(= y x))
       (implies (and (= x y)
		     (= y z))
		(= x z)))
  :rule-classes :equivalence)

;;; El orden de las operaciones no altera la suma de monomios a un
;;; polinomio ordenado

(defthm |m1 +M (m2 +M p) = m2 +M (m1 +M p)|
  (= (+M m1 (+M m2 p))
     (+M m2 (+M m1 p))))

(defthm |m1 +Mo (m2 +Mo p) = m2 +Mo (m1 +Mo p)|
  (implies (ordenadop (double-rewrite p))
	   (= (+-monomio m1 (+-monomio m2 p))
	      (+-monomio m2 (+-monomio m1 p)))))

;; (defthm |(a + b) = 0 => a +Mo (b +Mo p) = p|
;;   (implies (and (COE::coeficientep a)
;; 		(COE::coeficientep b)
;; 		(TER::terminop te)
;; 		(ordenadop p)
;; 		(not (COE::= a (COE::nulo)))
;; 		(COE::= (COE::+ a b) (COE::nulo)))
;; 	   (equal (+-monomio (monomio a te) (+-monomio (monomio b te) p))
;; 		  p))
;;   :hints (("Goal"
;; 	   :in-theory (disable COE::|(a + b) + c = a + (b + c)|))
;; 	  ("Subgoal *1/8"
;; 	   :use (:instance COE::|(a + b) + c = a + (b + c)|
;; 			   (COE::a a) (COE::b b)
;; 			   (COE::c (coeficiente (primero p)))))
;; 	  ("Subgoal *1/7"
;; 	   :use (:instance COE::|(a + b) + c = a + (b + c)|
;; 			   (COE::a a) (COE::b b)
;; 			   (COE::c (coeficiente (primero p)))))))

(defthm |(a + b) = 0 => a +Mo (b +Mo p) =P p|
  (implies (and (FLD::fdp (double-rewrite a))
		(FLD::fdp (double-rewrite b))
		(FUTER::terminop te)
		(ordenadop (double-rewrite p))
		(not (FLD::= (double-rewrite a)(FLD::0_f)))
		(FLD::= (FLD::+ (double-rewrite a)(double-rewrite b))(FLD::0_f)))
	   (=P (+-monomio (monomio a te) (+-monomio (monomio b te) p))
	       p))
  :hints (("Goal"
	   :in-theory (disable FLD::|(a + b) + c = a + (b + c)|))
	  ("Subgoal *1/8"
	   :use (:instance FLD::|(a + b) + c = a + (b + c)|
			   (FLD::a a) (FLD::b b)
			   (FLD::c (coeficiente (primero p)))))
	  ("Subgoal *1/7"
	   :use (:instance FLD::|(a + b) + c = a + (b + c)|
			   (FLD::a a) (FLD::b b)
			   (FLD::c (coeficiente (primero p)))))))

;; (defthm |¬(a + b) = 0 => a +Mo (b +Mo p) = (a + b) +Mo p|
;;   (implies (and (COE::coeficientep a)
;; 		(COE::coeficientep b)
;; 		(TER::terminop te)
;; 		(ordenadop p)
;; 		(not (COE::= b (COE::nulo)))
;; 		(not (COE::= (COE::+ a b) (COE::nulo))))
;; 	   (equal (+-monomio (monomio b te) (+-monomio (monomio a te) p))
;; 		  (+-monomio (monomio (COE::+ a b) te) p))))

(defthm |~(a + b) = 0 => a +Mo (b +Mo p) =P (a + b) +Mo p|
  (implies (and (FLD::fdp (double-rewrite a))
		(FLD::fdp (double-rewrite b))
		(FUTER::terminop te)
		(ordenadop (double-rewrite p))
		(not (FLD::= (double-rewrite b)(FLD::0_f)))
		(not (FLD::= (FLD::+ (double-rewrite a)(double-rewrite b))
			     (FLD::0_f))))
	   (=P (+-monomio (monomio b te) (+-monomio (monomio a te) p))
	       (+-monomio (monomio (FLD::+ a b) te) p))))

;;; -----------------------------------------------------------------
;;; Congruencia de la igualdad de polinomios con la suma de monomio y
;;; polinomio
;;; -----------------------------------------------------------------

;;; Primer parámetro

;; (defcong MON::= = (+M m p) 1
;;   :hints (("Goal" :in-theory (enable MON::=))))

(defthm
  |FUMON::=-implies-=-+M-1|
  (implies (FUMON::= m1 m2)
	   (= (+M m1 p)
	      (+M m2 p)))
  :rule-classes :congruence)

;;; Segundo parámetro

;; (defcong = = (+M m p) 2)

(defthm
  =-implies-=-+M-2
  (implies (= p1 p2)
	   (= (+M m p1)
	      (+M m p2)))
  :rule-classes :congruence)

;;; -------------------------------------------------------------
;;; Congruencia de la igualdad de polinomios con la normalizacion
;;; -------------------------------------------------------------

;; (defcong = equal (fn p) 1)

(defthm
  =-implies-=P-fn
  (implies (= p1 p2)
	   (=P (fn p1)
	       (fn p2)))
  :rule-classes :congruence)

;;; ------------------------------------------------------------
;;; Congruencia de la igualdad de polinomios con la suma externa
;;; ------------------------------------------------------------

;;; Primer parámetro

;; (defcong MON::= equal (+-monomio m p) 1
;;   :hints (("Goal" :in-theory (enable MON::=))))

(defthm
  |FUMON::=-implies-=-+-monomio-1|
  (implies (FUMON::= m1 m2)
	   (= (+-monomio m1 p)
	      (+-monomio m2 p)))
  :rule-classes :congruence
  :hints (("Goal"
	   :in-theory (enable FUMON::=))))

;;; NOTA:
;;;
;;; Esta propiedad es expansiva; restringimos su aplicación sintácticamente

(local
  (defthm +-monomio-fn
    (implies (syntaxp (not (and (consp p) (eq (primero p) 'fn))))
	     (= (+-monomio m p) (+-monomio m (fn p))))))

;;; Segundo parámetro

;; (defcong = = (+-monomio m p) 2)

(defthm
  =-implies-=-+-monomio-2
  (implies (= p1 p2)
	   (= (+-monomio m p1)
	      (+-monomio m p2)))
  :rule-classes :congruence)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Additional theory and theorems.
;;  Added by J. Cowles

(defun
  C_= (p)
  (if (consp p)
      (let ((first (primero p)))
	   (if (and (monomiop first)
		    (not (FUMON::nulop first)))
	       (cons (FUMON::C_= first)
		     (C_= (rest p)))
	       (C_= (rest p))))
      nil))

(defthm
  Polinomiop-C_=
  (polinomiop (C_= p))
  :rule-classes :type-prescription)

(defthm
  C_=-=P
  (implies (ordenadop (double-rewrite p))
	   (=P (C_= p) p)))

(defthm
  C_=-=
  (implies (polinomiop (double-rewrite p))
	   (= (C_= p) p)))

(defthm
  =P-implies-equal-C_=
  (implies (=P p1 p2)
	   (equal (C_= p1)
		  (C_= p2)))
  :rule-classes :congruence)
