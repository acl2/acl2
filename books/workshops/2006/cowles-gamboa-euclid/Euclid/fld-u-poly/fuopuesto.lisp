; ACL2 Univariate Polynomials over a Field books -- Unary Minus
;; Unary Minus of Univariate Polynomials over a Field
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
;;; ------------------------------------------------------------------
;;; Opuesto de polinomios
;;;
;;; Autores:
;;;
;;; Inmaculada Medina Bulo
;;; Francisco Palomo Lozano
;;;
;;; Descripción:
;;;
;;; Desarrollo del opuesto de un polinomio, que se define monomio a
;;; monomio. Su corrección se prueba demostrando que la función que lo
;;; calcula produce el inverso aditivo. Para que éstas y otras
;;; propiedades sean incondicionales (carezcan de hipótesis) se
;;; completa cuidadosamente la definición de la función. Se demuestra
;;; que los polinomios con las operaciones de suma y opuesto forman un
;;; grupo conmutativo.
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

(certify-book "fuopuesto"
	      5
	      nil ;;compile-flg
	      )
|#
(in-package "FUPOL")

;;(include-book "congruencias-suma")
(include-book "fucongruencias-suma"
	      :load-compiled-file nil)

;;; ---------------------
;;; Opuesto de polinomios
;;; ---------------------

;;; La siguiente desactivación es necesaria para la verificación de la
;;; protección del opuesto

(in-theory (disable FUMON::monomio-coeficiente-termino))

(defun - (p)
  (cond ((or (not (polinomiop p)) (nulop p))
	 (nulo))
	(t
	 (+M (FUMON::- (primero p)) (- (resto p))))))

(in-theory (enable FUMON::monomio-coeficiente-termino))

;;; Clausura

(defthm polinomiop--
  (polinomiop (- p))
  :rule-classes (:type-prescription
		 :rewrite))

;;; Distributividad respecto de la suma de monomio y polinomio

(defthm |- p =e (- mp(p)) +M (- (resto(p)))|
  (implies (and (polinomiop (double-rewrite p))
		(not (nulop p)))
	   (equal (- p)
		  (+M (FUMON::- (primero p)) (- (resto p))))))

;;; Inverso de la suma

(defthm |m +M (- m +M 0) = 0|
  (implies (monomiop (double-rewrite m))
	   (= (+M m (+M (FUMON::- m) (nulo)))
	      (nulo))))

(defthm |p + (- p) = 0|
  (= (+ p (- p)) (nulo))
  :hints (("Goal"
	   :in-theory (disable = + +M - FUMON::-)
	   :induct (fn p))
	  ("Subgoal *1/1" :in-theory (enable = + +M))
	  ("Subgoal *1/2"
	   :use ((:instance |p + q = q + p|
			    (p (+M (FUMON::- (primero p)) (- (resto p))))
			    (q (resto p)))))))

;;; Distributividad respecto de la suma en orden de monomio y
;;; polinomio

;; (defthm |- (m +Mo p) =e (- m) +Mo (- p)|
;;   (implies (and (monomiop (double-rewrite m))
;; 		(polinomiop (double-rewrite p)))
;; 	   (equal (- (+-monomio m p))
;; 		  (+-monomio (FUMON::- m) (- p)))))

(defthm |- (m +Mo p) =P (- m) +Mo (- p)|
  (implies (and (monomiop (double-rewrite m))
		(polinomiop (double-rewrite p)))
	   (=P (- (+-monomio m p))
	       (+-monomio (FUMON::- m) (- p)))))

;;; -------------------------------------------------------
;;; Congruencia de la igualdad de polinomios con el opuesto
;;; -------------------------------------------------------

(defthm
  |FUMON::nulop_-|
  (implies (monomiop (double-rewrite m))
	   (equal (FUMON::nulop (FUMON::- m))
		  (FUMON::nulop m))))

(defthm
  =P-implies-=P_-
  (implies (=P p1 p2)
	   (=P (- p1)
	       (- p2)))
  :rule-classes :congruence)

(defthm
  Ordenadop_-
  (implies (ordenadop p)
	   (ordenadop (- p))))

;; (local
;;   (defthm |fn(- p) = - fn(p)|
;;     (equal (fn (- p)) (- (fn p)))
;;     :hints (("Goal" :in-theory (disable MON::- )))))

(local
  (defthm |fn(- p) =P - fn(p)|
    (=P (fn (- p)) (- (fn p)))
    :hints (("Goal" :in-theory (disable FUMON::- )))))

;; (defcong = = (- p) 1)

(defthm
  =-implies-=_-
  (implies (= p1 p2)
	   (= (- p1)
	      (- p2)))
  :rule-classes :congruence)

;;; ---------------
;;; Desactivaciones
;;; ---------------

(local (in-theory (disable polinomiop = + -)))

;;; -----------------------------------------------------------------------
;;; El inverso debe ser invisible para la primera operación y para sí mismo
;;; -----------------------------------------------------------------------
(ACL2::set-invisible-fns-table ((+ -) (- -)))


;;; El opuesto de una suma de polinomios es la suma de los opuestos.

(defthm |p + r = q + r <=> p = q|
  (implies (and (polinomiop (double-rewrite p))
		(polinomiop (double-rewrite q)))
	   (iff (= (+ p r) (+ q r)) (= p q)))
  :hints (("Goal"
	   :in-theory (disable |p + q = q + p| |p + 0 = p|)
	   :use ((:instance |p + q = q + p| (p (+ p r)) (q (- r)))
	         (:instance |p + q = q + p| (p (- r)) (q (+ q r)))
		 (:instance |p + 0 = p| (p q))
		 |p + 0 = p|))))

(local
  (defthm |p + q = q <=> p = 0|
    (implies (and (polinomiop (double-rewrite p))
		  (polinomiop (double-rewrite q)))
	     (iff (= (+ p q) q) (= p (nulo))))
    :hints (("Goal"
	     :in-theory (disable |p + r = q + r <=> p = q|)
	     :use (:instance |p + r = q + r <=> p = q| (q (nulo)) (r q))))))

(local
  (defthm |p + q = 0 <=> q = - p|
    (implies (and (polinomiop (double-rewrite p))
		  (polinomiop (double-rewrite q)))
	     (iff (= (+ p q) (nulo)) (= q (- p))))
    :hints (("Goal"
	     :in-theory (disable |p + r = q + r <=> p = q|)
	     :use (:instance |p + r = q + r <=> p = q| (p q) (q (- p)) (r p))))))

;;; Mezcla de asociatividad y conmutatividad

(defthm |p + (q + r) = q + (p + r)|
  (= (+ p (+ q r)) (+ q (+ p r)))
  :hints (("Goal"
	   :in-theory (disable |(p + q) + r = p + (q + r)|)
	   :use (|(p + q) + r = p + (q + r)|
		 (:instance |(p + q) + r = p + (q + r)| (p q) (q p))))))

;;; Idempotencia del inverso

(defthm |- (- p) = p|
  (implies (polinomiop (double-rewrite p))
	   (= (- (- p)) p))
  :hints (("Goal"
	   :in-theory (disable |p + q = 0 <=> q = - p|)
	   :use (:instance |p + q = 0 <=> q = - p| (p (- p)) (q p)))))

;;; Distributividad de la inversa sobre la primera operación

(defthm |- (p + q) = (- p) + (- q)|
  (= (- (+ p q)) (+ (- p) (- q)))
  :hints (("Goal"
	   :in-theory (disable |p + q = 0 <=> q = - p|)
	   :use (:instance |p + q = 0 <=> q = - p| (p (+ p q)) (q (+ (- p) (- q)))))))
