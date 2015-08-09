; ACL2 Univariate Polynomials over a Field books -- Polynomial Sums
;; Sums of Univariate Polynomials over a Field
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
;;; ----------------------------------------------------------------
;;; Suma de polinomios
;;;
;;; Autores:
;;;
;;; Inmaculada Medina Bulo
;;; Francisco Palomo Lozano
;;;
;;; Descripción:
;;;
;;; Desarrollo de la suma de polinomios definida simplemente como la
;;; concatenación de las listas de monomios que los integran. Las
;;; propiedades de la concatenación de listas permiten establecer la
;;; base para realizar demostraciones de propiedades sobre los
;;; polinomios más complicadas que incorporan la igualdad
;;; semántica. Se demuestra que los polinomios con la operación de
;;; suma forman un monoide conmutativo.
;;; ----------------------------------------------------------------
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

(certify-book "fusuma"
	      5
	      nil ;;compile-flg
	      )
|#
(in-package "FUPOL")

;;(include-book "forma-normal")
(include-book "fuforma-normal"
	      :load-compiled-file nil)

;;; ------------------
;;; Suma de polinomios
;;; ------------------

(defun + (p q)
  (cond ((and (not (polinomiop p)) (not (polinomiop q)))
	 (nulo))
	((not (polinomiop p))
	 q)
	((not (polinomiop q))
	 p)
	(t
	 (append p q))))

;;; Clausura

(defthm polinomiop-append
  (implies (and (polinomiop (double-rewrite p))
		(polinomiop (double-rewrite q)))
	   (polinomiop (append p q)))
  :rule-classes (:type-prescription :rewrite))

(defthm polinomiop-+
  (polinomiop (+ p q))
  :rule-classes (:type-prescription :rewrite))

;;; ----------------------
;;; Propiedades de la suma
;;; ----------------------

;;; Neutro

(defthm |(0 p) = p|
  (equal (append (nulo) p) p))

(defthm |0 + p = p|
  (= (+ (nulo) p) p))

(defthm |(p 0) = p|
  (implies (polinomiop (double-rewrite p))
	   (equal (append p (nulo)) p)))

(defthm |p + 0 = p|
  (= (+ p (nulo)) p))

;;; Asociatividad

(defthm |(m +M p) + q =P m +M (p + q)|
  (equal (+ (+M m p) q) (+M m (+ p q)))
  :hints (("Goal"
	   :use  polinomiop-append)))

(defthm |p + q =e mp(p) +M (resto(p) + q)-1|
  (implies (and (polinomiop p)
		(not (nulop p)))
	   (equal (+ p q) (+M (primero p) (+ (resto p) q))))
  :rule-classes nil)

(defthm |p + q =e mp(p) +M (resto(p) + q)|
  (implies (and (polinomiop (double-rewrite p))
		(not (nulop p)))
	   (equal (+ p q) (+M (primero p) (+ (resto p) q))))
  :hints (("Goal"
	   :use |p + q =e mp(p) +M (resto(p) + q)-1|)))

(local (in-theory (disable = + +M)))

(defthm |(p + q) + r = p + (q + r)|
  (= (+ (+ p q) r) (+ p (+ q r)))
  :hints (("Goal" :induct (fn p))
	  ("Subgoal *1/1" :in-theory (enable = + +M))))

;;; Conmutatividad

(defthm |q + p = mp(p) +M (q + resto(p))|
  (implies (and (polinomiop (double-rewrite p))
		(not (nulop p)))
	   (= (+ q p) (+M (primero p) (+ q (resto p)))))
  :hints (("Goal" :induct (fn q))
	  ("Subgoal *1/1" :in-theory (enable = + +M))))

(defthm |p + q = q + p|
  (= (+ p q) (+ q p))
  :hints (("Goal" :induct (fn p))
	  ("Subgoal *1/1" :in-theory (enable = + +M))))
