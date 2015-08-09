; ACL2 Univariate Polynomials over a Field books -- (Unnormalized) Polynomials
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
;;; -------------------------------------------------------------------
;;; Polinomios
;;;
;;; Autores:
;;;
;;; Inmaculada Medina Bulo
;;; Francisco Palomo Lozano
;;;
;;; Descripción:
;;;
;;; Representación abstracta de los polinomios mediante listas propias
;;; de ACL2 formadas por monomios que contienen coeficientes y
;;; términos abstractos.
;;; -------------------------------------------------------------------
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

(certify-book "fupolinomio"
	      5
	      nil ;;compile-flg
	      )
|#
(in-package "FUPOL")

;;(include-book "monomio")
(include-book "fumonomio"
	      :load-compiled-file nil)

;;; ---------
;;; Funciones
;;; ---------

;;; Accesores

(defmacro primero (p)
  `(first ,p))

(defmacro resto (p)
  `(rest ,p))

;;; Reconocedor

(defun polinomiop (p)
  (if (atom p)
      (equal p nil)
    (and (monomiop (primero p)) (polinomiop (resto p)))))

;;; Polinomio nulo en forma normal

;;; NOTA:
;;;
;;; Posteriormente definiremos la igualdad semántica entre
;;; polinomios. Entonces, esta definición corresponderá al
;;; representante canónico de la clase de equivalencia formada por los
;;; polinomios nulos.

(defmacro nulo () nil)

;;; NOTA:
;;;
;;; La siguiente versión se emplea en los casos base de las funciones
;;; recursivas que trabajan con polinomios.

(defmacro nulop (p)
  `(atom ,p))

;;; -----------
;;; Propiedades
;;; -----------

;;; Clausura

(defthm polinomiop-resto
  (implies (polinomiop p)
	   (polinomiop (resto p)))
  :rule-classes :type-prescription)
