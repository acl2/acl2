; ACL2 Univariate Polynomials over a Field books -- Monomials
;; Monomials for Univariate polynomials over a Field
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

;;; Modified by John R. Cowles

;;   Last modified July 2006 (for ACL2 Version 3.0).

;;  Based on
;;; ------------------------------------------------------------------
;;; Monomios con coeficientes y términos abstractos
;;;
;;; Autores:
;;;
;;; Inmaculada Medina Bulo
;;; Francisco Palomo Lozano
;;;
;;; Descripción:
;;;
;;; Pares coeficiente-término. Se define una igualdad semántica, ya
;;; que dos monomios con coeficiente nulo han de ser interpretados
;;; como el mismo, aunque tengan distinto término. Orden de monomios
;;; heredado de los términos.
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

(certify-book "fumonomio"
	      4
	      nil ;;compile-flg
	      )
|#
(in-package "FUMON")

;; (include-book "coeficiente")
;; (include-book "termino")
(include-book "coe-fld"
	      :load-compiled-file nil)
(include-book "futermino"
	      :load-compiled-file nil)

;;; ---------
;;; Funciones
;;; ---------

;;; Etiqueta que marca el principio de las funciones

(deflabel principio-funciones)

;;; Reconocedor

;; (defun monomiop (a)
;;   (and (consp a)
;;        (coeficientep (first a))
;;        (terminop (rest a))))

(defun monomiop (a)
  (and (consp a)
       (fdp (first a))
       (terminop (rest a))))

;;; Constructor

(defun monomio (c e)
  (cons c e))

;;; Accesores

;; (defun coeficiente (a)
;;   (if (not (monomiop a))
;;       (COE::nulo)
;;     (first a)))

(defun coeficiente (a)
  (if (not (monomiop a))
      (FLD::0_f)
      (first a)))

(defun termino (a)
  (if (or (not (consp a)) (not (terminop (rest a)))) ;(not (monomiop a))
      (FUTER::uno)
      (rest a)))

;;; Monomio nulo

;; (defun nulo ()
;;   (monomio (COE::nulo) (TER::uno)))

(defun nulo ()
  (monomio (FLD::0_f) (FUTER::uno)))

;;; Reconocedor de monomios nulos

;; (defun nulop (a)
;;   (COE::= (coeficiente a) (COE::nulo)))

(defun nulop (a)
  (FLD::= (coeficiente a) (FLD::0_f)))

;;; Neutro de la operación

;; (defun identidad ()
;;   (monomio (COE::identidad) (TER::uno)))

(defun identidad ()
  (monomio (FLD::1_f) (FUTER::uno)))

;;; Operación

;; (defun * (a b)
;;   (monomio (COE::* (coeficiente a) (coeficiente b))
;; 	   (TER::* (termino a) (termino b))))

(defun * (a b)
  (monomio (FLD::* (coeficiente a) (coeficiente b))
	   (FUTER::* (termino a) (termino b))))

;;; Igualdad semántica

;; (defun = (a b)
;;   (or (and (not (monomiop a)) (not (monomiop b)))
;;       (and (monomiop a) (monomiop b)
;; 	   (nulop a) (nulop b))
;;       (and (monomiop a) (monomiop b)
;; 	   (COE::= (coeficiente a) (coeficiente b))
;; 	   (TER::= (termino a) (termino b)))))

(defun = (a b)
  (or (and (not (monomiop a)) (not (monomiop b)))
      (and (monomiop a) (monomiop b)
	   (nulop a) (nulop b))
      (and (monomiop a) (monomiop b)
	   (FLD::= (coeficiente a) (coeficiente b))
	   (FUTER::= (termino a) (termino b)))))

;;; Igualdad de los términos subyacentes

(defmacro =T (a b)
  `(FUTER::= (termino ,a) (termino ,b)))

;;; Orden de monomios

(defmacro < (a b)
  `(FUTER::< (termino ,a) (termino ,b)))

;;; Inmersión en los ordinales

(defmacro monomio->ordinal (a)
  `(FUTER::termino->ordinal (termino ,a)))

;;; -----------------------
;;; Teoría de las funciones
;;; -----------------------

(deftheory funciones
  (set-difference-theories (universal-theory :here)
			   (universal-theory 'principio-funciones)))

;;; -----------
;;; Propiedades
;;; -----------

;;; Clausura de las operaciones

;; (defthm monomiop-monomio
;;   (implies (and (coeficientep c)
;; 		(terminop e))
;; 	   (monomiop (monomio c e)))
;;   :rule-classes (:type-prescription :generalize))

(defthm monomiop-monomio
  (implies (and (fdp c)
		(terminop e))
	   (monomiop (monomio c e)))
  :rule-classes (:type-prescription :generalize))

;; (defthm coeficientep-coeficiente
;;  (implies (monomiop m)
;; 	   (coeficientep (coeficiente m)))
;;   :rule-classes (:type-prescription :generalize))

(defthm coeficientep-coeficiente
 (implies (monomiop m)
	   (fdp (coeficiente m)))
  :rule-classes (:type-prescription :generalize))

(defthm terminop-termino
  (implies (monomiop m)
	   (FUTER::terminop (termino m)))
  :rule-classes (:type-prescription :generalize))

(defthm monomiop-identidad
  (monomiop (identidad))
  :hints (("Goal" :in-theory (disable (identidad))))
  :rule-classes (:type-prescription :generalize))

(defthm monomiop-*
  (implies (and (monomiop a) (monomiop b))
	   (monomiop (* a b)))
  :rule-classes (:type-prescription :generalize))

;;; Equivalencia

;;(defequiv =)
(defthm =-is-an-equivalence
  (and (booleanp (= x y))
       (= x x)
       (implies (= x y)
		(= y x))
       (implies (and (= x y)
		     (= y z))
		(= x z)))
  :rule-classes :equivalence)

;;; Congruencias

;;(defcong = COE::= (coeficiente m) 1)
(defthm |=-implies-FLD::=-coeficiente|
  (implies (= y1 y2)
	   (FLD::= (coeficiente y1)
		   (coeficiente y2)))
  :rule-classes :congruence)

(defthm ;;===
  =-implies-equal-termino-1
  (implies (and (= (double-rewrite y1)
		   (double-rewrite y2))
		(not (nulop y1)))
	   (equal (equal (termino y1)
			 (termino y2))
		  t)))

(defthm ;;===
  =-implies-equal-termino-2
  (implies (and (= (double-rewrite y1)
		   (double-rewrite y2))
		(not (nulop y2)))
	   (equal (equal (termino y1)
			 (termino y2))
		  t)))

;;(defcong = = (* a b) 1)
(defthm =-implies-=-*-1
  (implies (= y1 y2)
	   (= (* y1 z)
	      (* y2 z)))
  :rule-classes :congruence)

;;(defcong = = (* a b) 2)
(defthm =-implies-=-*-2
  (implies (= y1 y2)
	   (= (* x y1)
	      (* x y2)))
  :rule-classes :congruence)

;;; Conmutatividad de la operación

(defthm |a * b = b * a|
  (implies (and (monomiop a) (monomiop b))
	   (= (* a b) (* b a))))

;;; Asociatividad de la operación

;; (defthm |(a * b) * c = a * (b * c)|
;;   (implies (and (monomiop a) (monomiop b) (monomiop c))
;; 	   (= (* (* a b) c) (* a (* b c))))
;;   :hints (("Goal"
;; 	   :in-theory (disable (nulo) COE::|a + b = b + a|))))

(defthm |(a * b) * c = a * (b * c)|
  (implies (and (monomiop a) (monomiop b) (monomiop c))
	   (= (* (* a b) c) (* a (* b c))))
  :hints (("Goal"
	   :in-theory (disable (nulo) FLD::|a + b = b + a|))))

;;; Neutro de la operación

(defthm |1 * b = b|
  (implies (monomiop b)
	   (= (* (identidad) b) b))
  :hints (("Goal" :in-theory (disable (identidad)))))

;;; Cancelativo de la operación

(defthm |a = 0 => a * b = 0|
  (implies (and (monomiop a) (monomiop b) (nulop a))
	   (nulop (* a b)))
  :hints (("Goal" :in-theory (disable (nulo)))))

;;; Coeficiente y término del constructor

;; (defthm coeficiente-monomio
;;   (implies (and (coeficientep c) (terminop e))
;; 	   (COE::= (coeficiente (monomio c e)) c)))

(defthm coeficiente-monomio
  (implies (and (fdp (double-rewrite c)) (terminop e))
	   (FLD::= (coeficiente (monomio c e)) c)))

;; (defthm termino-monomio
;;   (implies (and (coeficientep c) (terminop e))
;; 	   (TER::= (termino (monomio c e)) e)))

(defthm termino-monomio
  (implies (and (fdp (double-rewrite c)) (terminop e))
	   (FUTER::= (termino (monomio c e)) e)))

;;; Eliminación de destructores

(defthm monomio-coeficiente-termino
  (implies (monomiop m)
	   (equal (monomio (coeficiente m) (termino m)) m))
  :rule-classes (:rewrite :elim))

;;; Coeficiente y término de la operación

;; (defthm coeficiente-*
;;   (COE::= (coeficiente (* a b))
;; 	  (COE::* (coeficiente a) (coeficiente b)))
;;   :hints (("Goal" :in-theory (disable (nulo)))))

(defthm coeficiente-*
  (FLD::= (coeficiente (* a b))
	  (FLD::* (coeficiente a) (coeficiente b)))
  :hints (("Goal" :in-theory (disable (nulo)))))

(defthm termino-*
  (FUTER::= (termino (* a b))
	    (FUTER::* (termino a) (termino b))))

;;; Buena fundamentación

(defthm buena-fundamentacion-<-M
  (and (implies (monomiop a)
		(o-p (monomio->ordinal a)))
       (implies (and (monomiop a) (monomiop b)
		     (< a b))
		(o< (monomio->ordinal a) (monomio->ordinal b)))))

(defthm ;;===
  |=-implies-equal-FUTER::termino->ordinal-terminino-1|
  (implies (and (= (double-rewrite y1)
		   (double-rewrite y2))
		(not (nulop y1)))
	   (equal (equal (FUTER::termino->ordinal (termino y1))
			 (FUTER::termino->ordinal (termino y2)))
		  t)))

(defthm ;;===
  |=-implies-equal-FUTER::termino->ordinal-terminino-2|
  (implies (and (= (double-rewrite y1)
		   (double-rewrite y2))
		(not (nulop y2)))
	   (equal (equal (FUTER::termino->ordinal (termino y1))
			 (FUTER::termino->ordinal (termino y2)))
		  t)))

(defthm ;;===
  |=-implies-equal-FUTER::<-termino-1a|
  (implies (and (= (double-rewrite y1)
		   (double-rewrite y2))
		(not (nulop y1)))
	   (equal (equal (FUTER::< (termino y1)(termino z))
			 (FUTER::< (termino y2)(termino z)))
		  t)))

(defthm ;;===
  |=-implies-equal-FUTER::<-termino-1b|
  (implies (and (= (double-rewrite y1)
		   (double-rewrite y2))
		(not (nulop y2)))
	   (equal (equal (FUTER::< (termino y1)(termino z))
			 (FUTER::< (termino y2)(termino z)))
		  t)))

(defthm ;;===
  |=-implies-equal-FUTER::<-termino-2a|
  (implies (and (= (double-rewrite y1)
		   (double-rewrite y2))
		(not (nulop y1)))
	   (equal (equal (FUTER::< (termino x)(termino y1))
			 (FUTER::< (termino x)(termino y2)))
		  t)))

(defthm ;;===
  |=-implies-equal-FUTER::<-termino-2b|
  (implies (and (= (double-rewrite y1)
		   (double-rewrite y2))
		(not (nulop y2)))
	   (equal (equal (FUTER::< (termino x)(termino y1))
			 (FUTER::< (termino x)(termino y2)))
		  t)))

;;; Definiciones extras

;;; Suma

;; (defun + (a b)
;;   (monomio (COE::+ (coeficiente a) (coeficiente b))
;; 	   (termino a)))

(defun + (a b)
  (monomio (FLD::+ (coeficiente a) (coeficiente b))
	   (termino a)))

;;; Negación

;; (defun - (a)
;;   (monomio (COE::- (coeficiente a)) (termino a)))

(defun - (a)
  (monomio (FLD::- (coeficiente a)) (termino a)))

;;; Inverso de la suma

(defthm |a + (- a) = 0|
  (implies (monomiop a)
	   (= (+ a (- a)) (nulo)))
  :hints (("Goal" :in-theory (disable (nulo)))))

;;; --------
;;; Teoremas
;;; --------

;;; Teoremas que resultan de aplicar la conmutatividad a los axiomas

(defthm |b * 1 = b|
  (implies (monomiop b)
	   (= (* b (identidad)) b))
  :hints (("Goal" :in-theory (disable (identidad)))))

(defthm |a = 0 => b * a = 0|
  (implies (nulop a)
	   (nulop (* b a))))

;;; Complemento a la conmutatividad y la asociatividad de la operación

(defthm |a * (b * c) = b * (a * c)|
  (implies (and (monomiop a) (monomiop b) (monomiop c))
	   (= (* a (* b c)) (* b (* a c))))
  :hints (("Goal"
	   :in-theory (disable |(a * b) * c = a * (b * c)|)
	   :use (|(a * b) * c = a * (b * c)|
		 (:instance |(a * b) * c = a * (b * c)| (a b) (b a))))))

(defthm |- (a + b) = (- a) + (- b)|
  (implies (and (monomiop a) (monomiop b))
	   (= (- (+ a b)) (+ (- a) (- b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Additional Theorems
;;   added by J. Cowles

(defthm
  |FLD::=-implies-=-monomio-1|
  (implies (FLD::= y1 y2)
	   (= (monomio y1 z)
	      (monomio y2 z)))
  :rule-classes :congruence)

(defthm
  =-implies-iff-monomiop
  (implies (= y1 y2)
	   (iff (monomiop y1)
		(monomiop y2)))
  :rule-classes :congruence)

(defun
  C_= (x)
  (if (monomiop x)
      (if (nulop x)
	  (monomio (FLD::C_= (coeficiente x))
		   (FUTER::uno))
	  (monomio (FLD::C_= (coeficiente x))
		   (termino x)))
      t))

(defthm
  C_=-=
  (implies (monomiop (double-rewrite x))
	   (= (C_= x) x)))

(defthm
  =-implies-equal-C_=
  (implies (= y1 y2)
	   (equal (C_= y1)
		  (C_= y2)))
  :rule-classes :congruence)

(defthm
  =-implies-=-+-2
  (implies (= m1 m2)
	   (= (+ m m1)
	      (+ m m2)))
  :rule-classes :congruence)

(defthm
  =-implies-=_-
  (implies (= m1 m2)
	   (= (- m1)
	      (- m2)))
  :rule-classes :congruence)

(defthm
  =-implies-=-+-1a
  (implies (and (= (double-rewrite m1)
		   (double-rewrite m2))
		(not (nulop m1)))
	   (equal (= (+ m1 m)
		     (+ m2 m))
		  t)))

(defthm
  =-implies-=-+-1b
  (implies (and (= (double-rewrite m1)
		   (double-rewrite m2))
		(not (nulop m2)))
	   (equal (= (+ m1 m)
		     (+ m2 m))
		  t)))

(defthm
  |nulop a * b iff (nulop a) or (nulop b)|
  (equal (nulop (* a b))
	 (or (nulop a)
	     (nulop b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; ++++++++++++++++++++++++++
;;; + Barrera de abstracción +
;;; ++++++++++++++++++++++++++

;;; NOTA:
;;;
;;; A partir de aquí se procederá por aplicación de las propiedades

(in-theory (disable funciones))
(in-theory (enable nulop (nulop) (:type-prescription nulop)))
