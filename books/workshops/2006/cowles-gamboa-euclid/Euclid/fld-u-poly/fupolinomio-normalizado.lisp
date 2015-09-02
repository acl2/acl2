; ACL2 Univariate Polynomials over a Field books -- Normalized Polynomials
;; Normalized Univariate Polynomials over a Field
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
;;; Polinomios normalizados
;;;
;;; Autores:
;;;
;;; Inmaculada Medina Bulo
;;; Francisco Palomo Lozano
;;;
;;; Descripción:
;;;
;;; Polinomios normalizados definidos a partir de los polinomios
;;; desnormalizados y de la operación de normalización. Ascenso de las
;;; propiedades de anillo de la representación desnormalizada a la
;;; normalizada.
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

(defpkg "FUNPOL"
  (set-difference-eq *import-symbols*
		     '(rem)))

(certify-book "fupolinomio-normalizado"
	      6
	      nil ;;compile-flg
	      )
|#
(in-package "FUNPOL")

;;(include-book "../polinomios/congruencias-producto")
(include-book "fucongruencias-producto"
	      :load-compiled-file nil)

(in-theory (enable FUPOL::=))

;;; ---------------------------------------------
;;; Reconocedor de los polinomios en forma normal
;;; ---------------------------------------------

(defmacro polinomiop (p)
  `(FUPOL::ordenadop ,p))

(defmacro primero (p)
  `(FUPOL::primero ,p))

(defmacro resto (p)
  `(FUPOL::resto ,p))

;; (defthm booleanp-polinomiop
;;   (ACL2::booleanp (polinomiop p))
;;   :rule-classes :type-prescription)

(defthm booleanp-polinomiop
  (booleanp (polinomiop p))
  :rule-classes :type-prescription)

;;; --------------------------
;;; Elemento neutro de la suma
;;; --------------------------

(defmacro nulop (p)
  `(FUPOL::nulop ,p))

(defun nulo () (FUPOL::nulo))

(defthm polinomiop-nulo
  (polinomiop (nulo))
  :rule-classes :type-prescription)

;;; ----------------------------
;;; Elemento neutro del producto
;;; ----------------------------

(defun identidad () (FUPOL::identidad))

(defthm polinomiop-identidad
  (polinomiop (identidad))
  :hints (("Goal" :in-theory (disable (identidad))))
  :rule-classes :type-prescription)

;;; ----
;;; Suma
;;; ----

(defun + (p q)
  (FUPOL::fn (FUPOL::+ p q)))

(defthm polinomiop-+
  (polinomiop (+ p q))
  :rule-classes :type-prescription)

;;; --------------
;;; Multiplicación
;;; --------------

(defun * (p q)
  (FUPOL::fn (FUPOL::* p q)))

(defthm polinomiop-*
  (polinomiop (* p q))
  :rule-classes :type-prescription)

;;; -----
;;; Resta
;;; -----

(defun - (p)
  (FUPOL::fn (FUPOL::- p)))

(defthm polinomiop--
  (polinomiop (- p))
  :rule-classes :type-prescription)

;;; -----------
;;; Propiedades
;;; -----------

(in-theory (disable FUPOL::+ FUPOL::* FUPOL::-))

(defun
  = (p q)
  (FUPOL::=P p q))

(defthm
  =-is-an-equivalence
  (and (booleanp (= p q))
       (= p p)
       (implies (= p q)
		(= q p))
       (implies (and (= p q)
		     (= q r))
		(= p r)))
  :rule-classes :equivalence)

(defthm
  =-implies-=-+-1
  (implies (= p1 p2)
	   (= (+ p1 q)
	      (+ p2 q)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use (:instance
		 FUPOL::=-implies-=-+-1
		 (FUPOL::p1 p1)
		 (FUPOL::p2 p2)
		 (FUPOL::q q)))))

(defthm
  =-implies-=-+-2
  (implies (= q1 q2)
	   (= (+ p q1)
	      (+ p q2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use (:instance
		 FUPOL::=-implies-=-+-2
		 (FUPOL::q1 q1)
		 (FUPOL::q2 q2)
		 (FUPOL::p p)))))

(defthm
  =-implies-=-*-1
  (implies (= p1 p2)
	   (= (* p1 q)
	      (* p2 q)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use (:instance
		 FUPOL::=-implies-=-*-1
		 (FUPOL::p1 p1)
		 (FUPOL::p2 p2)
		 (FUPOL::q q)))))

(defthm
  =-implies-=-*-2
  (implies (= q1 q2)
	   (= (* p q1)
	      (* p q2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :use (:instance
		 FUPOL::=-implies-=-*-2
		 (FUPOL::q1 q1)
		 (FUPOL::q2 q2)
		 (FUPOL::p p)))))

(defthm
  =-implies-=_-
  (implies (= p1 p2)
	   (= (- p1)
	      (- p2)))
  :rule-classes :congruence)

;; (defthm |p + q = q + p|
;;   (equal (+ p q) (+ q p))
;;   :hints (("Goal"
;; 	   :in-theory (disable POL::|p + q = q + p|)
;; 	   :use (:instance POL::|p + q = q + p| (POL::p p) (POL::q q)))))

(defthm |p + q = q + p|
  (= (+ p q) (+ q p)))

;; (defthm |(p + q) + r = p + (q + r)|
;;   (equal (+ (+ p q) r) (+ p (+ q r)))
;;   :hints (("Goal"
;; 	   :in-theory (disable POL::|p + (q + r) = q + (p + r)|)
;; 	   :use ((:instance POL::|p + (q + r) = q + (p + r)|
;; 			    (POL::p p) (POL::q q) (POL::r r))
;; 		 (:instance POL::|p + q = fn(p) + q|
;; 			    (POL::p (POL::+ p q))
;; 			    (POL::q r))
;; 		 (:instance POL::|p + q = p + fn(q)|
;; 			    (POL::p p)
;; 			    (POL::q (POL::+ q r)))))))

(defthm |(p + q) + r = p + (q + r)|
  (= (+ (+ p q) r) (+ p (+ q r)))
  :hints (("Goal"
	   :in-theory (disable FUPOL::|p + (q + r) = q + (p + r)|)
	   :use ((:instance FUPOL::|p + (q + r) = q + (p + r)|
			    (FUPOL::p p) (FUPOL::q q) (FUPOL::r r))
		 (:instance FUPOL::|p + q = fn(p) + q|
			    (FUPOL::p (FUPOL::+ p q))
			    (FUPOL::q r))
		 (:instance FUPOL::|p + q = p + fn(q)|
			    (FUPOL::p p)
			    (FUPOL::q (FUPOL::+ q r)))))))

;; (defthm |0 + p = p|
;;   (implies (polinomiop p)
;; 	   (equal (+ (nulo) p) p))
;;   :hints (("Goal"
;; 	   :in-theory (disable POL::|0 + p = p|)
;; 	   :use (:instance POL::|0 + p = p| (POL::p p)))))

(defthm |0 + p = p|
  (implies (polinomiop (double-rewrite p))
	   (= (+ (nulo) p) p)))

;; (defthm |p * q = q * p|
;;   (equal (* p q) (* q p))
;;   :hints (("Goal"
;; 	   :in-theory (disable POL::|p * q = q * p|)
;; 	   :use (:instance POL::|p * q = q * p| (POL::p p) (POL::q q)))))

(defthm |p * q = q * p|
  (= (* p q) (* q p)))

;; (defthm |(p * q) * r = p * (q * r)|
;;   (equal (* (* p q) r) (* p (* q r)))
;;   :hints (("Goal"
;; 	   :in-theory (disable POL::|(p * q) * r = p * (q * r)|
;; 			       POL::|p * q = q * p|)
;; 	   :use ((:instance POL::|(p * q) * r = p * (q * r)|
;; 			    (POL::p p) (POL::q q) (POL::r r))
;; 		 (:instance POL::|fn(p) * q = p * q|
;; 			    (POL::p (POL::* p q))
;; 			    (POL::q r))
;; 		 (:instance POL::|p * q = q * p|
;; 			    (POL::q r) (POL::p (POL::* p q)))
;; 		 (:instance POL::|p * q = q * p|
;; 			    (POL::q r) (POL::p (POL::fn (POL::* p q))))
;; 		 (:instance POL::|p * fn(q) = p * q|
;; 			    (POL::p p)
;; 			    (POL::q (POL::* q r)))))))

(defthm |(p * q) * r = p * (q * r)|
  (= (* (* p q) r) (* p (* q r)))
  :hints (("Goal"
	   :in-theory (disable FUPOL::|(p * q) * r = p * (q * r)|
			       FUPOL::|p * q = q * p|)
	   :use ((:instance FUPOL::|(p * q) * r = p * (q * r)|
			    (FUPOL::p p) (FUPOL::q q) (FUPOL::r r))
		 (:instance FUPOL::|fn(p) * q = p * q|
			    (FUPOL::p (FUPOL::* p q))
			    (FUPOL::q r))
		 (:instance FUPOL::|p * q = q * p|
			    (FUPOL::q r) (FUPOL::p (FUPOL::* p q)))
		 (:instance FUPOL::|p * q = q * p|
			    (FUPOL::q r) (FUPOL::p (FUPOL::fn (FUPOL::* p q))))
		 (:instance FUPOL::|p * fn(q) = p * q|
			    (FUPOL::p p)
			    (FUPOL::q (FUPOL::* q r)))))))

;; (defthm |1 * p = p|
;;   (implies (polinomiop p)
;; 	   (equal (* (identidad) p) p))
;;   :hints (("Goal"
;; 	   :in-theory (disable POL::|1 * p = p| (identidad))
;; 	   :use (:instance POL::|1 * p = p| (POL::p p)))))

(defthm |1 * p = p|
  (implies (polinomiop (double-rewrite p))
	   (= (* (identidad) p) p)))

(defthm |p + (- p) = 0|
  (equal (+ p (- p)) (nulo))
  :hints (("Goal"
	   :use ((:instance FUPOL::|p + q = p + fn(q)|
			    (FUPOL::p p)
			    (FUPOL::q (FUPOL::- p)))))))

;; (defthm |p * (q + r) = (p * q) + (p * r)|
;;   (equal (* p (+ q r)) (+ (* p q) (* p r)))
;;   :hints (("Goal"
;; 	   :in-theory (disable POL::|p * (q + r) = (p * q) + (p * r)|
;; 			       POL::|(p * q) * r = p * (q * r)|)
;; 	   :use ((:instance POL::|p * (q + r) = (p * q) + (p * r)|
;; 			    (POL::p p) (POL::q q) (POL::r r))
;; 		 (:instance POL::|fn(p) + fn(q) = p + q|
;; 			    (POL::p (POL::* p q))
;; 			    (POL::q (POL::* p r)))
;; 		 (:instance POL::|p * fn(q) = p * q|
;; 			    (POL::p p)
;; 			    (POL::q (POL::+ q r)))))))

(defthm |p * (q + r) = (p * q) + (p * r)|
  (= (* p (+ q r)) (+ (* p q) (* p r)))
  :hints (("Goal"
	   :in-theory (disable FUPOL::|p * (q + r) = (p * q) + (p * r)|
			       FUPOL::|(p * q) * r = p * (q * r)|)
	   :use ((:instance FUPOL::|p * (q + r) = (p * q) + (p * r)|
			    (FUPOL::p p) (FUPOL::q q) (FUPOL::r r))
		 (:instance FUPOL::|fn(p) + fn(q) = p + q|
			    (FUPOL::p (FUPOL::* p q))
			    (FUPOL::q (FUPOL::* p r)))
		 (:instance FUPOL::|p * fn(q) = p * q|
			    (FUPOL::p p)
			    (FUPOL::q (FUPOL::+ q r)))))))

(defthm |0 * p =e 0|
  (equal (* (nulo) p) (nulo)))

(defthm |p * 0 =e 0|
  (equal (* p (nulo)) (nulo)))

(defthm |- 0 =e 0|
  (equal (- (nulo)) (nulo)))


;;; Mejor con teorías

(in-theory (disable + (+) * (*) - (-) nulo (nulo) identidad (identidad)))

(in-theory (disable = (=)))
;;; -----------------------------------------------------------------------
;;; El inverso debe ser invisible para la primera operación y para sí mismo
;;; -----------------------------------------------------------------------

;; (ACL2::set-invisible-fns-table ((+ -) (- -)))
(set-invisible-fns-table ((+ -) (- -)))

;;; --------------------------------------
;;; Propiedades derivadas de las de anillo
;;; --------------------------------------

;;; Teoremas que resultan de aplicar la conmutatividad a los axiomas

;; (defthm |p + 0 = p|
;;   (implies (polinomiop p)
;; 	   (equal (+ p (nulo)) p)))

(defthm |p + 0 = p|
  (implies (polinomiop (double-rewrite p))
	   (= (+ p (nulo)) p)))

;; (defthm |p * 1 = p|
;;   (implies (polinomiop p)
;; 	   (equal (* p (identidad)) p)))

(defthm |p * 1 = p|
  (implies (polinomiop (double-rewrite p))
	   (= (* p (identidad)) p)))

;; (defthm |(- p) + p = 0|
;;   (equal (+ (- p) p) (nulo)))

(defthm |(- p) + p = 0|
  (= (+ (- p) p) (nulo)))

;; (defthm |(p + q) * r = (p * r) + (q * r)|
;;   (equal (* (+ p q) r) (+ (* p r) (* q r))))

(defthm |(p + q) * r = (p * r) + (q * r)|
  (= (* (+ p q) r) (+ (* p r) (* q r))))

;;; Teorema de cancelación

;; (defthm |p + r = q + r <=> p = q|
;;   (implies (and (polinomiop p) (polinomiop q))
;; 	   (iff (equal (+ p r) (+ q r)) (equal p q)))
;;   :hints (("Goal"
;; 	   :in-theory (disable |p + q = q + p| |p + 0 = p|)
;; 	   :use ((:instance |p + q = q + p| (p (+ p r)) (q (- r)))
;; 	         (:instance |p + q = q + p| (p(- r)) (q (+ q r)))
;; 		 (:instance |p + 0 = p| (p q))
;; 		 |p + 0 = p|))))

(defthm |p + r = q + r <=> p = q|
  (implies (and (polinomiop (double-rewrite p))
		(polinomiop (double-rewrite q)))
	   (iff (= (+ p r) (+ q r)) (= p q)))
  :hints (("Goal"
	   :in-theory (disable |p + q = q + p| |p + 0 = p|)
	   :use ((:instance |p + q = q + p| (p (+ p r)) (q (- r)))
	         (:instance |p + q = q + p| (p(- r)) (q (+ q r)))
		 (:instance |p + 0 = p| (p q))
		 |p + 0 = p|))))

;; (defthm |p + q = 0 <=> q = - p|
;;   (implies (and (polinomiop p) (polinomiop q))
;; 	   (iff (equal (+ p q) (nulo)) (equal q (- p))))
;;   :hints (("Goal"
;; 	   :in-theory (disable |p + r = q + r <=> p = q|)
;; 	   :use (:instance |p + r = q + r <=> p = q| (p q) (q (- p)) (r p)))))

(defthm |p + q = 0 <=> q = - p|
  (implies (and (polinomiop (double-rewrite p))
		(polinomiop (double-rewrite q)))
	   (iff (= (+ p q) (nulo)) (= q (- p))))
  :hints (("Goal"
	   :in-theory (disable |p + r = q + r <=> p = q|)
	   :use (:instance |p + r = q + r <=> p = q| (p q) (q (- p)) (r p)))))

;; (defthm |p * (- q) = - (p * q)|
;;   (equal (* p (- q)) (- (* p q)))
;;   :hints (("Goal"
;; 	   :in-theory (disable |p * (q + r) = (p * q) + (p * r)|)
;; 	   :use (:instance |p * (q + r) = (p * q) + (p * r)|
;; 			   (q (- q)) (r q)))))

(defthm |p * (- q) = - (p * q)|
  (implies (and (polinomiop (double-rewrite p))
		(polinomiop (double-rewrite q)))
	   (= (* p (- q)) (- (* p q))))
  :hints (("Goal"
	   :in-theory (disable |p * (q + r) = (p * q) + (p * r)|
			       |p + q = 0 <=> q = - p|)
	   :use ((:instance |p * (q + r) = (p * q) + (p * r)|
			    (q (- q)) (r q))
		 (:instance |p + q = 0 <=> q = - p|
			    (q (* p (- q)))(p (* p q)))))))

;; (defthm |p + (q + r) = q + (p + r)|
;;   (equal (+ p (+ q r)) (+ q (+ p r)))
;;   :hints (("Goal"
;; 	   :in-theory (disable |(p + q) + r = p + (q + r)|)
;; 	   :use (|(p + q) + r = p + (q + r)|
;; 		 (:instance |(p + q) + r = p + (q + r)| (p q) (q p))))))

(defthm |p + (q + r) = q + (p + r)|
  (= (+ p (+ q r)) (+ q (+ p r)))
  :hints (("Goal"
	   :in-theory (disable |(p + q) + r = p + (q + r)|)
	   :use (|(p + q) + r = p + (q + r)|
		 (:instance |(p + q) + r = p + (q + r)| (p q) (q p))))))

;; (defthm |- (p + q) = (- p) + (- q)|
;;   (equal (- (+ p q)) (+ (- p) (- q)))
;;   :hints (("Goal"
;; 	   :in-theory (disable |p + q = 0 <=> q = - p|)
;; 	   :use ((:instance |p + q = 0 <=> q = - p|
;; 			    (p (+ p q)) (q (+ (- p) (- q))))))))

(defthm |- (p + q) = (- p) + (- q)|
  (= (- (+ p q)) (+ (- p) (- q)))
  :hints (("Goal"
	   :in-theory (disable |p + q = 0 <=> q = - p|)
	   :use ((:instance |p + q = 0 <=> q = - p|
			    (p (+ p q)) (q (+ (- p) (- q))))))))

;;; Idempotencia del inverso

;; (defthm |- (- p) = p|
;;   (implies (polinomiop p)
;; 	   (equal (- (- p)) p))
;;   :hints (("Goal"
;; 	   :in-theory (disable |p + q = 0 <=> q = - p|)
;; 	   :use (:instance |p + q = 0 <=> q = - p| (p (- p)) (q p)))))

(defthm |- (- p) = p|
  (implies (polinomiop (double-rewrite p))
	   (= (- (- p)) p))
  :hints (("Goal"
	   :in-theory (disable |p + q = 0 <=> q = - p|)
	   :use (:instance |p + q = 0 <=> q = - p| (p (- p)) (q p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Additional theory and theorems by J. Cowles

(defthm |(- p) * q = - (p * q)|
  (implies (and (polinomiop (double-rewrite p))
		(polinomiop (double-rewrite q)))
	   (= (* (- p) q) (- (* p q)))))

(defthm |(- p) * (- q) = p * q|
  (implies (and (polinomiop (double-rewrite p))
		(polinomiop (double-rewrite q)))
	   (= (* (- p) (- q)) (* p q))))

(defthm |p * (q * r) = q * (p * r)|
  (= (* p (* q r)) (* q (* p r)))
  :hints (("Goal"
	   :in-theory (disable |(p * q) * r = p * (q * r)|)
	   :use (|(p * q) * r = p * (q * r)|
		 (:instance |(p * q) * r = p * (q * r)| (p q) (q p))))))

(defun
  C_= (p)
  (FUPOL::fn (FUPOL::C_= p)))

(defthm
  Polinomiop-C_=
  (polinomiop (C_= p))
  :rule-classes :type-prescription)

(in-theory (enable = (=)))

(defthm
  C_=-=
  (implies (polinomiop (double-rewrite p))
	   (= (C_= p) p)))

(defthm
  =-implies-equal-C_=
  (implies (= p1 p2)
	   (equal (C_= p1)
		  (C_= p2)))
  :rule-classes :congruence)

(defthm
  |=-implies-equal-FUPOL::ordenadop|
  (implies (= p1 p2)
	   (equal (FUPOL::ordenadop p1)
		  (FUPOL::ordenadop p2)))
  :rule-classes :congruence)

(defthm
  |p1 * p2 = 0 <=> p1 = 0 or p2 = 0|
  (implies (and (polinomiop (double-rewrite p1))
		(polinomiop (double-rewrite p2)))
	   (equal (= (* p1 p2)(nulo))
		  (or (= p1 (nulo))
		      (= p2 (nulo)))))
  :hints (("Goal"
	   :in-theory (e/d (* (*) nulo)
			   (FUPOL::|fn(p1 * p2) = 0 <=> p1 = 0 or p2 = 0|))
	   :use (:instance
		 FUPOL::|fn(p1 * p2) = 0 <=> p1 = 0 or p2 = 0|
		 (FUPOL::p1 p1)
		 (FUPOL::p2 p2)))))

(in-theory (disable = (=)))
