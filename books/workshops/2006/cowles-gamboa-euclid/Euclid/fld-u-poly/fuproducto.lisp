; ACL2 Univariate Polynomials over a Field books -- Polynomial Products
;; Products of Univariate Polynomials over a Field
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

; Modified by Matt Kaufmann for ACL2 Version 3.1 because
; SBCL complains about LISP::.

;; Based on
;;; ---------------------------------------------------------------
;;; Producto de polinomios
;;;
;;; Autores:
;;;
;;; Inmaculada Medina Bulo
;;; Francisco Palomo Lozano
;;;
;;; Descripción:
;;;
;;; Desarrollo del producto externo de un monomio por un polinomio y
;;; del producto de polinomios. Las funciones se completan
;;; cuidadosamente, de lo contrario, no es posible establecer las
;;; congruencias, ya que éstas no pueden contener hipótesis. Se
;;; demuestra que los polinomios con el producto forman un monoide
;;; conmutativo y que el producto distribuye respecto de la suma,
;;; completándose con esto la demostración de las propiedades del
;;; anillo de polinomios.
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

(certify-book "fuproducto"
	      5
	      nil ;;compile-flg
	      )
|#
(in-package "FUPOL")

;; (include-book "opuesto")
(include-book "fuopuesto"
	      :load-compiled-file nil)

;;; ------
;;; Neutro
;;; ------

(defmacro identidad ()
  `(+M (FUMON::identidad) (nulo)))

(defmacro identidadp (p)
  `(= ,p (identidad)))

(defthm polinomiop-identidad
  (polinomiop (identidad))
  :rule-classes :type-prescription)

;; (defthm
;;   |RNG::1 !RNG::= RNG::0|
;;   (not (RNG::= (RNG::1_r)(RNG::0_r)))
;;   :hints (("Goal"
;; 	   :use RNG::|0 != 1|)))

(defthm ordenadop-identidad
  (ordenadop (identidad))
  :hints (("Goal" :in-theory (enable FUMON::identidad)))
  :rule-classes :type-prescription)

;;; -------------------------------
;;; Producto de monomio y polinomio
;;; -------------------------------

(defun *-monomio (m p)
  (cond ((or (nulop p) (not (monomiop m)) (not (polinomiop p)))
	 (nulo))
	(t
	 (+M (FUMON::* m (primero p)) (*-monomio m (resto p))))))

;;; Clausura

(defthm polinomiop-*-monomio
  (polinomiop (*-monomio m p))
  :rule-classes (:type-prescription
		 :rewrite))

;;; Neutro

(defthm |1 *M p = p|
  (implies (polinomiop (double-rewrite p))
	   (= (*-monomio (FUMON::identidad) p) p)))

;;; Cancelación

;;; NOTA:
;;;
;;; Primero se demuestra sintácticamente, introduciendo la forma
;;; normal. Luego se extiende a la igualdad semántica.

(defthm |m = 0 => fn(m *M p) =e 0|
  (implies (FUMON::nulop m)
	   (equal (fn (*-monomio m p)) (nulo))))

(defthm |m = 0 => m *M p = 0|
  (implies (FUMON::nulop m)
	   (= (*-monomio m p) (nulo))))

;;; Distributividad del producto externo respecto de la suma.

(defthm |m1 *M (m2 +M p) =e (m1 * m2) +M (m *M p)|
  (implies (and (monomiop (double-rewrite m1))
		(monomiop (double-rewrite m2)))
	   (equal (*-monomio m1 (+M m2 p))
		  (+M (FUMON::* m1 m2) (*-monomio m1 p)))))

(defthm |m *M (p + q) = (m *M p) + (m *M q)|
  (= (*-monomio m (+ p q))
     (+ (*-monomio m p) (*-monomio m q)))
  :hints (("Goal"
	   :in-theory (disable = + +M |p + q = q + p|))
	  ("Subgoal *1/1" :in-theory (enable = + +M))))

;;; NOTA:
;;;
;;; Esta propiedad permite cambiar un producto externo por otro
;;; más sencillo sobre monomios.

(defthm |m1 *M (m2 *M p) = (m1 * m2) *M p|
  (implies (and (monomiop (double-rewrite m1))
		(monomiop (double-rewrite m2)))
	   (= (*-monomio m1 (*-monomio m2 p))
	      (*-monomio (FUMON::* m1 m2) p)))
  :hints (("Goal" :in-theory (disable = + +M))
	  ("Subgoal *1/1" :in-theory (enable = + +M))))

(defthm
  |p != 0 => m *M p != 0|
  (implies (and (monomiop (double-rewrite m))
		(polinomiop (double-rewrite p))
		(not (nulop p)))
	   (not (nulop (*-monomio m p)))))

(defthm
  |ordenadop p => ordenadop m *M p|
  (implies (and (not (FUMON::nulop m))
		(ordenadop (double-rewrite p)))
	   (ordenadop (*-monomio m p))))

(defthm
  | m != 0 and p != 0 => fn(m *M p) != 0|
  (implies (and (monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(ordenadop (double-rewrite p))
		(not (nulop p)))
	   (not (nulop (fn (*-monomio m p)))))
  :hints (("Goal"
	   :in-theory (disable fnp-iff-ordenadop)
	   :use |p != 0 => m *M p != 0|)))

;;; ----------------------
;;; Producto de polinomios
;;; ----------------------

(defun * (p q)
  (cond ((or (nulop p) (not (polinomiop p)))
	 (nulo))
	(t
	 (+ (*-monomio (primero p) q) (* (resto p) q)))))

;;; Clausura

(defthm polinomiop-*
  (polinomiop (* p q))
  :rule-classes (:type-prescription
		 :rewrite))

;;; El producto de un monomio por el producto de dos polinomios es
;;; igual al producto del segundo polinomio por el resultado de
;;; multiplicar el monomio por el primer polinomio

(defthm |m *M (p * q) = (m *M p) * q|
  (implies (monomiop (double-rewrite m))
	   (= (*-monomio m (* p q))
	      (* (*-monomio m p) q)))
  :hints (("Goal"
	   :in-theory (disable + =))))

;;; Distributividad respecto de la suma

(defthm |p * q =e mp(p) *M q + resto(p) * q|
  (implies (and (polinomiop (double-rewrite p))
		(not (nulop p)))
	   (equal (* p q)
		  (+ (*-monomio (primero p) q) (* (resto p) q)))))

(defthm |(p + q) * r = (p * r) + (q * r)|
  (= (* (+ p q) r) (+ (* p r) (* q r)))
  :hints (("Goal"
	   :induct (fn p)
	   :in-theory (disable = + *))
	  ("Subgoal *1/1"
	   :in-theory (enable = + *))))

;;; Neutro

(defthm |1 * p = p|
  (= (* (identidad) p) p))

;;; Cancelación

(defthm |0 * p =e 0|
  (equal (* (nulo) p) (nulo)))

;; (defthm |0 * p = 0|
;;   (= (* (nulo) p) (nulo)))

;;; Asociatividad

(defthm |(p * q) * r = p * (q * r)|
  (= (* (* p q) r) (* p (* q r)))
  :hints (("Goal" :in-theory (disable = +))))

;;; Conmutatividad

;;; NOTA:
;;;
;;; La inducción apropiada es múltiple. Unas veces se requiere una
;;; hipótesis de inducción sobre uno de los parámetros, otras veces
;;; sobre el otro y otras sobre ambos. Hemos de suministrar el
;;; esquema.

(encapsulate ()
  (local
    (defthm tecnico
      (implies (and (monomiop (double-rewrite m))
		    (polinomiop (double-rewrite p))
		    (polinomiop (double-rewrite q)))
	       (= (+ p (+M m q)) (+ q (+M m p))))
      :hints (("Goal" :in-theory (disable = +)))))

  (local
    (defun esquema-de-induccion (p q)
      (declare (xargs :verify-guards nil :measure (ACL2::+ (len p) (len q))))
      (cond ((or (nulop p) (nulop q))
	    t)
	    (t
	     (and (esquema-de-induccion (resto p) (resto q))
		  (esquema-de-induccion (resto p) q)
		  (esquema-de-induccion p (resto q)))))))

  (defthm |p * q = q * p|
    (= (* p q) (* q p))
    :hints (("Goal"
	     :induct (esquema-de-induccion p q)
	     :do-not '(eliminate-destructors)
	     :in-theory (disable = + +M
				 |m = 0 => m *M p = 0|
				 |p != 0 => m *M p != 0|)))))

;;; Distributividad respecto de la suma

(defthm |p * (q + r) = (p * q) + (p * r)|
  (= (* p (+ q r)) (+ (* p q) (* p r)))
  :hints (("Goal"
	   :in-theory (disable = + *)
	   :use ((:instance |(p + q) * r = (p * r) + (q * r)|
			    (r p) (p q) (q r))))))

(defthm |p * 1 = p|
  (= (* p (identidad)) p))

(defthm |p * 0 =e 0|
  (equal (* p (nulo))(nulo)))

;; (defthm |p * 0 = 0|
;;   (= (* p (nulo)) (nulo)))

(defthm
  |nulop p1 * p2 <=> nulop p1 or nulop p2|
  (implies (and (polinomiop (double-rewrite p1))
		(polinomiop (double-rewrite p2)))
	   (equal (nulop (* p1 p2))
		  (or (nulop p1)
		      (nulop p2)))))

(defthm
  |p1 * p2 = 0 <=> p1 = 0 or p2 = 0|
  (implies (and (polinomiop (double-rewrite p1))
		(polinomiop (double-rewrite p2)))
	   (equal (equal (* p1 p2)(nulo))
		  (or (equal p1 (nulo))
		      (equal p2 (nulo))))))

(defthm
  |primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|
  (implies (and (polinomiop (double-rewrite p1))
		(polinomiop (double-rewrite p2))
		(not (nulop p1))
		(not (nulop p2)))
	   (equal (primero (* p1 p2))
		  (FUMON::* (primero p1)(primero p2)))))

(defun
  >-monomio (m p)
  "Determine if monomio m is FUMON::> than
   every monomio in p."
  (if (consp p)
      (and (FUTER::< (termino (primero p))(termino m))
	   (>-monomio m (resto P)))
      t))

(defthm
  |primero p FUMON::< m => >-monomio m p|
  (implies (and (ordenadop (double-rewrite p))
		(FUMON::< (primero p) m))
	   (>-monomio m p)))

(defthm
  |m >-monomio p => primero (m +M p) =e m|
  (implies (and (monomiop m)
		(not (FUMON::nulop m))
		(>-monomio m p))
	   (equal (primero (+-monomio m p)) m)))

(defthm
  |m >-monomio (n +-monomio p)|
  (implies (and (>-monomio m p)
		(FUTER::< (termino n)(termino m)))
	   (>-monomio m (+-monomio n p))))

(defthm
  |m >-monomio p => m >-monomio (fn p)|
  (implies (>-monomio m p)
	   (>-monomio m (fn p))))

(defthm
  |(primero p) >-monomio (resto p) => primero (fn p) =e primero p|
  (implies (and (polinomiop (double-rewrite p))
		(not (FUMON::nulop (primero p)))
		(>-monomio (primero p)(resto p)))
	   (equal (primero (fn p))(primero p))))

(defthm
  |primero (p1 * p2) != 0|
  (implies (and (ordenadop (double-rewrite p1))
		(ordenadop (double-rewrite p2))
		(not (nulop p1))
		(not (nulop p2)))
	   (not (FUMON::nulop (primero (* p1 p2)))))
  :hints (("Goal"
	   :in-theory (disable
		       |primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|)
	   :use |primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|)))

(defthm
  |ordenadop p => (primero p) >-monomio (resto p)|
  (implies (and (ordenadop (double-rewrite p))
		(not (nulop p)))
	   (>-monomio (primero p)(resto p))))

(defthm
  |primero (m *M p) >-monomio resto (m *M p)|
  (implies (and (not (FUMON::nulop m))
		(ordenadop (double-rewrite p)))
	   (>-monomio (primero (*-monomio m p))
		      (resto (*-monomio m p))))
  :hints (("Goal"
	   :in-theory (disable |ordenadop p => ordenadop m *M p|)
	   :use |ordenadop p => ordenadop m *M p|)))

(defthm
  |m >-monomio (append p1 p2)|
  (implies (and (>-monomio m p1)
		(>-monomio m p2))
	   (>-monomio m (append p1 p2))))

(defthm
  |termino (primero (*-monomio n p)) FUTER::< termino (primero (*-monomio m p))|
  (implies (and (monomiop (double-rewrite m))
		(monomiop (double-rewrite n))
		(FUMON::< n m)
		(polinomiop (double-rewrite p))
		(not (nulop p)))
	  (FUTER::< (termino (primero (*-monomio n p)))
		    (termino (primero (*-monomio m p))))))

(defthm
  |m FUMON::> n and n >-monomio p => m >-monomio p|
  (implies (and (FUMON::< n m)
		(>-monomio n p))
	   (>-monomio m p)))

(defthm
  |primero (m *M p) >- monomio append (resto m *M p)(n *m p)|
  (implies (and (monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(not (FUMON::nulop n))
		(FUMON::< n m)
		(ordenadop (double-rewrite p)))
	   (>-monomio (primero (*-monomio m p))
		      (append (resto (*-monomio m p))
			      (*-monomio n p))))
  :hints
  (("Goal"
    :in-theory
    (disable
     |m >-monomio (append p1 p2)|
     |termino (primero (*-monomio n p)) FUTER::< termino (primero (*-monomio m p))|)
    :use
    (|termino (primero (*-monomio n p)) FUTER::< termino (primero (*-monomio m p))|
     (:instance
      |m >-monomio (append p1 p2)|
      (m (primero (*-monomio m p)))
      (p1 (resto (*-monomio m p)))
      (p2 (*-monomio n p)))))))

(defthm
  |primero append (m *M p)(n *M p) >- monomio resto append ( m *M p)(n *m p)|
  (implies (and (monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(not (FUMON::nulop n))
		(FUMON::< n m)
		(ordenadop (double-rewrite p)))
	   (>-monomio (primero (append (*-monomio m p)
				       (*-monomio n p)))
		      (resto (append (*-monomio m p)
				     (*-monomio n p)))))
  :hints (("Goal"
	   :in-theory (disable
		       |primero (m *M p) >- monomio append (resto m *M p)(n *m p)|)
	   :use |primero (m *M p) >- monomio append (resto m *M p)(n *m p)|)))

(defthm
  |primero (m *M p2) >-monomio append (resto m *M p2) p1|
  (implies (and (not (FUMON::nulop m))
		(>-monomio (primero p1)(resto p1))
		(FUMON::< (primero p1)(primero (*-monomio m p2)))
		(ordenadop (double-rewrite p2)))
	   (>-monomio (primero (*-monomio m p2))
		      (append (resto (*-monomio m p2))
			      p1))))

(defthm
  |primero (append (m *M p2) p1) >-monomio resto (append (m *M p2) p1)|
  (implies (and (not (FUMON::nulop m))
		(>-monomio (primero p1)(resto p1))
		(FUMON::< (primero p1)(primero (*-monomio m p2)))
		(ordenadop (double-rewrite p2)))
	   (>-monomio (primero (append (*-monomio m p2)
				       p1))
		      (resto (append (*-monomio m p2)
				     p1))))
  :hints (("Goal"
	   :in-theory (disable
		       |primero (m *M p2) >-monomio append (resto m *M p2) p1|)
	   :use |primero (m *M p2) >-monomio append (resto m *M p2) p1|)))

(defthm
  |primero (* p1 p2) >-monomio resto (* p1 p2)-lemma|
  (implies (and (>-monomio (primero (* (resto p1) p2))
			   (resto (* (resto p1) p2)))
		(not (FUMON::nulop (primero p1)))
		(FUMON::< (primero (resto p1))(primero p1))
		(ordenadop (double-rewrite p2)))
	   (>-monomio (car (append (*-monomio (primero p1) p2)
				   (* (resto p1) p2)))
		      (cdr (append (*-monomio (primero p1) p2)
				   (* (resto p1) p2)))))
  :hints (("Goal"
	   :in-theory
	   (disable
	    |primero (append (m *M p2) p1) >-monomio resto (append (m *M p2) p1)|
	    |primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|)
	   :use
	   ((:instance
	     |primero (append (m *M p2) p1) >-monomio resto (append (m *M p2) p1)|
	     (m (car p1))
	     (p1 (* (CDR P1) P2)))
	    (:instance
	     |primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|
	     (p1 (cdr p1)))))))

(defthm
  |primero (* p1 p2) >-monomio resto (* p1 p2)|
  (implies (and (ordenadop (double-rewrite p1))
		(ordenadop (double-rewrite p2)))
	   (>-monomio (primero (* p1 p2))(resto (* p1 p2)))))

(defthm
   |primero fn (p1 * p2) =e primero (p1 * p2)|
   (implies (and (ordenadop (double-rewrite p1))
		 (ordenadop (double-rewrite p2))
		 (not (nulop p1))
		 (not (nulop p2)))
	    (equal (primero (fn (* p1 p2)))(primero (* p1 p2)))))

(defthm
  |primero fn (p1 * p2) != 0|
  (implies (and (ordenadop (double-rewrite p1))
		(ordenadop (double-rewrite p2))
		(not (nulop p1))
		(not (nulop p2)))
	   (not (FUMON::nulop (primero (fn (* p1 p2))))))
  :hints (("Goal"
	   :in-theory (disable |primero (p1 * p2) != 0|)
	   :use |primero (p1 * p2) != 0|)))

(defthm
  |p1 != 0 and p2 != 0 => fn(p1 * p2) != 0|
  (implies (and (ordenadop (double-rewrite p1))
		(ordenadop (double-rewrite p2))
		(not (nulop p1))
		(not (nulop p2)))
	   (not (nulop (fn (* p1 p2)))))
  :hints (("Goal"
	   :in-theory
	   (e/d (coeficiente monomiop)
		(|primero fn (p1 * p2) != 0|
		 |primero fn (p1 * p2) =e primero (p1 * p2)|
		 |(primero p) >-monomio (resto p) => primero (fn p) =e primero p|))
	   :use |primero fn (p1 * p2) != 0|)))

(defthm
  |nulop fn(p1 * p2) <=> nulop p1 or nulop p2|
  (implies (and (ordenadop (double-rewrite p1))
		(ordenadop (double-rewrite p2)))
	   (equal (nulop (fn (* p1 p2)))
		  (or (nulop p1)
		      (nulop p2))))
  :hints (("Subgoal 3"
	   :in-theory (disable |p1 != 0 and p2 != 0 => fn(p1 * p2) != 0|)
	   :use |p1 != 0 and p2 != 0 => fn(p1 * p2) != 0|)))

(defthm
  |fn(p1 * p2) = 0 <=> p1 = 0 or p2 = 0|
  (implies (and (ordenadop (double-rewrite p1))
		(ordenadop (double-rewrite p2)))
	   (equal (equal (fn (* p1 p2))(nulo))
		  (or (equal p1 (nulo))
		      (equal p2 (nulo)))))
  :hints (("Subgoal 3"
	   :in-theory (disable |p1 != 0 and p2 != 0 => fn(p1 * p2) != 0|)
	   :use |p1 != 0 and p2 != 0 => fn(p1 * p2) != 0|)))
