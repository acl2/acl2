; ACL2 Univariate Polynomials over a Field books -- Polynomial Quotients
; and Remainders
;; Quotients, Remainders, Degrees, and Leading Coefficients
;;  of Normalized Univariate Polynomials over a Field
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

;;   John Cowles
;;   Department of Computer Science
;;   University of Wyoming
;;   Laramie, WY 82071-3682 U.S.A.

;;   Last modified July 2006 (for ACL2 Version 3.0).

; Modified by Matt Kaufmann for ACL2 Version 3.1 because
; SBCL complains about LISP::.

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

(certify-book "fuquot-rem"
	      6
	      nil ;;compile-flg
	      )
|#
(in-package "FUNPOL")

(include-book "fupolinomio-normalizado"
	      :load-compiled-file nil)

(defun
  deg (p)
  (FUMON::termino (primero p)))

(defthm
  Natp-deg
  (implies (and (polinomiop p)
		(not (= p (nulo))))
	   (and (integerp (deg p))
		(>= (deg p) 0)))
  :rule-classes :type-prescription
  :hints (("Goal"
	   :in-theory (enable nulo FUTER::terminop))))

(defthm
  =-implies-equal-deg-a
  (implies (and (= (double-rewrite p1)
		   (double-rewrite p2))
		(polinomiop (double-rewrite p1)))
	   (equal (equal (deg p1)
			 (deg p2))
		  t))
  :hints (("Goal"
	   :in-theory (enable = FUMON::=))))

(defthm
  =-implies-equal-deg-b
  (implies (and (= (double-rewrite p1)
		   (double-rewrite p2))
		(polinomiop (double-rewrite p2)))
	   (equal (equal (deg p1)
			 (deg p2))
		  t))
  :hints (("Goal"
	   :in-theory (enable = FUMON::=))))

(defthm
  |primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|
  (implies (and (polinomiop (double-rewrite p1))
		(polinomiop (double-rewrite p2))
		(not (nulop p1))
		(not (nulop p2)))
	   (equal (primero (* p1 p2))
		  (FUMON::* (primero p1)(primero p2))))
  :hints (("Goal"
	   :in-theory (enable *))))

(defthm
  |FUMON::termino (* m1 m2) =e FUMON::termino m1 ACL2::+ FUMON::termino m2|
  (equal (FUMON::termino (FUMON::* m1 m2))
	 (ACL2::+ (FUMON::termino m1)
		  (FUMON::termino m2)))
  :hints (("Goal"
	   :in-theory (enable FUTER::*))))

(defthm
  |deg (p1 * p2) =e deg p1 ACL2::+ deg p2|
  (implies (and (polinomiop (double-rewrite p1))
		(polinomiop (double-rewrite p2))
		(not (= (double-rewrite p1) (nulo)))
		(not (= (double-rewrite p2) (nulo))))
	   (equal (deg (* p1 p2))
		  (ACL2::+ (deg p1)
			   (deg p2))))
  :hints (("Goal"
	   :in-theory (enable nulo))))

(defthm
  |deg p1 <= deg (p1 * p2)|
  (implies (and (polinomiop (double-rewrite p1))
		(not (= (double-rewrite p1) (nulo)))
		(polinomiop (double-rewrite p2))
		(not (= (double-rewrite p2) (nulo))))
	   (<= (deg p1)(deg (* p1 p2))))
  :rule-classes :linear
  :hints (("Goal"
	   :in-theory (disable deg))))

(defthm
  |deg p2 <= deg (p1 * p2)|
  (implies (and (polinomiop (double-rewrite p1))
		(not (= (double-rewrite p1) (nulo)))
		(polinomiop (double-rewrite p2))
		(not (= (double-rewrite p2) (nulo))))
	   (<= (deg p2)(deg (* p1 p2))))
  :rule-classes :linear
  :hints (("Goal"
	   :in-theory (disable deg))))

(defun
  lc (p)
  (FUMON::coeficiente (primero p)))

(defthm
  |FLD::fdp (lc p)|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo))))
	   (and (FLD::fdp (lc p))
		(not (FLD::= (lc p)(FLD::0_f)))))
  :hints (("Goal"
	   :in-theory (enable nulo))))

(defthm
  |primero -p FUMON::= FUMON::- primero p|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p) (nulo))))
	   (FUMON::= (primero (- p))(FUMON::- (primero p))))
  :hints (("Goal"
	   :in-theory (enable nulo - FUPOL::+M))))

(defthm
  |resto -p = - resto p|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p) (nulo))))
	   (= (resto (- p))(- (resto p))))
  :hints (("Goal"
	   :in-theory (enable nulo  -))))

(defthm
  |nil + p = p|
  (implies (polinomiop (double-rewrite p))
	   (= (+ nil p) p))
  :hints (("Goal"
	   :in-theory (e/d (nulo)(|0 + p = p|))
	   :use |0 + p = p|)))

(defthm
  |FUMON::termino (- m) =e FUMON::termino m|
  (implies (FUMON::monomiop (double-rewrite m))
	   (equal (FUMON::termino (FUMON::- m))
		  (FUMON::termino m))))

(defthm
  |FUMON::monomiop (primero p)|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo))))
	   (FUMON::monomiop (primero p)))
  :hints (("Goal"
	   :in-theory (enable nulo))))

(defthm
  |not FUMON::nulop (primero p)|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo))))
	   (not (FUMON::nulop (primero p))))
  :hints (("Goal"
	   :in-theory (enable nulo))))

(defthm
  |FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo))))
	   (equal (FUMON::termino (primero (- p)))
		  (FUMON::termino (FUMON::- (primero p)))))
  :hints (("Goal"
	   :in-theory (disable FUMON::-
			       |FUMON::termino (- m) =e FUMON::termino m|))))

(defthm
  |FUMON::termino (FUMON::- (primero p) =e FUMON::termino (primero p)|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo))))
	   (equal (FUMON::termino (FUMON::- (primero p)))
		  (FUMON::termino (primero p))))
 :hints (("Goal"
	  :in-theory (disable |FUMON::termino (- m) =e FUMON::termino m|)
	  :use (:instance
		|FUMON::termino (- m) =e FUMON::termino m|
		(m (primero p))))))

(defthm
  |deg (- p) =e deg p|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo))))
	   (equal (deg (- p))
		  (deg p)))
  :hints (("Goal"
	   :in-theory
	   (disable
	    |FUMON::termino (FUMON::- (primero p) =e FUMON::termino (primero p)|)
	   :use
	   |FUMON::termino (FUMON::- (primero p) =e FUMON::termino (primero p)|)))

(defthm
  |primero p FUPOL::+-monomio resto p =e p|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo))))
	   (equal (FUPOL::+-monomio (primero p)(resto p)) p)))

(defthm
  |- nil =e nil|
  (equal (- nil) nil)
  :hints (("Goal"
	   :in-theory (e/d (nulo)
			   (|- 0 =e 0|))
	   :use |- 0 =e 0|)))

(defthm
  |- p =e FUPOL::- p|
  (implies (polinomiop (double-rewrite p))
	   (equal (- p)(FUPOL::- p)))
  :hints (("Goal"
	   :in-theory (enable -))))

(defthm
  |- (m +Mo p) = (- m) +Mo (- p)|
  (implies (and (FUMON::monomiop (double-rewrite m))
		(polinomiop (double-rewrite p)))
	   (= (- (FUPOL::+-monomio m p))
	      (FUPOL::+-monomio (FUMON::- m)(- p))))
  :hints (("Goal"
	   :in-theory (e/d (=)
			   (FUPOL::|- (m +Mo p) =P (- m) +Mo (- p)|))
	   :use (:instance
		 FUPOL::|- (m +Mo p) =P (- m) +Mo (- p)|
		 (FUPOL::m m)
		 (FUPOL::p p)))))

(in-theory (disable |- p =e FUPOL::- p|))

(defthm
  |p + q FUPOL::=P mp(p) +Mo (resto(p) + q)-lemma|
  (implies (and (polinomiop (double-rewrite p))
		(FUMON::monomiop (double-rewrite m)))
	   (FUPOL::=p (FUPOL::+-monomio m (FUPOL::fn (FUPOL::+ nil p)))
		      (FUPOL::+-monomio m p))))

(defthm
  |p + q = mp(p) +Mo (resto(p) + q)-lemma-a|
  (implies (and (polinomiop p)
		(not (= p (nulo)))
		(polinomiop q))
	   (= (+ p q) (FUPOL::+-monomio (primero p)(+ (resto p) q))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable + =)
	   :do-not '(generalize))))

(defthm
  |p + q = mp(p) +Mo (resto(p) + q)|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q)))
	   (= (+ p q) (FUPOL::+-monomio (primero p)(+ (resto p) q))))
  :hints (("Goal"
	   :use |p + q = mp(p) +Mo (resto(p) + q)-lemma-a|)))

(defthm
  |=-implies-=-FUPOL::+-monomio-2a|
  (implies (and (= (double-rewrite p1)
		   (double-rewrite p2))
		(polinomiop (double-rewrite p1)))
	   (equal (= (FUPOL::+-monomio m p1)
		     (FUPOL::+-monomio m p2))
		  t))
 :hints (("Goal"
	  :in-theory (enable =))))

(defthm
  |=-implies-=-FUPOL::+-monomio-2b|
  (implies (and (= (double-rewrite p1)
		   (double-rewrite p2))
		(polinomiop (double-rewrite p2)))
	   (equal (= (FUPOL::+-monomio m p1)
		     (FUPOL::+-monomio m p2))
		  t))
 :hints (("Goal"
	  :in-theory (enable =))))

(defthm
  |q + p = mp(q) +Mo (resto(q) + p)|
  (implies (and (polinomiop q)
		(not (= q (nulo)))
		(polinomiop p))
	   (= (+ q p) (FUPOL::+-monomio (primero q)(+ (resto q) p))))
  :rule-classes nil)

(defthm
  |p + q = mp(q) +Mo (p + (resto(q))|
  (implies (and (polinomiop (double-rewrite p))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo))))
	   (= (+ p q) (FUPOL::+-monomio (primero q)(+ p (resto q)))))
  :hints (("Goal"
	   :use |q + p = mp(q) +Mo (resto(q) + p)|)))

(defthm
  |p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo))))
	   (= (+ p q)
	      (FUPOL::+-monomio (primero p)
				(FUPOL::+-monomio (primero q)
						  (+ (resto p)
						     (resto q))))))
  :hints (("Goal"
	   :in-theory (disable |p + q = mp(p) +Mo (resto(p) + q)|)
	   :use |p + q = mp(p) +Mo (resto(p) + q)|)))

(defthm
  |FUMON::coeficiente (- m) FLD::= FLD::- (FUMON::coeficiente m)|
  (implies (FUMON::monomiop (double-rewrite m))
	   (FLD::= (FUMON::coeficiente (FUMON::- m))
		   (FLD::- (FUMON::coeficiente m)))))

(defthm
  |coeficiente (- (primero p)) FLD::= FLD::- (coeficiente (primero p))|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo))))
	   (FLD::= (FUMON::coeficiente (FUMON::- (primero p)))
		   (FLD::- (FUMON::coeficiente (primero p)))))
  :hints (("Goal"
	   :in-theory
	   (disable |FUMON::coeficiente (- m) FLD::= FLD::- (FUMON::coeficiente m)|)
	   :use (:instance
		 |FUMON::coeficiente (- m) FLD::= FLD::- (FUMON::coeficiente m)|
		 (m (primero p))))))

(defthm
  |coeficiente (primero p)) + coeficiente (primero q) = 0|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(FUMON::= (FUMON::- (primero p))
			  (primero q)))
	   (FLD::= (FLD::+ (FUMON::coeficiente (primero p))
			   (FUMON::coeficiente (primero q)))
		   (FLD::0_f)))
  :hints
  (("Goal"
    :in-theory
    (e/d
     (nulo)
     (|coeficiente (- (primero p)) FLD::= FLD::- (coeficiente (primero p))|))
    :use |coeficiente (- (primero p)) FLD::= FLD::- (coeficiente (primero p))|)))

(defthm
  |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-1|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(FUMON::= (FUMON::- (primero p))
			  (primero q)))
	   (= (FUPOL::+-monomio
	       (FUMON::monomio (FUMON::coeficiente (primero p))
			       (FUMON::termino (primero p)))
	       (FUPOL::+-monomio (FUMON::monomio (FUMON::coeficiente (car q))
						 (FUMON::termino (car p)))
				 (+ (resto p)(resto q))))
	      (+ (resto p)(resto q))))
  :hints (("Goal"
	   :in-theory (e/d (=)(FUPOL::|(a + b) = 0 => a +Mo (b +Mo p) =P p|))
	   :use (:instance
		 FUPOL::|(a + b) = 0 => a +Mo (b +Mo p) =P p|
		 (FUPOL::p (+ (resto p)(resto q)))
		 (FUPOL::a (FUMON::coeficiente (primero p)))
		 (FUPOL::b (FUMON::coeficiente (primero q)))
		 (FUPOL::te (FUMON::termino (primero p)))))))

(defthm
  Lemma-a
  (implies (and (polinomiop q)
		(not (= q (nulo)))
		(FUMON::= (FUMON::- (primero p))
			  (primero q)))
	   (equal (FUMON::termino (FUMON::- (primero p)))
		  (FUMON::termino (primero q))))
  :rule-classes nil)

(defthm
  Lemma-b
  (implies (and (polinomiop p)
		(not (= p (nulo)))
		(polinomiop q)
		(not (= q (nulo)))
		(FUMON::= (FUMON::- (primero p))
			  (primero q)))
	   (equal (FUMON::termino (primero p))
		  (FUMON::termino (primero q))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory
	   (disable
	    |FUMON::termino (FUMON::- (primero p) =e FUMON::termino (primero p)|)
	   :use (|FUMON::termino (FUMON::- (primero p) =e FUMON::termino (primero p)|
		 Lemma-a))))

(defthm
  |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-2|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(FUMON::= (FUMON::- (primero p))
			  (primero q)))
	   (= (FUPOL::+-monomio
	       (FUMON::monomio (FUMON::coeficiente (primero p))
			       (FUMON::termino (primero p)))
	       (FUPOL::+-monomio (FUMON::monomio (FUMON::coeficiente (primero q))
						 (FUMON::termino (primero q)))
				 (+ (resto p)(resto q))))
	      (+ (resto p)(resto q))))
  :hints (("Goal"
	   :in-theory (disable |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-1|
			       FUPOL::ordenadop)
	   :use (|(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-1|
		 Lemma-b))))

(defthm
  |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(FUMON::= (FUMON::- (primero p))
			  (primero q)))
	   (= (FUPOL::+-monomio (primero p)
				(FUPOL::+-monomio (primero q)
						  (+ (resto p)
						     (resto q))))
	      (+ (resto p)(resto q))))
  :hints (("Goal"
	   :in-theory (disable |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-2|
			       FUPOL::ordenadop)
	  :use |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-2|)))

;;Bad rewrite rule:
(defthm
  |p + q = (resto p) + (resto q)|
  (implies (and (polinomiop p)
		(not (= p (nulo)))
		(polinomiop q)
		(not (= q (nulo)))
		(FUMON::= (FUMON::- (primero p))
			  (primero q)))
	   (= (+ p q)(+ (resto p)(resto q))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable FUPOL::ordenadop))))

;;Bad rewrite rule:
(defthm
  |p + q = (resto p) + (resto q)-a|
  (implies (and (polinomiop p)
		(not (= p (nulo)))
		(polinomiop q)
		(not (= q (nulo)))
		(FUMON::= (primero p)
			  (FUMON::- (primero q))))
	   (= (+ p q)(+ (resto p)(resto q))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|
			       |p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|
			       |p + q = mp(q) +Mo (p + (resto(q))|
			       |p + q = mp(p) +Mo (resto(p) + q)|
			       FUPOL::ordenadop)
	   :use (:instance
		 |p + q = (resto p) + (resto q)|
		 (p q)(q p)))))

(defthm
  |deg(p + q) =_e deg(p)-lemma-1|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(FUTER::< (FUMON::termino (primero q))
			  (FUMON::termino (primero p))))
	  (FUPOL::>-monomio (primero (FUPOL::+ p q))(resto (FUPOL::+ p q))))
  :hints (("Goal"
	   :in-theory (enable FUPOL::+))))

(defthm
  |deg(p + q) =_e deg(p)-lemma-2|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(FUTER::< (FUMON::termino (primero q))
			  (FUMON::termino (primero p))))
	  (equal (primero (FUPOL::fn (FUPOL::+ p q)))
		 (primero (FUPOL::+ p q))))
  :hints
  (("Goal"
    :in-theory
    (e/d  (nulo)
	  (FUPOL::|(primero p) >-monomio (resto p) => primero (fn p) =e primero p|))
    :use (:instance
	  FUPOL::|(primero p) >-monomio (resto p) => primero (fn p) =e primero p|
	  (FUPOL::p (FUPOL::+ p q))))))

(defthm
  |deg(p + q) =_e deg(p)-lemma-3|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p) (nulo))))
	   (equal (primero (FUPOL::+ p q))
		  (primero p)))
  :hints (("Goal"
	   :in-theory (enable FUPOL::+ nulo))))

(defthm
  |deg(p + q) =_e deg(p)-lema-4|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(FUTER::< (FUMON::termino (primero q))
			  (FUMON::termino (primero p))))
	  (equal (primero (+ p q))
		 (primero p)))
  :hints (("Goal"
	   :in-theory (enable +))))

(defthm
  |deg(p + q) =_e deg(p)|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(> (deg p) (deg q)))
	  (equal (deg (+ p q))
		 (deg p)))
  :hints (("Goal"
	   :in-theory (enable FUTER::<))))

(defthm
  |=-refines-FUPOL::=P|
  (implies (= p1 p2)
	   (FUPOL::=P p1 p2))
  :rule-classes :refinement
  :hints (("Goal"
	   :in-theory (enable =))))

(defthm
  |FUPOL::=P-refines-=|
  (implies (FUPOL::=P p1 p2)
	   (= p1 p2))
  :rule-classes :refinement
  :hints (("Goal"
	   :in-theory (enable =))))

(defthm
  |deg(p + q) =_e deg(q)|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(ACL2::< (deg p)(deg q)))
	   (equal (deg (+ p q))
		  (deg q)))
  :hints (("Goal"
	   :in-theory (disable =-implies-equal-deg-a
			       =-implies-equal-deg-b
			       |deg(p + q) =_e deg(p)|)
	   :use ((:instance
		  =-implies-equal-deg-a
		  (p1 (+ p q))
		  (p2 (+ q p)))
		 (:instance
		  |deg(p + q) =_e deg(p)|
		  (p q)(q p))))))

(defthm
  |deg(p + q) ACL2::< deg(p)-lemma-1|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(equal (FUMON::termino (primero p))
		       (FUMON::termino (primero q))))
	   (FUPOL::>-monomio (primero p)
			     (append (resto p)(resto q)))))

(defthm
  |deg(p + q) ACL2::< deg(p)-lemma-2|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(not (= (+ (resto p)(resto q))(nulo)))
		(equal (FUMON::termino (primero p))
		       (FUMON::termino (primero q))))
	   (FUPOL::>-monomio (primero p)
			     (FUPOL::+ (resto p)(resto q))))
  :hints (("Goal"
	   :in-theory (enable FUPOL::+))))

(defthm
  |deg(p + q) ACL2::< deg(p)-lemma-3|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(not (= (+ (resto p)(resto q))(nulo)))
		(equal (FUMON::termino (primero p))
		       (FUMON::termino (primero q))))
	   (FUPOL::>-monomio (primero p)
			     (FUPOL::fn (FUPOL::+ (resto p)(resto q)))))
  :hints (("Goal"
	   :in-theory (disable FUPOL::ordenadop))))

(defthm
  |deg(p + q) ACL2::< deg(p)-lemma-4|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(not (= (+ (resto p)(resto q))(nulo)))
		(equal (FUMON::termino (primero p))
		       (FUMON::termino (primero q))))
	   (FUPOL::>-monomio (primero p)
			     (+ (resto p)(resto q))))
  :hints (("Goal"
	   :in-theory (e/d (+)(FUPOL::ordenadop)))))

;; (defthm
;;   |deg(p + q) ACL2::< deg(p)-lemma-5|
;;   (implies (and (polinomiop p)
;; 		(not (= p (nulo)))
;; 		(FUPOL::>-monomio m p))
;; 	   (FUTER::< (FUMON::termino (primero p))
;; 		     (FUMON::termino m)))
;;   :hints (("Goal"
;; 	   :in-theory (enable nulo))))

(defthm
  |deg(p + q) ACL2::< deg(p)-lemma-5|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(FUPOL::>-monomio m p))
	   (FUTER::< (FUMON::termino (primero p))
		     (FUMON::termino m)))
  :hints (("Goal"
	   :in-theory (enable nulo))))

(defthm
  |deg(p + q) ACL2::< deg(p)-lemma-6|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(not (= (+ (resto p)(resto q))(nulo)))
		(equal (FUMON::termino (primero p))
		       (FUMON::termino (primero q))))
	   (FUTER::< (FUMON::termino (primero (+ (resto p)(resto q))))
		     (FUMON::termino (primero p))))
  :hints (("Goal"
	   :in-theory (e/d (nulo)
			   (FUPOL::ordenadop)))))

(defthm
  |deg(p + q) ACL2::< deg(p)-lemma-7|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q)(nulo)))
		(not (= (+ (resto p)(resto q))(nulo)))
		(equal (FUMON::termino (primero p))
		       (FUMON::termino (primero q))))
	   (ACL2::< (deg (+ (resto p)(resto q)))
		    (deg p)))
  :hints (("Goal"
	   :in-theory (e/d (FUTER::<)
			   (|deg(p + q) ACL2::< deg(p)-lemma-6|))
	   :use |deg(p + q) ACL2::< deg(p)-lemma-6|)))

(defthm
  |deg(p + q) ACL2::< deg(p)|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q) (nulo)))
		(FUMON::= (FUMON::- (primero p))
			  (primero q))
		(not (= (+ (double-rewrite p)
			   (double-rewrite q))
			(nulo))))
	   (ACL2::< (deg (+ p q))
		    (deg p)))
  :rule-classes (:rewrite
		 :linear)
  :hints (("Goal"
	   :in-theory
	   (e/d (FUMON::=)
		(=-implies-equal-deg-a
		 =-implies-equal-deg-b
		 |deg(p + q) ACL2::< deg(p)-lemma-7|
		 |FUMON::termino (FUMON::- (primero p) =e FUMON::termino (primero p)|
		 FUPOL::ordenadop))
	   :use (|p + q = (resto p) + (resto q)|
		 (:instance
		   =-implies-equal-deg-a
		   (p1 (+ p q))(p2 (+ (resto p)(resto q))))
		 |FUMON::termino (FUMON::- (primero p) =e FUMON::termino (primero p)|
		 |deg(p + q) ACL2::< deg(p)-lemma-7|))))

(defthm
  |deg(p + q) ACL2::< deg(p)-a|
  (implies (and (polinomiop (double-rewrite p))
		(not (= (double-rewrite p)(nulo)))
		(polinomiop (double-rewrite q))
		(not (= (double-rewrite q) (nulo)))
		(FUMON::= (primero p)
			  (FUMON::- (primero q)))
		(not (= (+ (double-rewrite p)
			   (double-rewrite q))
			(nulo))))
	   (ACL2::< (deg (+ p q))
		    (deg p)))
  :rule-classes (:rewrite
		 :linear)
  :hints
  (("Goal"
    :in-theory
    (disable |deg(p + q) ACL2::< deg(p)|
	     FUMON::nulop
	     |p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|
	     |p + q = mp(q) +Mo (p + (resto(q))|
	     |p + q = mp(p) +Mo (resto(p) + q)|
	     |FUMON::termino (FUMON::- (primero p) =e FUMON::termino (primero p)|
	     FUMON::=-implies-equal-termino-1
	     FUMON::=-implies-equal-termino-2
	     =-implies-equal-deg-a
	     =-implies-equal-deg-b)
    :use ((:instance
	   |deg(p + q) ACL2::< deg(p)|
	   (p q)(q p))
	  (:instance
	   |FUMON::termino (FUMON::- (primero p) =e FUMON::termino (primero p)|
	   (p q))
	  (:instance
	   FUMON::=-implies-equal-termino-1
	   (FUMON::y1 (primero p))
	   (FUMON::y2 (FUMON::- (primero q))))
	  (:instance
	   =-implies-equal-deg-a
	   (p1 (+ p q))
	   (p2 (+ q p)))))))

(defthm
  |not FUMON::nulop m|
  (implies (and (polinomiop (double-rewrite p1))
		(not (= (double-rewrite p1)(nulo)))
		(polinomiop (double-rewrite p2))
		(not (= (double-rewrite p2)(nulo)))
		(ACL2::>= (deg p1)
			  (deg p2)))
	   (not (FUMON::nulop (FUMON::monomio (FLD::* (lc p1)
						      (FLD::/ (lc p2)))
					      (ACL2::- (deg p1)
						       (deg p2))))))
  :hints (("Goal"
	   :in-theory (enable nulo FUTER::terminop))))

(defthm
  |m FUPOL::*-monomio p2 != 0|
  (implies (and (polinomiop (double-rewrite p1))
		(not (= (double-rewrite p1)(nulo)))
		(polinomiop p2)
		(not (= p2 (nulo)))
		(ACL2::>= (deg p1)
			  (deg p2)))
	   (let ((m (FUMON::monomio (FLD::* (lc p1)
					    (FLD::/ (lc p2)))
				    (ACL2::- (deg p1)
					     (deg p2)))))
	        (not (= (FUPOL::*-monomio m p2)
			(nulo)))))
  :hints (("Goal"
	   :in-theory (enable FUTER::* FUTER::terminop
			      FUMON::* FUMON::monomiop FUMON::monomio
			      FUMON::coeficiente FUMON::termino
			      FUPOL::+M =))))

(defthm
  |polinomiop (m FUPOL::*-monomio p2)|
  (implies (and (polinomiop (double-rewrite p1))
		(not (= (double-rewrite p1)(nulo)))
		(polinomiop p2)
		(not (= p2 (nulo)))
		(ACL2::>= (deg p1)
			  (deg p2)))
	   (let ((m (FUMON::monomio (FLD::* (lc p1)
					    (FLD::/ (lc p2)))
				    (ACL2::- (deg p1)
					     (deg p2)))))
	        (polinomiop (FUPOL::*-monomio m p2))))
    :hints (("Goal"
	   :in-theory (disable FUPOL::|ordenadop p => ordenadop m *M p|
			       |not FUMON::nulop m|)
	   :use (|not FUMON::nulop m|
		 (:instance
		  FUPOL::|ordenadop p => ordenadop m *M p|
		  (FUPOL::p p2)
		  (FUPOL::m (FUMON::monomio (FLD::* (lc p1)
						    (FLD::/ (lc p2)))
					    (ACL2::- (deg p1)
						     (deg p2)))))))))

(defthm
  |primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|
  (implies (and (polinomiop (double-rewrite p1))
		(not (= (double-rewrite p1)(nulo)))
		(polinomiop (double-rewrite p2))
		(not (= (double-rewrite p2)(nulo)))
		(ACL2::>= (deg p1)
			  (deg p2)))
	   (let ((m (FUMON::monomio (FLD::* (lc p1)
					    (FLD::/ (lc p2)))
				    (ACL2::- (deg p1)
					     (deg p2)))))
	        (FUMON::= (primero (FUPOL::*-monomio m p2))
			  (primero p1))))
  :hints (("Goal"
	   :in-theory (enable FUTER::* FUTER::terminop
			      FUMON::* FUMON::monomiop FUMON::monomio
			      FUMON::= FUMON::coeficiente FUMON::termino
			      FUPOL::+M nulo))))

(defthm
  |primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|
  (implies (and (polinomiop (double-rewrite p1))
		(not (= (double-rewrite p1)(nulo)))
		(polinomiop (double-rewrite p2))
		(not (= (double-rewrite p2)(nulo)))
		(ACL2::>= (deg p1)
			  (deg p2)))
	   (let ((m (FUMON::monomio (FLD::* (lc p1)
					    (FLD::/ (lc p2)))
				    (ACL2::- (deg p1)
					     (deg p2)))))
	        (FUMON::= (primero (- (FUPOL::*-monomio m p2)))
			  (FUMON::- (primero (FUPOL::*-monomio m p2))))))
  :hints (("Goal"
	   :in-theory (disable |primero -p FUMON::= FUMON::- primero p|
			       |polinomiop (m FUPOL::*-monomio p2)|
			       |m FUPOL::*-monomio p2 != 0|)
	   :use ((:instance
		  |primero -p FUMON::= FUMON::- primero p|
		  (p (let ((m (FUMON::monomio (FLD::* (lc p1)
						      (FLD::/ (lc p2)))
					      (ACL2::- (deg p1)
						       (deg p2)))))
		          (FUPOL::*-monomio m p2))))
		 |polinomiop (m FUPOL::*-monomio p2)|
		 |m FUPOL::*-monomio p2 != 0|))))

(defthm
  |FUMON::- (FUMON::- m) FUMON::= m|
  (implies (FUMON::monomiop (double-rewrite m))
	   (FUMON::= (FUMON::- (FUMON::- m))
		     m)))

(defthm
  |FUMON::- (primero (- (m *-monomio p2))) = (primero (m *-monomio p2))|
  (implies (and (polinomiop (double-rewrite p1))
		(not (= (double-rewrite p1)(nulo)))
		(polinomiop (double-rewrite p2))
		(not (= (double-rewrite p2)(nulo)))
		(ACL2::>= (deg p1)
			  (deg p2)))
	   (let ((m (FUMON::monomio (FLD::* (lc p1)
					    (FLD::/ (lc p2)))
				    (ACL2::- (deg p1)
					     (deg p2)))))
	        (FUMON::= (FUMON::- (primero (- (FUPOL::*-monomio m p2))))
			  (primero (FUPOL::*-monomio m p2)))))
  :hints (("Goal"
	   :in-theory
	   (disable |primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|
		    FUMON::=-implies-=_-
		    FUMON::-)
	   :use (|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|
		 (:instance
		  FUMON::=-implies-=_-
		  (FUMON::m1 (let ((m (FUMON::monomio (FLD::* (lc p1)
							      (FLD::/ (lc p2)))
						      (ACL2::- (deg p1)
							       (deg p2)))))
			           (primero (- (FUPOL::*-monomio m p2)))))
		  (FUMON::m2  (let ((m (FUMON::monomio (FLD::* (lc p1)
							       (FLD::/ (lc p2)))
						       (ACL2::- (deg p1)
								(deg p2)))))
			           (FUMON::- (primero (FUPOL::*-monomio m p2)))))
		  )))))

(defthm
  |FUMON::- (primero (- (m *-monomio p2))) FUMON::= primero p1|
  (implies (and (polinomiop (double-rewrite p1))
		(not (= (double-rewrite p1)(nulo)))
		(polinomiop (double-rewrite p2))
		(not (= (double-rewrite p2)(nulo)))
		(ACL2::>= (deg p1)
			  (deg p2)))
	   (let ((m (FUMON::monomio (FLD::* (lc p1)
					    (FLD::/ (lc p2)))
				    (ACL2::- (deg p1)
					     (deg p2)))))
	        (FUMON::= (FUMON::- (primero (- (FUPOL::*-monomio m p2))))
			  (primero p1))))
  :hints (("Goal"
	   :in-theory
	   (disable
	    |FUMON::- (primero (- (m *-monomio p2))) = (primero (m *-monomio p2))|
	    |primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|)
	   :use
	   (|FUMON::- (primero (- (m *-monomio p2))) = (primero (m *-monomio p2))|
	    |primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))))

(defthm
  |FUPOL::- p != 0|
  (implies (and (polinomiop p)
		(not (= p (nulo))))
	   (not (= (FUPOL::- p)(nulo))))
  :hints (("Goal"
	   :in-theory (enable =))))

(defthm
  |- p != 0|
  (implies (and (polinomiop p)
		(not (= p (nulo))))
	   (not (= (- p)(nulo))))
  :hints (("Goal"
	   :in-theory (enable |- p =e FUPOL::- p|))))

(defthm
  |- (m FUPOL::*-monomio p2) != 0|
  (implies (and (polinomiop (double-rewrite p1))
		(not (= (double-rewrite p1)(nulo)))
		(polinomiop p2)
		(not (= p2 (nulo)))
		(ACL2::>= (deg p1)
			  (deg p2)))
	   (let ((m (FUMON::monomio (FLD::* (lc p1)
					    (FLD::/ (lc p2)))
				    (ACL2::- (deg p1)
					     (deg p2)))))
	        (not (= (- (FUPOL::*-monomio m p2))
			(nulo)))))
  :hints (("Goal"
	   :in-theory (disable |m FUPOL::*-monomio p2 != 0|
			       |polinomiop (m FUPOL::*-monomio p2)|)
	   :use (|m FUPOL::*-monomio p2 != 0|
		 |polinomiop (m FUPOL::*-monomio p2)|))))

(defthm
  |deg (p1 + (- (m FUPOL::*-monomio p2))) ACL2::< deg p1|
  (implies (and (polinomiop (double-rewrite p1))
		(not (= (double-rewrite p1)(nulo)))
		(polinomiop (double-rewrite p2))
		(not (= (double-rewrite p2)(nulo)))
		(ACL2::>= (deg p1)
			  (deg p2))
		(let ((m (FUMON::monomio (FLD::* (lc p1)
						 (FLD::/ (lc p2)))
					 (ACL2::- (deg p1)
						  (deg p2)))))
		     (not (= (+ p1 (- (FUPOL::*-monomio m p2)))
			     (nulo)))))
	   (let ((m (FUMON::monomio (FLD::* (lc p1)
					    (FLD::/ (lc p2)))
				    (ACL2::- (deg p1)
					     (deg p2)))))
	        (ACL2::< (deg (+ p1 (- (FUPOL::*-monomio m p2))))
			 (deg p1))))
  :hints (("Goal"
	   :in-theory (disable deg lc
			       FUMON::- FUPOL::ordenadop
			       |deg(p + q) ACL2::< deg(p)|
			       |deg(p + q) ACL2::< deg(p)-a|)
	   :use ((:instance
		  |deg(p + q) ACL2::< deg(p)-a|
		  (p p1)(q (let ((m (FUMON::monomio (FLD::* (lc p1)
							    (FLD::/ (lc p2)))
						    (ACL2::- (deg p1)
							     (deg p2)))))
			        (- (FUPOL::*-monomio m p2)))))))))

(defun
  quot (p1 p2)
  (declare (xargs :measure (if (and (polinomiop p1)
				    (not (= p1 (nulo))))
			       (ACL2::+ 1 (deg p1))
			       0)
		  :hints (("Goal"
			   :in-theory (disable deg lc))
			  ("Subgoal 1.1"
			   :in-theory
			   (disable
			    |deg (p1 + (- (m FUPOL::*-monomio p2))) ACL2::< deg p1|)
			   :use
			   |deg (p1 + (- (m FUPOL::*-monomio p2))) ACL2::< deg p1|
			  ))))
  (if (and (not (= p1 (nulo)))
	   (not (= p2 (nulo)))
	   (polinomiop p1)
	   (polinomiop p2)
	   (ACL2::>= (deg p1)
		     (deg p2)))
      (let ((m (FUMON::monomio (FLD::* (lc p1)
				       (FLD::/ (lc p2)))
			       (ACL2::- (deg p1)
					(deg p2)))))
	   (FUPOL::+-monomio m
			     (quot (+ p1 (- (FUPOL::*-monomio m p2)))
				   p2)))
      (nulo)))

(defthm
  |~(polinomiop p1) => quot(p1 p2) =e 0|
  (implies (not (polinomiop (double-rewrite p1)))
	   (equal (quot p1 p2)
		  (nulo))))

(defthm
  |~(polinomiop p2) => quot(p1 p2) =e 0|
  (implies (not (polinomiop (double-rewrite p2)))
	   (equal (quot p1 p2)
		  (nulo))))

(defthm
  |deg p1 < deq p2 => quot(p1 p2) =e 0|
  (implies (ACL2::< (deg p1)
		    (deg p2))
	   (equal (quot p1 p2)
		  (nulo))))

(defthm
  |(p = 0) =e (p =e nil)|
  (equal (= p (nulo))
	 (equal p nil))
  :hints (("Goal"
	   :in-theory (enable = nulo))))

(defthm
  |p1 = 0 => quot(p1 p2) =e 0|
  (implies (= (double-rewrite p1)(nulo))
	   (equal (quot p1 p2)
		  (nulo))))

(defthm
  |p2 = 0 => quot(p1 p2) =e 0|
  (implies (= (double-rewrite p2)(nulo))
	   (equal (quot p1 p2)
		  (nulo))))

(in-theory (disable |(p = 0) =e (p =e nil)|))

(defthm
  Polinomiop-quot
  (polinomiop (quot p1 p2))
  :hints (("Goal"
	   :in-theory (disable deg lc))))

(defun
  quot-induct-hint (p1 p2 p)
  (declare (xargs :measure (if (and (polinomiop p1)
				    (not (= p1 (nulo))))
			       (ACL2::+ 1 (deg p1))
			       0)
		  :hints (("Goal"
			   :in-theory (disable deg lc))
			  ("Subgoal 1.1"
			   :in-theory
			   (disable
			    |deg (p1 + (- (m FUPOL::*-monomio p2))) ACL2::< deg p1|)
			   :use
			   (:instance
			    |deg (p1 + (- (m FUPOL::*-monomio p2))) ACL2::< deg p1|
			    (p2 p))))))
  (if (and (not (= p1 (nulo)))
	   (not (= p2 (nulo)))
	   (not (= p  (nulo)))
	   (polinomiop p1)
	   (polinomiop p )
	   (ACL2::>= (deg p1)(deg p)))
      (let ((m1 (FUMON::monomio (FLD::* (lc p1)
					(FLD::/ (lc p)))
				(ACL2::- (deg p1)
					 (deg p))))
	    (m2 (FUMON::monomio (FLD::* (lc p2)
					(FLD::/ (lc p)))
				(ACL2::- (deg p2)
					 (deg p)))))
	   (quot-induct-hint (+ p1 (- (FUPOL::*-monomio m1 p)))
			     (+ p2 (- (FUPOL::*-monomio m2 p)))
			     p))
      t))

(defthm
  =-implies-=-quot-1-lemma-1
  (implies (and (ACL2::< (deg p1) (deg p))
		(= (double-rewrite p1)
		   (double-rewrite p2)))
	   (= (quot p2 p)(nulo)))
  :hints (("Goal"
	   :in-theory (disable deg
			       =-implies-equal-deg-a
			       =-implies-equal-deg-b)
	   :use =-implies-equal-deg-b)))

(defthm
  =-implies-=-quot-1-lemma-2
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(not (= p (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(FUPOL::ordenadop p)
		(<= (deg p) (deg p1))
		(<= (deg p) (deg p2))
		(equal (deg p1)(deg p2))
		(= p1 p2))
	   (FUMON::= (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p)))
				     (ACL2::+ (deg p1)
					      (ACL2::- (deg p))))
		     (FUMON::monomio (FLD::* (lc p2) (FLD::/ (lc p)))
				     (ACL2::+ (deg p2)
					      (ACL2::- (deg p))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable = FUMON::=))))

(defthm
  =-implies-=-quot-1-lemma-3
  (implies (and (not (= p1 (nulo)))
		(not (= p (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p)
		(<= (deg p) (deg p1))
		(= p1 p2))
	   (FUMON::= (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p)))
				     (ACL2::+ (deg p1)
					      (ACL2::- (deg p))))
		     (FUMON::monomio (FLD::* (lc p2) (FLD::/ (lc p)))
				     (ACL2::+ (deg p2)
					      (ACL2::- (deg p))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc
			       =-implies-equal-deg-a
			       =-implies-equal-deg-b)
	   :use (=-implies-=-quot-1-lemma-2
		 =-implies-equal-deg-a))))

(defthm
  |FUMON::=-implies-=-FUPOL::*-monomio-1|
  (implies (FUMON::= m1 m2)
	   (= (FUPOL::*-monomio m1 p)
	      (FUPOL::*-monomio m2 p)))
  :rule-classes :congruence)

(defthm
  =-implies-=-quot-1-lemma-4
  (implies (and (not (= p1 (nulo)))
		(not (= p  (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p)
		(<= (deg p) (deg p1))
		(= p1 p2))
	   (= (+ p1
		 (- (FUPOL::*-monomio
		     (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p)))
				     (ACL2::+ (deg p1)
					      (ACL2::- (deg p))))
		     p)))
	      (+ p2
		 (- (FUPOL::*-monomio
		     (FUMON::monomio (FLD::* (lc p2) (FLD::/ (lc p)))
				     (ACL2::+ (deg p2)
					      (ACL2::- (deg p))))
		     p)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc)
	   :use =-implies-=-quot-1-lemma-3)))

(defthm
  =-implies-=-quot-1-lemma-5
  (implies (and (FUMON::= m1 m2)
		(= p1 p2)
		(polinomiop p1))
	   (= (FUPOL::+-monomio m1 p1)
	      (FUPOL::+-monomio m2 p2)))
  :rule-classes nil)

(defthm
  =-implies-=-quot-1-lemma-6
  (implies (and (not (= p1 (nulo)))
		(not (= p  (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p)
		(<= (deg p) (deg p1))
		(= p1 p2)
		(=
		 (quot
		  (+ p1
		     (- (FUPOL::*-monomio
			 (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p)))
					 (ACL2::+ (deg p1)
						  (ACL2::- (deg p))))
			 p)))
		  p)
		 (quot
		  (+ p2
		     (- (FUPOL::*-monomio
			 (FUMON::monomio (FLD::* (lc p2) (FLD::/ (lc p)))
					 (ACL2::+ (deg p2)
						  (ACL2::- (deg p))))
			 p)))
		  p)))
	   (= (FUPOL::+-monomio
	       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p)))
			       (ACL2::+ (deg p1)
					(ACL2::- (deg p))))
	       (quot
		(+ p1
		   (- (FUPOL::*-monomio
		       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p)))
				       (ACL2::+ (deg p1)
						(ACL2::- (deg p))))
		       p)))
		p))
	      (FUPOL::+-monomio
	       (FUMON::monomio (FLD::* (lc p2) (FLD::/ (lc p)))
			       (ACL2::+ (deg p2)
					(ACL2::- (deg p))))
	       (quot
		(+ p2
		   (- (FUPOL::*-monomio
		       (FUMON::monomio (FLD::* (lc p2) (FLD::/ (lc p)))
				       (ACL2::+ (deg p2)
						(ACL2::- (deg p))))
		       p)))
		p))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc
			       |=-implies-=-FUPOL::+-monomio-2a|
			       |=-implies-=-FUPOL::+-monomio-2b|
			       FUPOL::|FUMON::=-implies-=P-+-monomio-1|
			       )
	   :use ((:instance
		  =-implies-=-quot-1-lemma-5
		  (m1 (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p)))))
		  (m2 (FUMON::monomio (FLD::* (lc p2) (FLD::/ (lc p)))
				      (ACL2::+ (deg p2)
					       (ACL2::- (deg p)))))
		  (p1 (quot
		       (+ p1
			  (- (FUPOL::*-monomio
			      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p)))
					      (ACL2::+ (deg p1)
						       (ACL2::- (deg p))))
			      p)))
		       p))
		  (p2 (quot
		       (+ p2
			  (- (FUPOL::*-monomio
			      (FUMON::monomio (FLD::* (lc p2) (FLD::/ (lc p)))
					      (ACL2::+ (deg p2)
						       (ACL2::- (deg p))))
			      p)))
		       p)))
		 =-implies-=-quot-1-lemma-3))))

(defthm
  =-implies-=-quot-1-lemma-7
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(polinomiop p1)
		(polinomiop p2)
		(ACL2::>= (deg p1)
			  (deg p2)))
	   (equal (quot p1 p2)
		  (FUPOL::+-monomio
		   (FUMON::monomio (FLD::* (lc p1)
					   (FLD::/ (lc p2)))
				   (ACL2::- (deg p1)
					    (deg p2)))
		   (quot (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1)
							(FLD::/ (lc p2)))
						(ACL2::- (deg p1)
							 (deg p2)))
				p2)))
			 p2))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (e/d (nulo)
			   (deg lc (:definition quot)))
	   :use (:definition quot))))

(defthm
  =-implies-=-quot-1-lemma-8
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(not (= p  (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(FUPOL::ordenadop p)
		(<= (deg p) (deg p1))
		(<= (deg p) (deg p2))
		(= p1 p2)
		(=
		 (quot
		  (+ p1
		     (- (FUPOL::*-monomio
			 (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p)))
					 (ACL2::+ (deg p1)
						  (ACL2::- (deg p))))
			 p)))
		  p)
		 (quot
		  (+ p2
		     (- (FUPOL::*-monomio
			 (FUMON::monomio (FLD::* (lc p2) (FLD::/ (lc p)))
					 (ACL2::+ (deg p2)
						  (ACL2::- (deg p))))
			 p)))
		  p)))
	   (= (quot p1 p)
	      (quot p2 p)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (e/d (nulo)
			   (deg lc (:definition quot)))
	   :use (=-implies-=-quot-1-lemma-6
		 (:instance
		  =-implies-=-quot-1-lemma-7
		  (p2 p))
		 (:instance
		  =-implies-=-quot-1-lemma-7
		  (p1 p2)
		  (p2 p))))))

(defthm
  =-implies-=-quot-1-lemma-9
  (implies (and (not (= p1 (nulo)))
		(not (= p  (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p)
		(<= (deg p) (deg p1))
		(= p1 p2)
		(=
		 (quot
		  (+ p1
		     (- (FUPOL::*-monomio
			 (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p)))
					 (ACL2::+ (deg p1)
						  (ACL2::- (deg p))))
			 p)))
		  p)
		 (quot
		  (+ p2
		     (- (FUPOL::*-monomio
			 (FUMON::monomio (FLD::* (lc p2) (FLD::/ (lc p)))
					 (ACL2::+ (deg p2)
						  (ACL2::- (deg p))))
			 p)))
		  p)))
	   (= (quot p1 p)(quot p2 p)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUPOL::+-monomio
			       quot FUPOL::ordenadop
			       =-implies-equal-deg-a
			       =-implies-equal-deg-b)
	   :use (=-implies-=-quot-1-lemma-8
		 =-implies-equal-deg-a))))

(defthm
  =-implies-=-quot-1
  (implies (= p1 p2)
	   (= (quot p1 p)
	      (quot p2 p)))
  :rule-classes :congruence
  :hints (("Goal"
	   :in-theory (disable deg lc)
	   :induct (quot-induct-hint p1 p2 p))
	  ("Subgoal *1/1"
	   :use (=-implies-=-quot-1-lemma-4
		 =-implies-=-quot-1-lemma-9))))

(defthm
  =-implies-=-quot-2-lemma-1
  (implies (and (ACL2::< (deg p)(deg p1))
		(= (double-rewrite p1)
		   (double-rewrite p2)))
	   (= (quot p p2)(nulo)))
  :hints (("Goal"
	   :in-theory (disable deg
			       =-implies-equal-deg-a
			       =-implies-equal-deg-b)
	   :use =-implies-equal-deg-b)))

(defthm
  =-implies-=-quot-2-lemma-2
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(not (= p (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(FUPOL::ordenadop p)
		(<= (deg p1)(deg p))
		(<= (deg p2)(deg p))
		(equal (deg p1)(deg p2))
		(= p1 p2))
	   (FUMON::= (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
				     (ACL2::+ (deg p)
					      (ACL2::- (deg p1))))
		     (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p2)))
				     (ACL2::+ (deg p)
					      (ACL2::- (deg p2))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable = FUMON::=))))

(defthm
  =-implies-=-quot-2-lemma-3
  (implies (and (not (= p1 (nulo)))
		(not (= p (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p)
		(<= (deg p1)(deg p))
		(= p1 p2))
	   (FUMON::= (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
				     (ACL2::+ (deg p)
					      (ACL2::- (deg p1))))
		     (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p2)))
				     (ACL2::+ (deg p)
					      (ACL2::- (deg p2))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc
			       =-implies-equal-deg-a
			       =-implies-equal-deg-b)
	   :use (=-implies-=-quot-2-lemma-2
		 =-implies-equal-deg-a))))

(defthm
  =-implies-=-quot-2-lemma-4
  (implies (and (FUMON::= m1 m2)
		(= p1 p2))
	   (= (quot (+ p (- (FUPOL::*-monomio m1 p1)))
		    p2)
	      (quot (+ p (- (FUPOL::*-monomio m2 p2)))
		    p2)))
  :rule-classes nil)

(defthm
  =-implies-=-quot-2-lemma-5
  (implies (and (not (= p1 (nulo)))
		(not (= p (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p)
		(<= (deg p1)(deg p))
		(= p1 p2))
	   (= (quot (+ p
		       (-
			(FUPOL::*-monomio
			 (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
					 (ACL2::+ (deg p)
						  (ACL2::- (deg p1))))
			 p1)))
		    p2)
	      (quot (+ p
		       (-
			(FUPOL::*-monomio
			 (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p2)))
					 (ACL2::+ (deg p)
						  (ACL2::- (deg p2))))
			 p2)))
		    p2)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc)
	   :use (=-implies-=-quot-2-lemma-3
		 (:instance
		  =-implies-=-quot-2-lemma-4
		  (m1 (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
				      (ACL2::+ (deg p)
					       (ACL2::- (deg p1)))))
		  (m2 (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p2)))
				      (ACL2::+ (deg p)
					       (ACL2::- (deg p2))))))))))

(defthm
  =-implies-=-quot-2-lemma-6
  (implies (and (not (= p1 (nulo)))
		(not (= p (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p)
		(<= (deg p1)(deg p))
		(= p1 p2)
		(= (quot (+ p
			    (-
			     (FUPOL::*-monomio
			      (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
					      (ACL2::+ (deg p)
						       (ACL2::- (deg p1))))
			      p1)))
			 p1)
		   (quot (+ p
			    (-
			     (FUPOL::*-monomio
			      (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
					      (ACL2::+ (deg p)
						       (ACL2::- (deg p1))))
			      p1)))
			 p2)))
	   (= (quot (+ p
		       (-
			(FUPOL::*-monomio
			 (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
					 (ACL2::+ (deg p)
						  (ACL2::- (deg p1))))
			 p1)))
		    p1)
	      (quot (+ p
		       (-
			(FUPOL::*-monomio
			 (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p2)))
					 (ACL2::+ (deg p)
						  (ACL2::- (deg p2))))
			 p2)))
		    p2)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc)
	   :use =-implies-=-quot-2-lemma-5)))

(defthm
  =-implies-=-quot-2-lemma-7
  (implies (and (FUMON::= m1 m2)
		(= p1 p2)
		(polinomiop p1))
	   (= (FUPOL::+-monomio m1 p1)
	      (FUPOL::+-monomio m2 p2)))
  :rule-classes nil)

(defthm
  =-implies-=-quot-2-lemma-8
  (implies (and (not (= p1 (nulo)))
		(not (= p (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p)
		(<= (deg p1)(deg p))
		(= p1 p2)
		(= (quot (+ p
			    (-
			     (FUPOL::*-monomio
			      (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
					      (ACL2::+ (deg p)
						       (ACL2::- (deg p1))))
			      p1)))
			 p1)
		   (quot (+ p
			    (-
			     (FUPOL::*-monomio
			      (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
					      (ACL2::+ (deg p)
						       (ACL2::- (deg p1))))
			      p1)))
			 p2)))
	   (= (FUPOL::+-monomio
	       (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
			       (ACL2::+ (deg p)
					(ACL2::- (deg p1))))
	       (quot (+ p
			(-
			 (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
					  (ACL2::+ (deg p)
						   (ACL2::- (deg p1))))
			  p1)))
		     p1))
	      (FUPOL::+-monomio
	       (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p2)))
			       (ACL2::+ (deg p)
					(ACL2::- (deg p2))))
	       (quot (+ p
			(-
			 (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p)
						   (ACL2::- (deg p2))))
			  p2)))
		     p2))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc
			       FUPOL::|FUMON::=-implies-=P-+-monomio-1|
			       |=-implies-=-FUPOL::+-monomio-2a|
			       |=-implies-=-FUPOL::+-monomio-2b|
			       )
	   :use (=-implies-=-quot-2-lemma-3
		 =-implies-=-quot-2-lemma-6
		 (:instance
		  =-implies-=-quot-2-lemma-7
		  (m1 (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
				      (ACL2::+ (deg p)
					       (ACL2::- (deg p1)))))
		  (m2 (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p2)))
				      (ACL2::+ (deg p)
					       (ACL2::- (deg p2)))))
		  (p1 (quot (+ p
			       (-
				(FUPOL::*-monomio
				 (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
						 (ACL2::+ (deg p)
							  (ACL2::- (deg p1))))
				 p1)))
			    p1))
		  (p2 (quot (+ p
			       (-
				(FUPOL::*-monomio
				 (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p2)))
						 (ACL2::+ (deg p)
							  (ACL2::- (deg p2))))
				 p2)))
			    p2)))))))

(defthm
  =-implies-=-quot-2-lemma-9
  (implies (and (not (= p1 (nulo)))
		(not (= p (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p)
		(<= (deg p1)(deg p))
		(= p1 p2)
		(= (quot (+ p
			    (-
			     (FUPOL::*-monomio
			      (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
					      (ACL2::+ (deg p)
						       (ACL2::- (deg p1))))
			      p1)))
			 p1)
		   (quot (+ p
			    (-
			     (FUPOL::*-monomio
			      (FUMON::monomio (FLD::* (lc p) (FLD::/ (lc p1)))
					      (ACL2::+ (deg p)
						       (ACL2::- (deg p1))))
			      p1)))
			 p2)))
	   (= (quot p p1)
	      (quot p p2)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (e/d (nulo)
			   (deg lc (:definition quot)))
	   :use (=-implies-=-quot-2-lemma-8
		 (:instance
		  =-implies-=-quot-1-lemma-7
		  (p1 p)
		  (p2 p1))
		 (:instance
		  =-implies-=-quot-1-lemma-7
		  (p1 p))))))

(defthm
  =-implies-=-quot-2
  (implies (= p1 p2)
	   (= (quot p p1)
	      (quot p p2)))
  :rule-classes :congruence
  :hints (("Goal"
	   :in-theory (disable deg lc))
	  ("Subgoal *1/1"
	   :use =-implies-=-quot-2-lemma-9)))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-1|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(equal
		 (deg
		  (quot
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))
		   p2))
		 (ACL2::+
		  (ACL2::- (deg p2))
		  (deg
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))))))
	   (ACL2::< (deg
		     (quot
		      (+ p1
			 (- (FUPOL::*-monomio
			     (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					     (ACL2::+ (deg p1)
						      (ACL2::- (deg p2))))
			     p2)))
		      p2))
		    (ACL2::+ (deg p1)
			     (ACL2::- (deg p2)))))
  :rule-classes nil
  :hints (("Goal"
	  :in-theory
	  (disable deg lc
		   |deg (p1 + (- (m FUPOL::*-monomio p2))) ACL2::< deg p1|)
	  :use |deg (p1 + (- (m FUPOL::*-monomio p2))) ACL2::< deg p1|)))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-2|
  (implies (and (FUMON::monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(> (FUMON::termino m)
		   (FUMON::termino (primero p))))
	   (equal (primero (FUPOL::+-monomio m p))
		  m))
  :hints (("Goal"
	   :in-theory (e/d (FUTER::<)
			   (FUPOL::|primero p FUMON::< m => >-monomio m p|))
	   :use (:instance
		 FUPOL::|primero p FUMON::< m => >-monomio m p|
		 (FUPOL::m m)
		 (FUPOL::p p)))))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
  (implies (and (not (= (double-rewrite p1)(nulo)))
		(not (= (double-rewrite p2)(nulo)))
		(FUPOL::ordenadop (double-rewrite p1))
		(FUPOL::ordenadop (double-rewrite p2))
		(<= (deg p2) (deg p1)))
	   (FUMON::monomiop (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					    (ACL2::+ (deg p1)
						     (ACL2::- (deg p2))))))
  :hints (("Goal"
	   :in-theory (enable nulo FUTER::terminop FUMON::monomiop
			      FUMON::monomio FUMON::termino
			      FUMON::coeficiente))))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|
  (implies (and (not (= (double-rewrite p1)(nulo)))
		(not (= (double-rewrite p2)(nulo)))
		(FUPOL::ordenadop (double-rewrite p1))
		(FUPOL::ordenadop (double-rewrite p2))
		(<= (deg p2) (deg p1)))
	   (not (FUMON::nulop (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					      (ACL2::+ (deg p1)
						       (ACL2::- (deg p2)))))))
  :hints (("Goal"
	   :in-theory (enable nulo FUTER::terminop FUMON::monomiop
			      FUMON::monomio FUMON::coeficiente))))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
  (implies (and (not (= (double-rewrite p1)(nulo)))
		(not (= (double-rewrite p2)(nulo)))
		(FUPOL::ordenadop (double-rewrite p1))
		(FUPOL::ordenadop (double-rewrite p2))
		(<= (deg p2) (deg p1)))
	   (equal (FUMON::termino (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						  (ACL2::+ (deg p1)
							   (ACL2::- (deg p2)))))
		  (ACL2::+ (deg p1)
			   (ACL2::- (deg p2)))))
  :hints (("Goal"
	   :in-theory (enable nulo FUTER::terminop FUMON::monomiop
			      FUMON::monomio FUMON::termino
			      FUMON::coeficiente))))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-6|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(equal
		 (deg
		  (quot
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))
		   p2))
		 (ACL2::+
		  (ACL2::- (deg p2))
		  (deg
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))))))
	   (> (FUMON::termino (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					      (ACL2::+ (deg p1)
						       (ACL2::- (deg p2)))))
	      (FUMON::termino
	       (primero (quot (+ p1
				 (- (FUPOL::*-monomio
				     (FUMON::monomio (FLD::* (lc p1)
							     (FLD::/ (lc p2)))
						     (ACL2::+ (deg p1)
							      (ACL2::- (deg p2))))
				     p2)))
			      p2)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
			       FUMON::monomio-coeficiente-termino
			       car-cdr-elim
			       FUPOL::*-monomio
			       FUPOL::ordenadop
			       |p + q = mp(p) +Mo (resto(p) + q)|
			       |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|
			       |- p != 0|
			       |p + (- p) = 0|
			       |p + q = 0 <=> q = - p|
			       |p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|
			       |primero -p FUMON::= FUMON::- primero p|
			       |resto -p = - resto p|
			       =-IMPLIES-=-+-2)
	   :use (|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-1|
		 |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|))))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-7|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(equal
		 (deg
		  (quot
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))
		   p2))
		 (ACL2::+
		  (ACL2::- (deg p2))
		  (deg
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))))))
	   (equal (primero (FUPOL::+-monomio
			    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					    (ACL2::+ (deg p1)
						     (ACL2::- (deg p2))))
			    (quot (+ p1
				     (- (FUPOL::*-monomio
					 (FUMON::monomio (FLD::* (lc p1)
								 (FLD::/ (lc p2)))
							 (ACL2::+ (deg p1)
								  (ACL2::-
								   (deg p2))))
					 p2)))
				  p2)))
		  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				  (ACL2::+ (deg p1)
					   (ACL2::- (deg p2))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable
		       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-2|
		       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
		       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|)
	   :use (|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-6|
		 |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
		 |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|
		 (:instance
		  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-2|
		  (m (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				     (ACL2::+ (deg p1)
					      (ACL2::- (deg p2)))))
		  (p (quot (+ p1
			      (- (FUPOL::*-monomio
				  (FUMON::monomio (FLD::* (lc p1)
							  (FLD::/ (lc p2)))
						  (ACL2::+ (deg p1)
							   (ACL2::-
							    (deg p2))))
				  p2)))
			   p2)))))))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-8|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(equal
		 (deg
		  (quot
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))
		   p2))
		 (ACL2::+
		  (ACL2::- (deg p2))
		  (deg
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))))))
	   (equal (deg (FUPOL::+-monomio
			(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					(ACL2::+ (deg p1)
						 (ACL2::- (deg p2))))
			(quot (+ p1
				 (- (FUPOL::*-monomio
				     (FUMON::monomio (FLD::* (lc p1)
							     (FLD::/ (lc p2)))
						     (ACL2::+ (deg p1)
							      (ACL2::-
							       (deg p2))))
				     p2)))
			      p2)))
		  (ACL2::+ (deg p1)
			   (ACL2::- (deg p2)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
			       FUMON::monomio-coeficiente-termino
			       car-cdr-elim
			       FUPOL::*-monomio
			       FUPOL::ordenadop
			       |p + q = mp(p) +Mo (resto(p) + q)|
			       |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|
			       |- p != 0|
			       |p + (- p) = 0|
			       |p + q = 0 <=> q = - p|
			       |p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|
			       |primero -p FUMON::= FUMON::- primero p|
			       |resto -p = - resto p|
			       =-IMPLIES-=-+-2)
	   :use (|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
		 |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-7|))))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-9|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(= (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))
		   (nulo)))
	   (equal (deg (FUPOL::+-monomio
			(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					(ACL2::+ (deg p1)
						 (ACL2::- (deg p2))))
			(quot (+ p1
				 (- (FUPOL::*-monomio
				     (FUMON::monomio (FLD::* (lc p1)
							     (FLD::/ (lc p2)))
						     (ACL2::+ (deg p1)
							      (ACL2::-
							       (deg p2))))
				     p2)))
			      p2)))
		  (ACL2::+ (deg p1)
			   (ACL2::- (deg p2)))))
  :rule-classes nil
  :hints (("Goal"
	   ;;:do-not-induct t
	   :in-theory (e/d (nulo)
			   (|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
			    |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
			    |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|
			    FUMON::monomio-coeficiente-termino
			    car-cdr-elim
			    FUPOL::*-monomio
			    FUPOL::ordenadop
			    |p + q = mp(p) +Mo (resto(p) + q)|
			    |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|
			    |- p != 0|
			    |p + (- p) = 0|
			    |p + q = 0 <=> q = - p|
			    |p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|
			    |primero -p FUMON::= FUMON::- primero p|
			    |resto -p = - resto p|))
	   :use (|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
		 |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
		 |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|))))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-10|
  (implies (and (not (= p1 nil))
		(not (= p2 nil))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(equal
		 (deg
		  (quot
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))
		   p2))
		 (ACL2::+
		  (ACL2::- (deg p2))
		  (deg
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))))))
	   (equal
	    (deg
	     (FUPOL::+-monomio
	      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
			      (ACL2::+ (deg p1)
				       (ACL2::- (deg p2))))
	      (quot
	       (+ p1
		  (- (FUPOL::*-monomio
		      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p2))))
		      p2)))
	       p2)))
	    (ACL2::+ (deg p1)
		     (ACL2::- (deg p2)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (e/d (nulo)
			   (deg lc
				FUMON::monomio-coeficiente-termino
				car-cdr-elim
				FUPOL::*-monomio
				FUPOL::ordenadop
				|p + q = mp(p) +Mo (resto(p) + q)|
				|(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|
				|- p != 0|
				|p + (- p) = 0|
				|p + q = 0 <=> q = - p|
				|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|
				|primero -p FUMON::= FUMON::- primero p|
				|resto -p = - resto p|
				=-IMPLIES-=-+-2))
	   :use (|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-8|
		 |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-9|))))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-11|
  (implies (and (not (= p1 nil))
		(not (= p2 nil))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(ACL2::<
		 (deg
		  (+ p1
		     (- (FUPOL::*-monomio
			 (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					 (ACL2::+ (deg p1)
						  (ACL2::- (deg p2))))
			 p2))))
		 (deg p2)))
	   (equal
	    (deg
	     (FUPOL::+-monomio
	      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
			      (ACL2::+ (deg p1)
				       (ACL2::- (deg p2))))
	      (quot
	       (+ p1
		  (- (FUPOL::*-monomio
		      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p2))))
		      p2)))
	       p2)))
	    (ACL2::+ (deg p1)
		     (ACL2::- (deg p2)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (e/d (nulo)
			   (|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
			    FUPOL::|mp(m +M p) = m|
			    |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
			    |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|
			    FUMON::monomio-coeficiente-termino
			    car-cdr-elim
			    FUPOL::*-monomio
			    FUPOL::ordenadop
			    |p + q = mp(p) +Mo (resto(p) + q)|
			    |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|
			    |- p != 0|
			    |p + (- p) = 0|
			    |p + q = 0 <=> q = - p|
			    |p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|
			    |primero -p FUMON::= FUMON::- primero p|
			    |resto -p = - resto p|
			    =-IMPLIES-=-+-2))
	  :use (|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
		(:instance
		 FUPOL::|mp(m +M p) = m|
		 (FUPOL::m (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2)))))
		 (FUPOL::p nil))
		|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
		|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|))))

(defthm
  |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)|
  (implies (and (not (= (double-rewrite p1)(nulo)))
		(not (= (double-rewrite p2)(nulo)))
		(polinomiop (double-rewrite p1))
		(polinomiop (double-rewrite p2))
		(ACL2::>= (deg p1)
			  (deg p2)))
	   (equal (deg (quot p1 p2))
		  (ACL2::- (deg p1)
			   (deg p2))))
  :hints (("Goal"
	   :in-theory (e/d (nulo)
			   (deg lc)))
	  ("Subgoal *1/4''"
	   :use |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-10|)
	  ("Subgoal *1/3''"
	   :use |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-11|)
	  ("Subgoal *1/1'"
	   :use |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-9|)))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-1|
  (implies (and (common-lisp::< (deg p1) (deg p2))
		(FUPOL::ordenadop (double-rewrite p1)))
	   (ACL2::< (deg (+ p1 (nulo)))
		    (deg p2)))
  :hints (("Goal"
	   :in-theory (disable deg
			       =-implies-equal-deg-a
			       =-implies-equal-deg-b)
	   :use (:instance
		 =-implies-equal-deg-b
		 (p1 (+ p1 (nulo)))
		 (p2 p1)))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-2|
  (implies (and (FUMON::monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(FUPOL::ordenadop (double-rewrite p))
		(> (FUMON::termino m)
		   (FUMON::termino (primero p))))
	   (equal (resto (FUPOL::+-monomio m p))
		  p))
  :hints (("Goal"
	   :in-theory (enable FUTER::<))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-3|
    (implies (and (polinomiop p)
		(not (nulop p)))
	   (= (* p q)
	      (+ (FUPOL::*-monomio (primero p) q)
		 (* (resto p) q))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable * + =)
	   :use (:instance
		 FUPOL::|p + q = p + fn(q)|
		 (FUPOL::p (FUPOL::*-monomio (primero p) q))
		 (FUPOL::q (FUPOL::* (resto p) q))))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-4|
  (implies (and (FUMON::monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(polinomiop (double-rewrite q))
		(> (FUMON::termino m)
		   (FUMON::termino (primero q))))
	   (= (* p (FUPOL::+-monomio m q))
	      (+ (FUPOL::*-monomio m p)
		 (* p q))))
  :hints (("Goal"
	   :use (:instance
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-3|
                 (p (FUPOL::+-monomio m q))
		 (q p)))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-5|
  (implies (and (FUMON::monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(polinomiop (double-rewrite q))
		(> (FUMON::termino m)
		   (FUMON::termino (primero q))))
	   (equal (deg (+ p1 (- (* p2 (FUPOL::+-monomio m q)))))
		  (deg (+ p1 (+ (- (FUPOL::*-monomio m p2))
				(- (* p2 q)))))))
  :hints (("Goal"
	   :in-theory (disable deg))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-6|
  (implies (and (not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(not (= p2 (nulo)))
		(polinomiop (+ p1
			       (- (FUPOL::*-monomio
				   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						   (ACL2::+ (deg p1)
							    (ACL2::- (deg p2))))
				   p2))))
		(polinomiop p2)
		(>= (deg (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						(ACL2::+ (deg p1)
							 (ACL2::- (deg p2))))
				p2))))
		    (deg p2)))
	   (equal (deg (quot (+ p1
				(- (FUPOL::*-monomio
				    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						    (ACL2::+ (deg p1)
							     (ACL2::- (deg p2))))
				   p2)))
			     p2))
		  (ACL2::+ (ACL2::- (deg p2))
			   (deg
			    (+ p1
			       (- (FUPOL::*-monomio
				   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						   (ACL2::+ (deg p1)
							    (ACL2::- (deg p2))))
				   p2)))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-7|
  (implies (and (not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(not (= p2 (nulo)))
                (polinomiop p2)
		(>= (deg (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						(ACL2::+ (deg p1)
							 (ACL2::- (deg p2))))
				p2))))
		    (deg p2)))
	   (equal (deg (quot (+ p1
				(- (FUPOL::*-monomio
				    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						    (ACL2::+ (deg p1)
							     (ACL2::- (deg p2))))
				   p2)))
			     p2))
		  (ACL2::+ (ACL2::- (deg p2))
			   (deg
			    (+ p1
			       (- (FUPOL::*-monomio
				   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						   (ACL2::+ (deg p1)
							    (ACL2::- (deg p2))))
				   p2)))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc)
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-6|)))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-8|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(>= (deg (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						(ACL2::+ (deg p1)
							 (ACL2::- (deg p2))))
				p2))))
		    (deg p2)))
	   (ACL2::< (deg
		     (quot
		      (+ p1
			 (- (FUPOL::*-monomio
			     (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					     (ACL2::+ (deg p1)
						      (ACL2::- (deg p2))))
			     p2)))
		      p2))
		    (ACL2::+ (deg p1)
			     (ACL2::- (deg p2)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc
			       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)|)
	   :use (|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-1|
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-7|))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-9|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(>= (deg (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						(ACL2::+ (deg p1)
							 (ACL2::- (deg p2))))
				p2))))
		    (deg p2)))
	   (ACL2::< (deg
		     (quot
		      (+ p1
			 (- (FUPOL::*-monomio
			     (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					     (ACL2::+ (deg p1)
						      (ACL2::- (deg p2))))
			     p2)))
		      p2))
		    (FUMON::termino
		     (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				     (ACL2::+ (deg p1)
					      (ACL2::- (deg p2)))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory
	   (disable deg lc
		    FUPOL::ORDENADOP
		    FUPOL::*-monomio
		    |p + (- p) = 0|
		    |p + q = 0 <=> q = - p|
		    |p + q = mp(p) +Mo (resto(p) + q)|
		    |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
		    |deg(p + q) ACL2::< deg(p)|
		    |(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|
		    |- (m FUPOL::*-monomio p2) != 0|
		    |primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|
		    |- p != 0|
		    FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO
		    |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)|
		    |m FUPOL::*-monomio p2 != 0|
		    |p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|
		    |p1 = 0 => quot(p1 p2) =e 0|
		    |polinomiop (m FUPOL::*-monomio p2)|
		    |primero -p FUMON::= FUMON::- primero p|
		    |primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|)
	   :use (|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-8|
		 (:instance
		  (:theorem
		   (implies (and (ACL2::< a b)
				 (equal c b))
			    (ACL2::< a c)))
		  (a (deg
		      (quot
		       (+ p1
			  (- (FUPOL::*-monomio
			      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					      (ACL2::+ (deg p1)
						       (ACL2::- (deg p2))))
			      p2)))
		       q2)))
		  (b (ACL2::+ (deg p1)
			      (ACL2::- (deg p2))))
		  (c (FUMON::termino
		      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p2)))))))))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-10|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(>= (deg (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						(ACL2::+ (deg p1)
							 (ACL2::- (deg p2))))
				p2))))
		    (deg p2)))
	   (ACL2::< (FUMON::termino
		     (primero
		      (quot
		       (+ p1
			  (- (FUPOL::*-monomio
			      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					      (ACL2::+ (deg p1)
						       (ACL2::- (deg p2))))
			      p2)))
		       p2)))
		     (FUMON::termino
		      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p2)))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable lc FUPOL::ordenadop)
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-9|)))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-11|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(>= (deg (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						(ACL2::+ (deg p1)
							 (ACL2::- (deg p2))))
				p2))))
		    (deg p2)))
	   (and (FUMON::monomiop (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						 (ACL2::+ (deg p1)
							  (ACL2::- (deg p2)))))
		(not (FUMON::nulop (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						   (ACL2::+ (deg p1)
							    (ACL2::- (deg p2))))))
		(ACL2::< (FUMON::termino
			  (primero
			   (quot
			    (+ p1
			       (- (FUPOL::*-monomio
				   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						   (ACL2::+ (deg p1)
							    (ACL2::- (deg p2))))
				   p2)))
			    p2)))
			 (FUMON::termino
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
			       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|
			       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|)
	   :use (|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
		 |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-10|))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-12|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(>= (deg (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						(ACL2::+ (deg p1)
							 (ACL2::- (deg p2))))
				p2))))
		    (deg p2)))
	   (equal (deg (+ p1 (- (* p2
				   (FUPOL::+-monomio
				    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						    (ACL2::+ (deg p1)
							     (ACL2::- (deg p2))))
				    (quot
				     (+ p1
					(- (FUPOL::*-monomio
					    (FUMON::monomio (FLD::* (lc p1)
								    (FLD::/ (lc p2)))
							    (ACL2::+ (deg p1)
								     (ACL2::-
								      (deg p2))))
					    p2)))
				     p2))))))
		  (deg (+ p1 (+ (- (FUPOL::*-monomio
				    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						    (ACL2::+ (deg p1)
							     (ACL2::- (deg p2))))
				    p2))
				(- (* p2
				      (quot
				       (+ p1
					  (- (FUPOL::*-monomio
					      (FUMON::monomio
					       (FLD::* (lc p1)
						       (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
					      p2)))
				       p2))))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       |deg rem(p1 p2) ACL2::< deg p2-lemma-5|
			       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
			       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|
			       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|)
	   :use (|deg rem(p1 p2) ACL2::< deg p2-lemma-11|
		 (:instance
		  |deg rem(p1 p2) ACL2::< deg p2-lemma-5|
		  (m (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				     (ACL2::+ (deg p1)
					      (ACL2::- (deg p2)))))
		  (q (quot
		      (+ p1
			 (- (FUPOL::*-monomio
			     (FUMON::monomio
			      (FLD::* (lc p1)
				      (FLD::/ (lc p2)))
			      (ACL2::+ (deg p1)
				       (ACL2::- (deg p2))))
			     p2)))
		      p2)))))))

(defthm
  |nil * p =e nil|
  (equal (* nil p) nil)
  :hints (("Goal"
	   :in-theory (e/d (nulo)
			   (|0 * p =e 0|))
	   :use |0 * p =e 0|)))

(defthm
  |p * nil =e nil|
  (equal (* p nil) nil)
  :hints (("Goal"
	   :in-theory (e/d (nulo)
			   (|p * 0 =e 0|))
	   :use |p * 0 =e 0|)))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-13|
  (implies (and (FUMON::monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(polinomiop (double-rewrite p)))
	   (= (* p (FUPOL::+-monomio m (nulo)))
	      (FUPOL::*-monomio m p)))
  :hints (("Goal"
	   :use (:instance
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-3|
                 (p (FUPOL::+-monomio m (nulo)))
		 (q p)))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-14|
  (implies (and (FUMON::monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(polinomiop (double-rewrite p))
		(equal q (nulo)))
	   (= (* p (FUPOL::+-monomio m q))
	      (+ (FUPOL::*-monomio m p)
		 (* p q))))
  :hints (("Goal"
	   :in-theory (disable |deg rem(p1 p2) ACL2::< deg p2-lemma-13|)
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-13|)))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-15|
  (implies (and (FUMON::monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(polinomiop (double-rewrite p2))
		(equal q (nulo)))
	   (= (- (* p2 (FUPOL::+-monomio m q)))
	      (+ (- (FUPOL::*-monomio m p2))
		 (- (* p2 q)))))
  :hints (("Goal"
	   :in-theory (disable |deg rem(p1 p2) ACL2::< deg p2-lemma-14|)
	   :use (:instance
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-14|
		 (p p2)))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-16|
  (implies (and (FUMON::monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(polinomiop (double-rewrite p2))
		(equal q (nulo)))
	   (= (+ p1
		 (- (* p2 (FUPOL::+-monomio m q))))
	      (+ p1
		 (+ (- (FUPOL::*-monomio m p2))
		    (- (* p2 q))))))
    :hints (("Goal"
	   :in-theory (disable |deg rem(p1 p2) ACL2::< deg p2-lemma-15|)
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-15|)))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-17|
  (implies (and (FUMON::monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(polinomiop (double-rewrite p2))
		(equal q (nulo)))
	   (equal (deg (+ p1
			  (- (* p2 (FUPOL::+-monomio m q)))))
		  (deg (+ p1
			  (+ (- (FUPOL::*-monomio m p2))
			     (- (* p2 q)))))))
    :hints (("Goal"
	   :in-theory (disable deg
			       |deg rem(p1 p2) ACL2::< deg p2-lemma-16|)
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-16|)))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-18|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(= (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))
		   (nulo)))
	   (equal (deg (+ p1 (- (* p2
				   (FUPOL::+-monomio
				    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						    (ACL2::+ (deg p1)
							     (ACL2::- (deg p2))))
				    (quot
				     (+ p1
					(- (FUPOL::*-monomio
					    (FUMON::monomio (FLD::* (lc p1)
								    (FLD::/ (lc p2)))
							    (ACL2::+ (deg p1)
								     (ACL2::-
								      (deg p2))))
					    p2)))
				     p2))))))
		  (deg (+ p1 (+ (- (FUPOL::*-monomio
				    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						    (ACL2::+ (deg p1)
							     (ACL2::- (deg p2))))
				    p2))
				(- (* p2
				      (quot
				       (+ p1
					  (- (FUPOL::*-monomio
					      (FUMON::monomio
					       (FLD::* (lc p1)
						       (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
					      p2)))
				       p2))))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       |deg rem(p1 p2) ACL2::< deg p2-lemma-17|)
	   :use (:instance
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-17|
		 (m (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				    (ACL2::+ (deg p1)
					     (ACL2::- (deg p2)))))
		 (q (quot
		     (+ p1
			(- (FUPOL::*-monomio
			    (FUMON::monomio
			     (FLD::* (lc p1)
				     (FLD::/ (lc p2)))
			     (ACL2::+ (deg p1)
				      (ACL2::- (deg p2))))
			    p2)))
		     p2))))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-19|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(ACL2::< (deg (+ p1
				 (- (FUPOL::*-monomio
				     (FUMON::monomio (FLD::* (lc p1)
							     (FLD::/ (lc p2)))
						     (ACL2::+ (deg p1)
							      (ACL2::- (deg p2))))
				     p2))))
			 (deg p2)))
	   (equal (deg (+ p1 (- (* p2
				   (FUPOL::+-monomio
				    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						    (ACL2::+ (deg p1)
							     (ACL2::- (deg p2))))
				    (quot
				     (+ p1
					(- (FUPOL::*-monomio
					    (FUMON::monomio (FLD::* (lc p1)
								    (FLD::/ (lc p2)))
							    (ACL2::+ (deg p1)
								     (ACL2::-
								      (deg p2))))
					    p2)))
				     p2))))))
		  (deg (+ p1 (+ (- (FUPOL::*-monomio
				    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						    (ACL2::+ (deg p1)
							     (ACL2::- (deg p2))))
				    p2))
				(- (* p2
				      (quot
				       (+ p1
					  (- (FUPOL::*-monomio
					      (FUMON::monomio
					       (FLD::* (lc p1)
						       (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
					      p2)))
				       p2))))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       |deg rem(p1 p2) ACL2::< deg p2-lemma-17|)
	   :use (:instance
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-17|
		 (m (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				    (ACL2::+ (deg p1)
					     (ACL2::- (deg p2)))))
		 (q (quot
		     (+ p1
			(- (FUPOL::*-monomio
			    (FUMON::monomio
			     (FLD::* (lc p1)
				     (FLD::/ (lc p2)))
			     (ACL2::+ (deg p1)
				      (ACL2::- (deg p2))))
			    p2)))
		     p2))))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-20|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1)))
	   (equal (deg (+ p1 (- (* p2
				   (FUPOL::+-monomio
				    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						    (ACL2::+ (deg p1)
							     (ACL2::- (deg p2))))
				    (quot
				     (+ p1
					(- (FUPOL::*-monomio
					    (FUMON::monomio (FLD::* (lc p1)
								    (FLD::/ (lc p2)))
							    (ACL2::+ (deg p1)
								     (ACL2::-
								      (deg p2))))
					    p2)))
				     p2))))))
		  (deg (+ p1 (+ (- (FUPOL::*-monomio
				    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						    (ACL2::+ (deg p1)
							     (ACL2::- (deg p2))))
				    p2))
				(- (* p2
				      (quot
				       (+ p1
					  (- (FUPOL::*-monomio
					      (FUMON::monomio
					       (FLD::* (lc p1)
						       (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
					      p2)))
				       p2))))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       FUPOL::+-monomio)
	   :use (|deg rem(p1 p2) ACL2::< deg p2-lemma-12|
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-18|
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-19|))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-21|
  (equal (deg (+ p1 (+ (- (FUPOL::*-monomio
			   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2))))
			   p2))
		       (- (* p2
			     (quot
			      (+ p1
				 (- (FUPOL::*-monomio
				     (FUMON::monomio
				      (FLD::* (lc p1)
					      (FLD::/ (lc p2)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p2))))
				     p2)))
			      p2))))))
	 (deg (+ (+ p1
		    (- (FUPOL::*-monomio
			(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					(ACL2::+ (deg p1)
						 (ACL2::- (deg p2))))
			p2)))
		 (- (* p2
		       (quot
			(+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio
				(FLD::* (lc p1)
					(FLD::/ (lc p2)))
				(ACL2::+ (deg p1)
					 (ACL2::- (deg p2))))
			       p2)))
			p2))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       FUPOL::+-monomio))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-22|
  (implies (and (not (= p1 nil))
		(not (= p2 nil))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(ACL2::<
		 (deg
		  (+
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))
		   (-
		    (*
		     p2
		     (quot
		      (+
		       p1
		       (- (FUPOL::*-monomio
			   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2))))
			   p2)))
		      p2)))))
		 (deg p2)))
	   (ACL2::<
	    (deg
	     (+
	      p1
	      (-
	       (*
		p2
		(FUPOL::+-monomio
		 (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				 (ACL2::+ (deg p1)
					  (ACL2::- (deg p2))))
		 (quot
		  (+
		   p1
		   (- (FUPOL::*-monomio
		       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				       (ACL2::+ (deg p1)
						(ACL2::- (deg p2))))
		       p2)))
		  p2))))))
	    (deg p2)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (e/d (nulo)
			   (deg lc FUPOL::*-monomio FUMON::nulop
			       FUPOL::+-monomio))
	   :use (|deg rem(p1 p2) ACL2::< deg p2-lemma-20|
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-21|
		 (:instance
		  (:theorem
		   (implies (and (equal c d)
				 (equal d a)
				 (ACL2::< a b))
			    (ACL2::< c b)))
		  (a (deg
		      (+
		       (+ p1
			  (- (FUPOL::*-monomio
			      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					      (ACL2::+ (deg p1)
						       (ACL2::- (deg p2))))
			      p2)))
		       (-
			(*
			 p2
			 (quot
			  (+
			   p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			  p2))))))
		  (b (deg p2))
		  (c (deg
		      (+
		       p1
		       (-
			(*
			 p2
			 (FUPOL::+-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  (quot
			   (+
			    p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						(ACL2::+ (deg p1)
							 (ACL2::- (deg p2))))
				p2)))
			   p2)))))))
		  (d (deg (+ p1 (+ (- (FUPOL::*-monomio
				       (FUMON::monomio (FLD::* (lc p1)
							       (FLD::/ (lc p2)))
						       (ACL2::+ (deg p1)
								(ACL2::- (deg p2))))
				       p2))
				   (- (* p2
					 (quot
					  (+ p1
					     (- (FUPOL::*-monomio
						 (FUMON::monomio
						  (FLD::* (lc p1)
							  (FLD::/ (lc p2)))
						  (ACL2::+ (deg p1)
							   (ACL2::- (deg p2))))
						 p2)))
					  p2))))))))))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-23|
  (implies (and (FUMON::monomiop (double-rewrite m))
		(not (FUMON::nulop m))
		(polinomiop (double-rewrite q))
		(> (FUMON::termino m)
		   (FUMON::termino (primero q))))
	   (= (+ p1
		 (- (* p2 (FUPOL::+-monomio m q))))
	      (+ p1
		 (+ (- (FUPOL::*-monomio m p2))
		    (- (* p2 q)))))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-24|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(not (= (+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
			(nulo)))
		(>= (deg (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						(ACL2::+ (deg p1)
							 (ACL2::- (deg p2))))
				p2))))
		    (deg p2)))
	   (= (+ p1 (- (* p2
			  (FUPOL::+-monomio
			   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2))))
			   (quot
			    (+ p1
			       (- (FUPOL::*-monomio
				   (FUMON::monomio (FLD::* (lc p1)
							   (FLD::/ (lc p2)))
						   (ACL2::+ (deg p1)
							    (ACL2::-
							     (deg p2))))
				   p2)))
			    p2)))))
	      (+ p1 (+ (- (FUPOL::*-monomio
			   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2))))
			   p2))
		       (- (* p2
			     (quot
			      (+ p1
				 (- (FUPOL::*-monomio
				     (FUMON::monomio
				      (FLD::* (lc p1)
					      (FLD::/ (lc p2)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p2))))
				     p2)))
			      p2)))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
			       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|
			       |deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
			       |deg rem(p1 p2) ACL2::< deg p2-lemma-23|)
	   :use (|deg rem(p1 p2) ACL2::< deg p2-lemma-11|
		 (:instance
		  |deg rem(p1 p2) ACL2::< deg p2-lemma-23|
		  (m (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				     (ACL2::+ (deg p1)
					      (ACL2::- (deg p2)))))
		  (q (quot
		      (+ p1
			 (- (FUPOL::*-monomio
			     (FUMON::monomio
			      (FLD::* (lc p1)
				      (FLD::/ (lc p2)))
			      (ACL2::+ (deg p1)
				       (ACL2::- (deg p2))))
			     p2)))
		      p2)))))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-25|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(= (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					  (ACL2::+ (deg p1)
						   (ACL2::- (deg p2))))
			  p2)))
		   (nulo)))
	   (= (+ p1 (- (* p2
			  (FUPOL::+-monomio
			   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2))))
			   (quot
			    (+ p1
			       (- (FUPOL::*-monomio
				   (FUMON::monomio (FLD::* (lc p1)
							   (FLD::/ (lc p2)))
						   (ACL2::+ (deg p1)
							    (ACL2::-
							     (deg p2))))
				   p2)))
			    p2)))))
	      (+ p1 (+ (- (FUPOL::*-monomio
			   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2))))
			   p2))
		       (- (* p2
			     (quot
			      (+ p1
				 (- (FUPOL::*-monomio
				     (FUMON::monomio
				      (FLD::* (lc p1)
					      (FLD::/ (lc p2)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p2))))
				     p2)))
			      p2)))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       |deg rem(p1 p2) ACL2::< deg p2-lemma-16|)
	   :use (:instance
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-16|
		 (m (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				    (ACL2::+ (deg p1)
					     (ACL2::- (deg p2)))))
		 (q (quot
		     (+ p1
			(- (FUPOL::*-monomio
			    (FUMON::monomio
			     (FLD::* (lc p1)
				     (FLD::/ (lc p2)))
			     (ACL2::+ (deg p1)
				      (ACL2::- (deg p2))))
			    p2)))
		     p2))))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-26|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1))
		(ACL2::< (deg (+ p1
				 (- (FUPOL::*-monomio
				     (FUMON::monomio (FLD::* (lc p1)
							     (FLD::/ (lc p2)))
						     (ACL2::+ (deg p1)
							      (ACL2::- (deg p2))))
				     p2))))
			 (deg p2)))
	   (= (+ p1 (- (* p2
			  (FUPOL::+-monomio
			   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2))))
			   (quot
			    (+ p1
			       (- (FUPOL::*-monomio
				   (FUMON::monomio (FLD::* (lc p1)
							   (FLD::/ (lc p2)))
						   (ACL2::+ (deg p1)
							    (ACL2::-
							     (deg p2))))
				   p2)))
			    p2)))))
	      (+ p1 (+ (- (FUPOL::*-monomio
			   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2))))
			   p2))
		       (- (* p2
			     (quot
			      (+ p1
				 (- (FUPOL::*-monomio
				     (FUMON::monomio
				      (FLD::* (lc p1)
					      (FLD::/ (lc p2)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p2))))
				     p2)))
			      p2)))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       |deg rem(p1 p2) ACL2::< deg p2-lemma-16|)
	   :use (:instance
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-16|
		 (m (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				    (ACL2::+ (deg p1)
					     (ACL2::- (deg p2)))))
		 (q (quot
		     (+ p1
			(- (FUPOL::*-monomio
			    (FUMON::monomio
			     (FLD::* (lc p1)
				     (FLD::/ (lc p2)))
			     (ACL2::+ (deg p1)
				      (ACL2::- (deg p2))))
			    p2)))
		     p2))))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-27|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1)))
	   (= (+ p1 (- (* p2
			  (FUPOL::+-monomio
			   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2))))
			   (quot
			    (+ p1
			       (- (FUPOL::*-monomio
				   (FUMON::monomio (FLD::* (lc p1)
							   (FLD::/ (lc p2)))
						   (ACL2::+ (deg p1)
							    (ACL2::-
							     (deg p2))))
				   p2)))
			    p2)))))
	      (+ p1 (+ (- (FUPOL::*-monomio
			   (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2))))
			   p2))
		       (- (* p2
			     (quot
			      (+ p1
				 (- (FUPOL::*-monomio
				     (FUMON::monomio
				      (FLD::* (lc p1)
					      (FLD::/ (lc p2)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p2))))
				     p2)))
			      p2)))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       FUPOL::+-monomio)
	   :use (|deg rem(p1 p2) ACL2::< deg p2-lemma-24|
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-25|
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-26|))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-28|
  (implies (and (polinomiop c)
		(= p1 a)
		(= (+ p1 (- a))
		   (+ p1 (+ (- b)
			    (- c)))))
	   (= (+ p1 (- b))
	      c))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable |p + q = 0 <=> q = - p|)
	   :use (:instance
		 |p + q = 0 <=> q = - p|
		 (q (+ p1 (- b)))
		 (p (- c))))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-29|
  (implies (and (polinomiop p1)
		(polinomiop a)
		(= (+ p1 (- b))
		   c)
		(= (+ p1 (- a))
		   (+ p1 (+ (- b)
			    (- c)))))
	   (= p1 a))
  :rule-classes nil)

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-30|
  (implies (and (polinomiop p1)
		(polinomiop a)
		(polinomiop c)
		(= (+ p1 (- a))
		   (+ p1 (+ (- b)
			    (- c)))))
	   (equal (= (+ p1 (- b))
		     c)
		  (= p1 a)))
  :rule-classes nil
  :hints (("Goal"
	   :use (|deg rem(p1 p2) ACL2::< deg p2-lemma-28|
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-29|))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-31|
  (implies (and (polinomiop p1)
		(= (+ p1
		      (- (* p2
			    (FUPOL::+-monomio
			     (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					     (ACL2::+ (deg p1)
						      (ACL2::- (deg p2))))
			     (quot
			      (+ p1
				 (- (FUPOL::*-monomio
				     (FUMON::monomio (FLD::* (lc p1)
							     (FLD::/ (lc p2)))
						     (ACL2::+ (deg p1)
							      (ACL2::-
							       (deg p2))))
				     p2)))
			      p2)))))
		   (+ p1 (+ (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
						(ACL2::+ (deg p1)
							 (ACL2::- (deg p2))))
				p2))
			    (- (* p2
				  (quot
				   (+ p1
				      (- (FUPOL::*-monomio
					  (FUMON::monomio
					   (FLD::* (lc p1)
						   (FLD::/ (lc p2)))
					   (ACL2::+ (deg p1)
						    (ACL2::- (deg p2))))
					  p2)))
				   p2)))))))
	   (equal (= (+ p1 (- (FUPOL::*-monomio
			       (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					       (ACL2::+ (deg p1)
							(ACL2::- (deg p2))))
			       p2)))
		     (* p2
			(quot
			 (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio
				 (FLD::* (lc p1)
					 (FLD::/ (lc p2)))
				 (ACL2::+ (deg p1)
					  (ACL2::- (deg p2))))
				p2)))
			 p2)))
		  (= p1 (* p2
			   (FUPOL::+-monomio
			    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					    (ACL2::+ (deg p1)
						     (ACL2::- (deg p2))))
			    (quot
			     (+ p1
				(- (FUPOL::*-monomio
				    (FUMON::monomio (FLD::* (lc p1)
							    (FLD::/ (lc p2)))
						    (ACL2::+ (deg p1)
							     (ACL2::-
							      (deg p2))))
				    p2)))
			     p2))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       FUPOL::+-monomio)
	   :use (:instance
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-30|
		 (a (* p2
		       (FUPOL::+-monomio
			(FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					(ACL2::+ (deg p1)
						 (ACL2::- (deg p2))))
			(quot
			 (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio (FLD::* (lc p1)
							 (FLD::/ (lc p2)))
						 (ACL2::+ (deg p1)
							  (ACL2::-
							   (deg p2))))
				 p2)))
			  p2))))
		 (b (FUPOL::*-monomio
		     (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				     (ACL2::+ (deg p1)
					      (ACL2::- (deg p2))))
		     p2))
		 (c (* p2
		       (quot
			(+ p1
			   (- (FUPOL::*-monomio
			       (FUMON::monomio
				(FLD::* (lc p1)
					(FLD::/ (lc p2)))
				(ACL2::+ (deg p1)
					 (ACL2::- (deg p2))))
			       p2)))
			p2)))))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-32|
  (implies (and (not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(FUPOL::ordenadop p1)
		(FUPOL::ordenadop p2)
		(<= (deg p2) (deg p1)))
	   (equal (= (+ p1
			(- (FUPOL::*-monomio
			    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					    (ACL2::+ (deg p1)
						     (ACL2::- (deg p2))))
			    p2)))
		     (* p2
			(quot
			 (+ p1
			    (- (FUPOL::*-monomio
				(FUMON::monomio
				 (FLD::* (lc p1)
					 (FLD::/ (lc p2)))
				 (ACL2::+ (deg p1)
					  (ACL2::- (deg p2))))
				p2)))
			 p2)))
		  (= p1
		     (* p2
			(FUPOL::+-monomio
			 (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
					 (ACL2::+ (deg p1)
						  (ACL2::- (deg p2))))
			 (quot
			  (+ p1
			     (- (FUPOL::*-monomio
				 (FUMON::monomio (FLD::* (lc p1)
							 (FLD::/ (lc p2)))
						 (ACL2::+ (deg p1)
							  (ACL2::-
							   (deg p2))))
				 p2)))
			  p2))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       FUPOL::+-monomio)
	   :use (|deg rem(p1 p2) ACL2::< deg p2-lemma-27|
		 |deg rem(p1 p2) ACL2::< deg p2-lemma-31|))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-33|
  (not (and (not (= p1 (nulo)))
	    (not (= p2 (nulo)))
	    (FUPOL::ordenadop p1)
	    (FUPOL::ordenadop p2)
	    (<= (deg p2) (deg p1))
	    (= (+ p1
		  (- (FUPOL::*-monomio
		      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p2))))
		      p2)))
	       (* p2
		  (quot
		   (+ p1
		      (- (FUPOL::*-monomio
			  (FUMON::monomio
			   (FLD::* (lc p1)
				   (FLD::/ (lc p2)))
			   (ACL2::+ (deg p1)
				    (ACL2::- (deg p2))))
			  p2)))
		   p2)))
	    (not
	     (= p1
		(* p2
		   (FUPOL::+-monomio
		    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				    (ACL2::+ (deg p1)
					     (ACL2::- (deg p2))))
		    (quot
		     (+ p1
			(- (FUPOL::*-monomio
			    (FUMON::monomio (FLD::* (lc p1)
						    (FLD::/ (lc p2)))
					    (ACL2::+ (deg p1)
						     (ACL2::-
						      (deg p2))))
			    p2)))
		     p2)))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       FUPOL::+-monomio)
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-32|)))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-34|
  (not (and (not (= p1 (nulo)))
	    (not (= p2 (nulo)))
	    (FUPOL::ordenadop p1)
	    (FUPOL::ordenadop p2)
	    (<= (deg p2) (deg p1))
	    (= (+ p1
		  (- (FUPOL::*-monomio
		      (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				      (ACL2::+ (deg p1)
					       (ACL2::- (deg p2))))
		      p2)))
	       (nulo))
	    (not
	     (= p1
		(* p2
		   (FUPOL::+-monomio
		    (FUMON::monomio (FLD::* (lc p1) (FLD::/ (lc p2)))
				    (ACL2::+ (deg p1)
					     (ACL2::- (deg p2))))
		    (quot
		     (+ p1
			(- (FUPOL::*-monomio
			    (FUMON::monomio (FLD::* (lc p1)
						    (FLD::/ (lc p2)))
					    (ACL2::+ (deg p1)
						     (ACL2::-
						      (deg p2))))
			    p2)))
		     p2)))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc FUPOL::*-monomio FUMON::nulop
			       FUPOL::+-monomio)
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-33|)))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-35|
  (implies (and (polinomiop p1)
		(polinomiop p2)
		(not (= p1 (nulo)))
		(not (= p2 (nulo)))
		(not (= p1 (* p2 (quot p1 p2)))))
	   (ACL2::< (deg (+ p1 (- (* p2 (quot p1 p2)))))
		    (deg p2)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable deg lc))
	  ("Subgoal *1/4"
	   :in-theory (e/d (nulo)
			   (deg lc FUMON::nulop FUPOL::*-monomio FUPOL::+-monomio)))
	  ("Subgoal *1/4''"
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-22|)
	  ("Subgoal *1/3.2"
	   :in-theory (disable
		       deg lc FUMON::nulop FUPOL::*-monomio FUPOL::+-monomio)
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-33|)
	  ("Subgoal *1/3.1"
	   :in-theory (e/d (nulo)
			   (deg lc FUMON::nulop FUPOL::*-monomio FUPOL::+-monomio)))
	  ("Subgoal *1/2.2"
	   :in-theory (disable
		       deg lc FUMON::nulop FUPOL::*-monomio FUPOL::+-monomio)
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-34|)
	  ("Subgoal *1/2.1"
	   :in-theory (e/d
		       (nulo)
		       (deg lc FUMON::nulop FUPOL::*-monomio FUPOL::+-monomio)))))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2-lemma-36|
  (implies (and (polinomiop (double-rewrite p1))
		(polinomiop (double-rewrite p2))
		(not (= (double-rewrite p2)(nulo)))
		(not (= (double-rewrite p1)
			(* (double-rewrite p2)
			   (quot (double-rewrite p1)
				 (double-rewrite p2))))))
	   (ACL2::< (deg (+ p1 (- (* p2 (quot p1 p2)))))
		    (deg p2)))
  :rule-classes (:linear :rewrite)
  :hints (("Goal"
	   :in-theory (disable
		       deg lc FUMON::nulop FUPOL::*-monomio FUPOL::+-monomio)
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-35|)))

(defun
  rem (p1 p2)
  (+ p1 (- (* p2 (quot p1 p2)))))

(defthm
  Polinomiop-rem
  (polinomiop (rem p1 p2)))

(defthm
  |(polinomiop p1) & ~(polinomiop p2) => rem(p1 p2) = p1|
  (implies (and (polinomiop (double-rewrite p1))
		(not (polinomiop (double-rewrite p2))))
	   (= (rem p1 p2) p1)))

(defthm
  |(polinomiop p1) & deg p1 < deq p2 => rem(p1 p2) = p1|
  (implies (and (polinomiop (double-rewrite p1))
		(ACL2::< (deg p1)
			 (deg p2)))
	   (= (rem p1 p2) p1)))

(defthm
  |p1 = 0 => rem(p1 p2) = 0|
  (implies (= (double-rewrite p1)(nulo))
	   (= (rem p1 p2)
	      (nulo))))

(defthm
  |(polinomiop p1) & p2 = 0 => rem(p1 p2) = 0|
  (implies (and (polinomiop (double-rewrite p1))
		(= (double-rewrite p2)(nulo)))
	   (= (rem p1 p2) p1)))

(defthm
  |deg rem(p1 p2) ACL2::< deg p2|
  (implies (and (polinomiop (double-rewrite p1))
		(polinomiop (double-rewrite p2))
		(not (= (double-rewrite p2)(nulo)))
		(not (= (rem p1 p2)(nulo))))
	   (ACL2::< (deg (rem p1 p2))
		    (deg p2)))
  :rule-classes (:linear :rewrite :generalize)
  :hints (("Goal"
	   :in-theory (disable
		       deg lc FUMON::nulop FUPOL::*-monomio FUPOL::+-monomio
		       |deg rem(p1 p2) ACL2::< deg p2-lemma-36|)
	   :use |deg rem(p1 p2) ACL2::< deg p2-lemma-36|)))

(defthm
  =-implies-=-rem-1
  (implies (= p1 p2)
	   (= (rem p1 p)
	      (rem p2 p)))
  :rule-classes :congruence)

(defthm
  =-implies-=-rem-2
  (implies (= p1 p2)
	   (= (rem p p1)
	      (rem p p2)))
  :rule-classes :congruence)

(defthm
  quot-rem-elim
  (implies (polinomiop p1)
	   (= (+ (rem p1 p2)
		 (* p2 (quot p1 p2)))
	      p1))
  :rule-classes :elim
  :hints (("Goal"
	   :in-theory (disable
		       deg lc FUMON::nulop FUPOL::*-monomio FUPOL::+-monomio
		       |p + q = mp(p) +Mo (resto(p) + q)|))))

(in-theory (disable deg lc rem))

(defthm
  quot-rem-rewrite
  (implies (polinomiop (double-rewrite p1))
	   (= (+ (rem p1 p2)
		 (* p2 (quot p1 p2)))
	      p1)))
