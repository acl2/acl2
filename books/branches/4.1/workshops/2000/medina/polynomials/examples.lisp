(in-package "POL")

(include-book "congruences-2")

;;; --------
;;; Examples
;;; --------

;;; Equality is preserved when adding the null monomial to a
;;; polynomial.

(defthm polynomial-first-null
  (implies (MON::nullp m)
	   (= (polynomial m p) p)))

;;; Equality is preserved when introducing the addition into a
;;; polynomial.

(defthm +-polynomial
  (= (+ p1 (polynomial m p2)) (polynomial m (+ p1 p2))))


;;; Equality is preserved when adding two consecutive monomials with
;;; the same term to a polynomial.

(defthm polynomial-polynomial-monomial-=-term
  (implies (and (monomialp m1) (monomialp m2) (polynomialp p)
		(TER::= (term m1) (term m2)))
	   (= (polynomial m1 (polynomial m2 p))
	      (polynomial (monomial (COMMON-LISP::+ (coefficient m1) (coefficient m2))
				  (term m1))
			 p))))

;;; If the multiplication of a polynomial and a non-null monomial is
;;; null, then the polynomial is null.

(defthm polynomial-null-*-monomial
  (implies (and (polynomialp p) (monomialp m)
		(equal (*-monomial m p) *null*))
	   (equal p *null*))
  :rule-classes nil)

(encapsulate ()
  (local
    (defthm tecnico
      (implies (and (not (*-monomial m (nf p)))
		    (polynomialp p) (monomialp m))
	       (equal (nf p) *null*))
      :hints (("Goal"
	       :use ((:instance polynomial-null-*-monomial (p (nf p))))))))

  (defthm polynomial-null-*-monomial-nf
    (implies (and (polynomialp p) (uniformp p)
		  (monomialp m) (not (MON::nullp m))
		  (MON::compatiblep m (first p))
		  (= (*-monomial m p) *null*))
	     (= p *null*))
    :rule-classes nil))
