(in-package "POL")

(include-book "addition")

;;; -------------------
;;; Polynomial negation
;;; -------------------

(defun - (p)
  (cond ((or (not (polynomialp p)) (nullp p))
	 *null*)
	(t
	 (polynomial (monomial (COMMON-LISP::- (coefficient (first p)))
			     (term (first p)))
		    (- (rest p))))))

;;; Type rule.

(defthm polynomialp--
  (polynomialp (- p))
  :rule-classes :type-prescription)

;;; Addition of a polynomial to its negative equals to the additive
;;; identity polynomial.

(defthm +--
  (= (+ p (- p)) *null*))

;;; Polynomial negation distributes over addition of monomial and
;;; polynomial.

(defthm --distributes-+-monomial
  (implies (and (monomialp m) (polynomialp p))
	   (equal (- (+-monomial m p))
		  (+-monomial (monomial (COMMON-LISP::- (coefficient m)) (term m))
			     (- p)))))

;;; Polynomial negation distributes over polynomial addition.

(defthm --distributes-+
  (= (- (+ p1 p2)) (+ (- p1) (- p2))))
