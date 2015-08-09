(in-package "POL")

(include-book "polynomial")
(include-book "lexicographical-ordering")

;;; --------------------------------------------------------------------
;;; Polynomial strictly ordered by a decreasing term order without nulls
;;; --------------------------------------------------------------------

(defmacro term-greater-than-leader (m p)
  `(or (nullp ,p)
       (TER::< (term (first ,p)) (term ,m))))

(defun orderedp (p)
  (declare (xargs :guard (polynomialp p)))
  (and (polynomialp p)
       (or (nullp p)
	   (and (not (MON::nullp (first p)))
		(term-greater-than-leader (first p) (rest p))
		(orderedp (rest p))))))

;;; -----------------------------------
;;; Addition of monomial and polynomial
;;; -----------------------------------

(defun +-monomial (m p)
  (declare (xargs :guard (and (monomialp m) (polynomialp p))))
  (cond ((and (not (monomialp m)) (not (polynomialp p)))
	 *null*)
	((not (monomialp m))
	 p)
	((and (not (polynomialp p)) (MON::nullp m))
	 *null*)
	((not (polynomialp p))
	 (polynomial m *null*))
	((MON::nullp m)
	 p)
	((nullp p)
	 (polynomial m *null*))
	((TER::= (term m) (term (first p)))
	 (let ((c (COMMON-LISP::+ (coefficient m) (coefficient (first p)))))
	   (if (equal c 0)
	       (rest p)
	     (polynomial (monomial c (term m)) (rest p)))))
	((TER::< (term (first p)) (term m))
	 (polynomial m p))
	(t
	 (polynomial (first p) (+-monomial m (rest p))))))

;;; Type rule.

(defthm polynomialp-+-monomial
  (polynomialp (+-monomial m p))
  :rule-classes (:type-prescription :rewrite))

;;; The addition of a monomial to an ordered polynomial preserves the ordering.

(defthm orderedp-+-monomial-polynomial-ordered
  (implies (orderedp p)
	   (orderedp (+-monomial m p)))
  :rule-classes (:type-prescription :rewrite))

;;; Operation order does not alter the addition of monomials to an
;;; ordered polynomial.

(defthm +-monomial-+-monomial
  (implies (orderedp p)
	   (equal (+-monomial m1 (+-monomial m2 p))
		  (+-monomial m2 (+-monomial m1 p)))))

;;; -----------
;;; Normal form
;;; -----------

(defun nf (p)
  (declare (xargs :guard (polynomialp p)))
  (cond ((or (not (polynomialp p)) (nullp p))
	 *null*)
	(t
	 (+-monomial (first p) (nf (rest p))))))

;;; Example:

#|
(equal (POL::nf  '((1 . (2 3)) (2 . (8 9)) (6 . (4 5)) (0 . (4 5)) (-2 . (8 9)) (3 . (2 3))))
                 '((6 . (4 5)) (4 . (2 3))))
|#

;;; Type rule.

(defthm polynomialp-nf
  (polynomialp (nf p))
  :rule-classes (:type-prescription :rewrite))

;;; Normal form polynomial recognizer.

(defmacro nfp (p)
  `(equal (nf ,p) ,p))

;;; Normal form of a polynomial is ordered.

(defthm orderedp-nf
  (orderedp (nf p))
  :rule-classes (:type-prescription :rewrite))

;;; A polynomial is in normal form if, and only if, it is ordered.

(defthm nfp-iff-orderedp
  (iff (nfp p) (orderedp p)))

;;; If a polynomial is complete, so is its normal form.

(encapsulate ()
  (local
    (defthm technical-lemma
      (implies (and (completep p n)
		    (equal (len (term m)) n))
	       (completep (+-monomial m p) n))))

  (defthm completep-nf
    (implies (completep p n)
	     (completep (nf p) n))
    :rule-classes (:type-prescription :rewrite)))

;;; If a polynomial is uniform, so is its normal form.

(defthm uniformp-nf
  (implies (uniformp p)
	   (uniformp (nf p)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal"
	   :in-theory (disable completep-nf)
	   :use ((:instance completep-nf
			    (n (len (term (first p)))))))))

;;; Normal form is recognized as such.

(defthm nfp-nf
  (nfp (nf p)))

;;; --------------------------------
;;; Equality relation on polynomials
;;; --------------------------------

(defun = (p1 p2)
  (declare (xargs :guard (and (polynomialp p1) (polynomialp p2))))
  (equal (nf p1) (nf p2)))

;;; Examples:

#|
(POL::= '((1 . (2 3))  (2 . (8 9)) (6 . (4 5))
	  (0 . (4 5)) (-2 . (8 9)) (3 . (2 3)))
	'((6 . (4 5)) (4 . (2 3))))

(POL::= '( (1 . (7 7))  (1 . (2 3)) (2 . (8 9)) (3 . (2 3)) (6 . (4 5))
	   (0 . (4 5)) (-2 . (8 9)) (3 . (2 3)))
	'((-3 . (8 9))  (0 . (1 1)) (1 . (7 7)) (6 . (4 5))
	   (3 . (8 9))  (7 . (2 3))))
|#

;;; Equality is an equivalence relation.

(defequiv =)
