(in-package "POL")

(include-book "congruences-1")

;;; ----------------------------------
;;; Multiplicative identity polynomial
;;; ----------------------------------

(defconst *one*
  (polynomial MON::*one* *null*))

(defmacro onep (p)
  `(= ,p *one*))

;;; -----------------------------------------
;;; Multiplication of monomial and polynomial
;;; -----------------------------------------

(defun *-monomial (m p)
  (declare (xargs :guard (and (monomialp m) (polynomialp p))))
  (cond ((or (nullp p) (not (monomialp m)) (not (polynomialp p)))
	 *null*)
	(t
	 (polynomial (MON::* m (first p)) (*-monomial m (rest p))))))

;;; Examples:

#|
(POL::= (POL::*-monomial '(3 . (1 2 3)) '((5 . (1 2 3))))
        '((15 . (2 4 6))))

(POL::= (POL::*-monomial '(3 . (1)) '((5 . (1 2 3)) (-4 . (2 2 0))))
        '((15 . (2 2 3)) (-12 . (3 2 0))))
|#

;;; Type rule.

(defthm polynomialp-*-monomial
  (polynomialp (*-monomial m p))
  :rule-classes :type-prescription)

;;; Multiplication of monomial and polynomial has identity element.

(defthm *-monomial-identity
  (implies (and (uniformp p)
		(MON::onep m)
		(MON::compatiblep m (first p)))
	   (= (*-monomial m p) p)))

;;; Multiplication of monomial and polynomial has cancellative element.

(defthm *-monomial-cancellative-equal
  (implies (MON::nullp m)
	   (equal (nf (*-monomial m p)) *null*)))

(defthm *-monomial-cancellative
  (implies (MON::nullp m)
	   (= (*-monomial m p) *null*)))

;;; Multiplication of monomial and polynomial distributes over the
;;; addition of monomial and polynomial.

(encapsulate ()
  (local
    (defthm technical-lemma-1
      (implies (and (termp b) (termp c)
		    (TER::compatiblep b c)
		    (equal (TER::* a b) (TER::* a c)))
	       (equal b c))
      :rule-classes nil))

  (local
    (defthm technical-lemma-2
      (implies (and (equal (TER::* (term m) (term n))
			   (TER::* (term m) (term (first p))))
		    (termp (term n))
		    (termp (term (first p)))
		    (TER::compatiblep (term n) (term (first p))))
	       (equal (term n) (term (first p))))
      :hints (("Goal"
	       :use ((:instance technical-lemma-1
				(b (term n))
				(c (term (first p)))
				(a (term m))))))))

  (local
    (defthm distributivity
      (equal (COMMON-LISP::+ (COMMON-LISP::* r1 r2) (COMMON-LISP::* r1 r3)) (COMMON-LISP::* r1 (COMMON-LISP::+ r2 r3)))))

  (defthm *-monomial-distributes-+-monomial
    (implies (and (monomialp n) (monomialp m)
		  (not (MON::nullp m))
		  (or (nullp p) (MON::compatiblep n (first p)))
		  (MON::compatiblep m n)
		  (uniformp p) (orderedp p))
	     (equal (*-monomial m (+-monomial n p))
		    (+-monomial (MON::* m n) (*-monomial m p))))
    :hints (("Goal"
	     :in-theory (disable ACL2::distributivity)))))

;;; Multiplication of monomial and polynomial distributes over the
;;; addition.

(defthm *-monomial-distributes-+-append
  (implies (and (polynomialp p1) (polynomialp p2))
	   (equal (*-monomial m (append p1 p2))
		  (append (*-monomial m p1) (*-monomial m p2)))))

(defthm *-monomial-distributes-+
  (= (*-monomial m (+ p1 p2))
     (+ (*-monomial m p1) (*-monomial m p2))))

;;; Multiplication of a monomial by the multiplication of a monomial
;;; and a polynomial equals to multiplication of both monomials by the
;;; polynomial.

(defthm *-monomial-*-monomial
  (implies (and (monomialp m1) (monomialp m2))
	   (equal (*-monomial m1 (*-monomial m2 p))
		  (*-monomial (MON::* m1 m2) p)))
  :hints (("Goal"
	   :in-theory (disable ACL2::commutativity-of-*))))

;;; -------------------------
;;; Polynomial multiplication
;;; -------------------------

(defun * (p1 p2)
  (declare (xargs :guard (and (polynomialp p1) (polynomialp p2))))
  (cond ((or (nullp p1) (not (polynomialp p1)))
	 *null*)
	(t
	 (+ (*-monomial (first p1) p2) (* (rest p1) p2)))))

;;; Type rule.

(defthm polynomialp-*
  (polynomialp (* p1 p2))
  :rule-classes :type-prescription)

;;; Multiplication of a monomial by the multiplication of two
;;; polynomials equals to multiplication of the second polynomial by
;;; the result of multiplying the monomial and the first polynomial.

(defthm *-monomial-*
  (implies (monomialp m)
	   (equal (*-monomial m (* p1 p2))
		  (* (*-monomial m p1) p2))))

;;; Polynomial multiplication distributes over polynomial addition.

(defthm *-distributes-+-1
  (= (* p1 (+ p2 p3)) (+ (* p1 p2) (* p1 p3)))
  :hints (("Goal"
	   :in-theory (disable = +))))

(encapsulate ()
  (local
    (defthm technical-lemma
      (equal (* (+ p1 p2) p3) (+ (* p1 p3) (* p2 p3)))))

  (defthm *-distributes-+-2
    (= (* (+ p1 p2) p3) (+ (* p1 p3) (* p2 p3)))
    :hints (("Goal"
	     :in-theory (disable nf + *)))))

;;; Polynomial multiplication has left and right identity element.

(defthm *-identity-1
  (= (* *one* p) p))

(defthm *-identity-2
  (= (* p *one*) p))

;;; Polynomial multiplication has left and right cancellative element.

(defthm *-cancellative-1
  (= (* *null* p) *null*))

(defthm *-cancellative-2
  (= (* p *null*) *null*))

;;; Polynomial multiplication is associative.

(defthm associativity-of-*
  (= (* p1 (* p2 p3)) (* (* p1 p2) p3))
  :hints (("Goal"
	   :in-theory (disable = +))))

;;; Polynomial multiplication is commutative.

(encapsulate ()
  (local
    (defthm technical-lemma
      (implies (and (monomialp m) (polynomialp p) (polynomialp q))
	       (= (+ p (polynomial m q)) (+ q (polynomial m p))))))

  (local
    (defun induction-scheme (p1 p2)
      (declare (xargs :verify-guards nil :measure (COMMON-LISP::+ (len p1) (len p2))))
      (cond ((or (nullp p1) (nullp p2))
	    t)
	    (t
	     (and (induction-scheme (rest p1) (rest p2))
		  (induction-scheme (rest p1) p2)
		  (induction-scheme p1 (rest p2)))))))

  (defthm commutativity-of-*
    (= (* p1 p2) (* p2 p1))
    :hints (("Goal"
	     :induct (induction-scheme p1 p2)
	     :do-not '(eliminate-destructors)
	     :in-theory (disable = + polynomial)))))
