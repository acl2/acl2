(in-package "POL")

(include-book "multiplication")

;;; ---------------------------------------------------------------------
;;; Congruence of equality with multiplication of monomial and polynomial
;;; ---------------------------------------------------------------------

;;; First argument.

(defcong MON::= = (*-monomial m p) 1)

;;; Normal form of multiplication of a monomial and a polynomial equals
;;; to multiplication of the monomial and the polynomial normal form.

(encapsulate ()
  (local
    (defthm technical-lemma-1
      (implies (and (completep (nf p) (len (term (first p))))
		    (not (nullp (nf p))))
	       (TER::compatiblep (term (first (nf p))) (term (first p))))))

  (local
    (defthm technical-lemma-2
      (implies (and (polynomialp p)
		    (uniformp p)
		    (not (nullp (nf p))))
	       (TER::compatiblep (term (first (nf p))) (term (first p))))))

  (local
   (defun induction-scheme (m p)
     (declare (xargs :verify-guards nil))
     (if (and (not (MON::nullp m)) (not (nullp p)))
	 (induction-scheme m (rest p))
       t)))

  (defthm nf-*-monomial
    (implies (and (monomialp m) (polynomialp p)
		  (not (MON::nullp m))
		  (MON::compatiblep m (first p))
		  (uniformp p))
	     (equal (nf (*-monomial m p)) (*-monomial m (nf p))))
    :hints (("Goal"
	     :induct (induction-scheme m p)))))

;;; Second argument, congruence cannot be stated due to the hypothesis.

(defthm =-implies-=-*-monomial-2
  (implies (and (monomialp m) (polynomialp p1) (polynomialp p1-equiv)
		(MON::compatiblep m (first p1)) (compatiblep p1 p1-equiv)
		(= p1 p1-equiv))
	   (= (*-monomial m p1) (*-monomial m p1-equiv)))
  :hints (("Goal"
	   :cases ((MON::nullp m) (not (MON::nullp m))))
	  ("Subgoal 2"
	   :in-theory (disable =))))

;;; --------------------------------------------------------------------
;;; Congruence of equality with multiplication of compatible polynomials
;;; --------------------------------------------------------------------

;;; Multiplication of a monomial and an ordered and uniform polynomial
;;; is an ordered polynomial.

(defthm orderedp-*-monomial-orderedp
  (implies (and (uniformp p)
		(orderedp p)
		(monomialp m)
		(MON::compatiblep m (first p))
		(not (MON::nullp m)))
	   (orderedp (*-monomial m p))))

;;; Multiplication of a monomial and an ordered and uniform polynomial
;;; equals to its normal form.

(defthm nf-*-monomial-orderedp
  (implies (and (uniformp p)
		(orderedp p)
		(monomialp m)
		(not (MON::nullp m))
		(MON::compatiblep m (first p)))
	   (equal (nf (*-monomial m p))
		  (*-monomial m p))))

;;; Equality is preserved when replacing a polynomial with its normal
;;; form in the multiplication of a polynomial and a monomial.

(local
  (encapsulate ()
    (local
     (defthm technical-lemma-1
       (implies (and (completep (nf p) (len (term (first p))))
		     (not (nullp (nf p))))
		(TER::compatiblep (term (first (nf p)))
				  (term (first p))))))

    (local
     (defthm technical-lemma-2
       (implies (and (polynomialp p)
		     (uniformp p)
		     (not (nullp (nf p))))
		(TER::compatiblep (term (first (nf p)))
				  (term (first p))))))

    (local
       (defthm technical-lemma-3
	 (implies  (and (monomialp m)
			(not (MON::nullp m))
			(MON::compatiblep m (first p))
			(uniformp p)
			(polynomialp p))
		   (equal (nf (*-monomial m p))
			  (nf (*-monomial m (nf p)))))))

    (defthm nf-*-monomial-nf
      (implies  (and (monomialp m)
		     (MON::compatiblep m (first p))
		     (uniformp p)
		     (polynomialp p))
		(equal (nf (*-monomial m (nf p))) (nf (*-monomial m p))))
      :hints (("Goal"
	       :cases ((MON::nullp m) (not (MON::nullp m))))))))

;;; Equality is preserved when replacing a polynomial with its normal
;;; form in polynomial multiplication.


(local
  (encapsulate ()
    (local
     (defun induction-scheme (p1 p2)
       (declare (xargs :guard (and (polynomialp p1) (polynomialp p2))))
       (if (not (nullp p1))
	   (induction-scheme (rest p1) p2)
	 t)))

    (defthm nf-*-1
      (implies (and (polynomialp p1) (polynomialp p2)
		    (not (nullp p1)) (not (nullp p2))
		    (compatiblep p1 p2))
	       (= (* p1 (nf p2)) (* p1 p2)))
      :hints (("Goal"
	       :in-theory (disable nf-+)
	       :induct (induction-scheme p1 p2))
	      ("Subgoal *1/"
	       :use ((:instance nf-+ (p1 (*-monomial (first p1) (nf p2)))
				     (p2 (* (rest p1) (nf p2))))
		     (:instance nf-+ (p1 (*-monomial (first p1) p2))
				     (p2 (* (rest p1) p2)))))))))

(defthm =-implies-=-*-2
  (implies (and	(polynomialp p1) (polynomialp p2) (polynomialp p2-equiv)
		(compatiblep p1 p2) (compatiblep p1 p2-equiv)
		(= p2 p2-equiv))
	   (= (* p1 p2) (* p1 p2-equiv)))
  :hints (("Goal"
	   :in-theory (disable nf-*-1)
	   :use (nf-*-1
		 (:instance nf-*-1 (p2 p2-equiv))))))

(defthm =-implies-=-*-1
  (implies (and	(polynomialp p1) (polynomialp p1-equiv) (polynomialp p2)
		(compatiblep p1 p2) (compatiblep p1-equiv p2)
		(= p1 p1-equiv))
	   (= (* p1 p2) (* p1-equiv p2)))
  :hints (("Goal"
	   :in-theory (disable commutativity-of-*)
	   :use (commutativity-of-*
		 (:instance commutativity-of-* (p1 p1-equiv))
		 (:instance =-implies-=-*-2 (p1 p2) (p2 p1) (p2-equiv p1-equiv))))))
