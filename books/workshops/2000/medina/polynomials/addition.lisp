(in-package "POL")

(include-book "normal-form")

;;; -------------------
;;; Polynomial addition
;;; -------------------

(defun + (p1 p2)
  (declare (xargs :guard (and (polynomialp p1) (polynomialp p2))))
  (cond ((and (not (polynomialp p1)) (not (polynomialp p2)))
	 *null*)
	((not (polynomialp p1))
	 p2)
	((not (polynomialp p2))
	 p1)
	(t
	 (append p1 p2))))

;;; Type rules.

(defthm polynomialp-append
  (implies (and (polynomialp p1) (polynomialp p2))
	   (polynomialp (append p1 p2)))
  :rule-classes (:type-prescription :rewrite))

(defthm polynomialp-+
  (polynomialp (+ p1 p2))
  :rule-classes (:type-prescription :rewrite))

;;; -------------------
;;; Addition properties
;;; -------------------

;;; Polynomial addition has left and right identity element.

(defthm append-identity-1
  (implies (polynomialp p)
	   (equal (append p *null*) p)))

(defthm +-identity-1
  (= (+ p *null*) p))

(defthm append-identity-2
  (equal (append *null* p) p))

(defthm +-identity-2
  (= (+ *null* p) p))

;;; Polynomial addition is associative.

(defthm associativity-of-append
  (equal (append (append p1 p2) p3)
	 (append p1 (append p2 p3))))

(defthm associativity-of-+
  (= (+ (+ p1 p2) p3) (+ p1 (+ p2 p3))))

;;; Polynomial addition is commutative.

(encapsulate ()
  (local
    (defthm technical-lemma
      (equal (+-monomial m1 (+-monomial m2 (nf p)))
	     (+-monomial m2 (+-monomial m1 (nf p))))))

  (defthm commutativity-of-append-technical-lemma
    (implies (and (polynomialp p1)
		  (polynomialp p2)
		  (not (nullp p2)))
	     (equal (nf (append p1 p2))
		    (+-monomial (first p2)
			       (nf (append p1 (rest p2))))))))

(defthm commutativity-of-append
  (implies (and (polynomialp p1) (polynomialp p2))
	   (= (append p1 p2) (append p2 p1))))

(defthm commutativity-of-+
  (= (+ p1 p2) (+ p2 p1))
  :hints (("Goal"
	   :in-theory (disable =))))

;;; Polynomial addition is associative-commutative.

(defthm associativity-commutativity-of-append
  (implies (and (polynomialp p1) (polynomialp p2) (polynomialp p3))
	   (= (append p3 (append p2 p1))
	      (append p2 (append p3 p1)))))

(defthm associativity-commutativity-of-+
  (= (+ p3 (+ p2 p1)) (+ p2 (+ p3 p1)))
  :hints (("Goal" :in-theory (disable =))
	  ("Subgoal 1" :in-theory (enable =))))
