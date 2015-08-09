(in-package "MON")

(include-book "term")

;;; -----------
;;; Constructor
;;; -----------

(defmacro monomial (c e)
  `(cons ,c ,e))

;;; --------
;;; Accesors
;;; --------

(defmacro coefficient (a)
  `(first ,a))

(defmacro term (a)
  `(rest ,a))

;;; -------------------
;;; Monomial recognizer
;;; -------------------

;;; A monomial is a list whose first element is a rational and its
;;; rest, a term.

(defmacro monomialp (a)
  `(and (consp ,a)
	(rationalp (first ,a))
	(termp (rest ,a))))

;;; -------------
;;; Null monomial
;;; -------------

(defconst *null*
  (monomial 0 TER::*null*))

;;; A monomial is null if its coefficient is 0.

(defmacro nullp (a)
  `(equal (coefficient ,a) 0))

;;; -------------------------------------------
;;; Multiplicative identity monomial recognizer
;;; -------------------------------------------

(defconst *one*
  (monomial 1 TER::*null*))

;;; A monomial is a multiplicative identity if its coefficient is 1
;;; and its term is null.

(defmacro onep (a)
  `(and (equal (coefficient ,a) 1)
	(TER::nullp (term ,a))))

;;; -----------------------------------
;;; Compatibility relation on monomials
;;; -----------------------------------

;;; Two monomials are equivalent if their terms are compatible.

(defun compatiblep (a b)
  (declare (xargs :guard (and (monomialp a) (monomialp b))))
  (TER::compatiblep (term a) (term b)))

;;; Compatibility is an equivalence relation.

(defequiv compatiblep)

;;; ------------------------------
;;; Equality relation on monomials
;;; ------------------------------

;;; Two monomials are equal if they both are null or their
;;; coefficients and terms are respectively equal.

(defun = (a b)
  (declare (xargs :guard (and (monomialp a) (monomialp b))))
  (or (and (nullp a) (nullp b))
      (and (COMMON-LISP::= (coefficient a) (coefficient b))
	   (TER::= (term a) (term b)))))

;;; Equality is an equivalence relation.

(defequiv =)

;;; -----------------------
;;; Monomial multiplication
;;; -----------------------

(defun * (a b)
  (declare (xargs :guard (and (monomialp a) (monomialp b))))
  (monomial (COMMON-LISP::* (coefficient a) (coefficient b))
	    (TER::* (term a) (term b))))

;;; Multiplication of monomials is a monomial.

(defthm monomialp-*
  (implies (and (monomialp a) (monomialp b))
	   (monomialp (* a b)))
  :rule-classes :type-prescription)

;;; Equality is congruent with multiplication.

(defcong = = (* a b) 1)
(defcong = = (* a b) 2)

;;; Multiplication of compatible monomials is compatible with its arguments.

(defthm compatiblep-*
  (implies (and (monomialp a) (monomialp b) (compatiblep a b))
	   (and (compatiblep (* a b) a)
		(compatiblep (* a b) b))))

;;; Compatible monomial multiplication has left and right identity
;;; element.

(defthm *-identity-1
  (implies (and (onep a) (monomialp b) (compatiblep a b))
	   (= (* a b) b)))

(defthm *-identity-2
  (implies (and (monomialp a) (onep b) (compatiblep a b))
	   (= (* a b) a)))

;;; Compatible monomial multiplication has left and right cancellative
;;; element.

(defthm *-cancellative-1
  (implies (and (nullp a) (compatiblep a b))
	   (nullp (* a b))))

(defthm *-cancellative-2
  (implies (and (nullp b) (compatiblep a b))
	   (nullp (* a b))))

;;; Monomial multiplication is associative.

(defthm associativity-of-*
  (= (* (* a b) c) (* a (* b c)))
  :hints (("Goal"
	   :in-theory (disable ACL2::commutativity-of-*))))

;;; Monomial multiplication is commutative.

(defthm commutativity-of-*
  (= (* a b) (* b a)))
