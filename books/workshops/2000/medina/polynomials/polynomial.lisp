(in-package "POL")

(include-book "monomial")

;;; ---------------------
;;; Polynomial recognizer
;;; ---------------------

;;; Similar to «integer-listp» function.

(defun monomial-listp (l)
  (cond ((atom l)
	 (equal l nil))
	(t
	 (and (monomialp (first l))
	      (monomial-listp (rest l))))))

;;; A polynomial is a monomial list.

(defmacro polynomialp (p)
  `(monomial-listp ,p))

;;; ------------------------------
;;; Null polynomial in normal form
;;; ------------------------------

(defconst *null*
  nil)

;;; Note: this will be used in base cases of recursion.

(defmacro nullp (p)
  `(endp ,p))

;;; -----------
;;; Constructor
;;; -----------

(defun polynomial (m p)
  (declare (xargs :guard (and (monomialp m) (polynomialp p))))
  (cond ((and (not (monomialp m)) (not (polynomialp p)))
	 *null*)
	((not (monomialp m))
	 p)
	((not (polynomialp p))
	 (list m))
	(t
	 (cons m p))))

;;; Type rule.

(defthm polynomialp-polynomial
  (polynomialp (polynomial m p))
  :rule-classes :type-prescription)

;;; --------
;;; Accesors
;;; --------

;;; We shall use first and rest as accesors.

;;; Type rule.

(defthm polynomialp-rest
  (implies (polynomialp p)
	   (polynomialp (rest p)))
  :rule-classes :type-prescription)

;;; -------------------------------------
;;; Compatibility relation on polynomials
;;; -------------------------------------

;;; A polynomial is uniform if all of its monomials are compatible each other.

(defun uniformp (p)
  (declare (xargs :guard (polynomialp p)))
  (or (nullp p)
      (nullp (rest p))
      (and (MON::compatiblep (first p) (first (rest p)))
	   (uniformp (rest p)))))

;;; A polynomial is complete with n variables, if all of its monomials
;;; have terms with length n.

(defun completep (p n)
  (declare (xargs :guard (and (polynomialp p) (naturalp n))))
  (or (nullp p)
      (and (equal (len (term (first p))) n)
	   (completep (rest p) n))))

;;; If a polynomial is complete then it is uniform.

(defthm completep-uniformp
  (implies (completep p n)
	   (uniformp p)))

;;; If a polynomial is uniform then it is complete.

(defthm uniformp-completep
  (implies (uniformp p)
	   (completep p (len (term (first p))))))

;;; Therefore, a polynomial is uniform if, and only if, it is
;;; complete.

(defthm uniformp-iff-completep
  (iff (uniformp p) (completep p (len (term (first p)))))
  :rule-classes nil)

;;; Two polynomials are compatible if they both are uniform and their
;;; two first terms are compatible.

(defmacro compatiblep (p1 p2)
  `(and (uniformp ,p1) (uniformp ,p2)
	(MON::compatiblep (first ,p1) (first ,p2))))
