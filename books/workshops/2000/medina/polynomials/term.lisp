(in-package "TER")

;;; ------------------
;;; Natural recognizer
;;; ------------------

;;; Similar to «integerp» macro.

(defmacro naturalp (x)
  `(and (integerp ,x) (COMMON-LISP::<= 0 ,x)))

;;; --------------------------------
;;; True list of naturals recognizer
;;; --------------------------------

;;; Similar to «integer-listp» function.

(defun natural-listp (l)
  (cond ((atom l)
	 (equal l nil))
	(t
	 (and (naturalp (first l))
	      (natural-listp (rest l))))))

;;; ---------------
;;; Term recognizer
;;; ---------------

;;; A term is a list of naturals.

(defmacro termp (a)
  `(natural-listp ,a))

;;; ---------
;;; Null term
;;; ---------

(defconst *null*
  nil)

;;; A term is null if it only contains zeros.

(defun nullp (a)
  (cond ((atom a)
	 (equal a *null*))
	(t
	 (and (equal (first a) 0) (nullp (rest a))))))

;;; Type rule.

(defthm termp-nullp
  (implies (nullp a)
	   (termp a))
  :rule-classes :type-prescription)

(encapsulate ()

  ;;; Null term with arbitrary length.

  (local (defun null (n)
	   (declare (xargs :guard (naturalp n)))
	   (cond ((zp n)
		  *null*)
		 (t
		  (cons 0 (null (COMMON-LISP::- n 1)))))))

  ;;; Null terms are recognized.

  (local (defthm nullp-null
	   (nullp (null n)))))

;;; -------------------------------
;;; Compatibility relation on terms
;;; -------------------------------

;;; Two terms are compatible if they are the same length.

(defmacro compatiblep (a b)
  `(equal (len ,a) (len ,b)))

;;; --------------------------
;;; Equality relation on terms
;;; --------------------------

;;; Two terms are equal if they are syntactically equal.

(defmacro = (a b)
  `(equal ,a ,b))

;;; -------------------
;;; Term multiplication
;;; -------------------

(defun * (a b)
  (declare (xargs :guard (and (termp a) (termp b))))
  (cond ((and (not (termp a)) (not (termp b)))
	 *null*)
	((not (termp a))
	 b)
	((not (termp b))
	 a)
	((endp a)
	 b)
	((endp b)
	 a)
	(t
	 (cons (COMMON-LISP::+ (first a) (first b)) (* (rest a) (rest b))))))

;;; Examples:

#|
(equal (* '(1 2 3) '(1 2 3)) '(2 4 6))
(equal (* '(1)     '(1 2 3)) '(2 2 3))
|#

;;; Multiplication of terms is a term.

(defthm termp-*
  (termp (* a b))
  :rule-classes :type-prescription)

;;; Multiplication of compatible terms is compatible with its arguments.

(defthm compatiblep-*
  (implies (and (termp a) (termp b) (compatiblep a b))
	   (and (compatiblep (* a b) a)
		(compatiblep (* a b) b))))

;;; Term multiplication has left and right identity element.

(defthm *-identity-1
  (implies (and (nullp a) (termp b) (compatiblep a b))
	   (= (* a b) b)))

(defthm *-identity-2
  (implies (and (termp a) (nullp b) (compatiblep a b))
	   (= (* a b) a)))

;;; Term multiplication is commutative.

(defthm commutativity-of-*
  (= (* a b) (* b a)))

;;; Term multiplication is associative.

(defthm associativity-of-*
  (= (* (* a b) c) (* a (* b c))))
