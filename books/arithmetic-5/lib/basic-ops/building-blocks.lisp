; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; building-blocks.lisp
;;;
;;; This book contains functions we have found helpful when defining
;;; bind-free rules.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "building-blocks-helper"))

(table acl2-defaults-table :state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Since we mostly deal with binary operations in our bind-freee
;;; rules, we define a couple of functions for accessing the first and
;;; second args.

(defun arg1 (x)
  (declare (xargs :guard t))
  (if (and (consp x)
	   (consp (cdr x)))
      (cadr x)
    nil))

(defun arg2 (x)
  (declare (xargs :guard t))
  (if (and (consp x)
	   (consp (cdr x))
	   (consp (cddr x)))
      (caddr x)
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A couple of simple recognizers for constants.

(defun constant-p (x)
  (declare (xargs :guard t))
  (and (quotep x)
       (consp (cdr x))))

(defun numeric-constant-p (x)
  (declare (xargs :guard t))
  (and (quotep x)
       (consp (cdr x))
       (acl2-numberp (unquote x))))

(defun integer-constant-p (x)
  (declare (xargs :guard t))
  (and (quotep x)
       (consp (cdr x))
       (integerp (unquote x))))

(defun rational-constant-p (x)
  (declare (xargs :guard t))
  (and (quotep x)
       (consp (cdr x))
       (rationalp (unquote x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Two is an important number.

;;; 2 is an important number in hardware and software proofs and
;;; we treat it specially here.  The basic idea is to recognize
;;; powers of 2 inside an expt, and to rewrite appropriately.
;;; See common.lisp and collect.lisp.

;;; This was taken from somewhere in the rtl books and modified.

(defun power-of-2-measure (x)
  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((or (not (real/rationalp x))
             (<= x 0)) 0)
	((< x 1) (cons (cons 1 1) (floor (/ x) 1)))
	(t (floor x 1))))

(defun power-of-2-helper (x)
  (declare (xargs :guard t
                  :measure (power-of-2-measure x)))
  (cond ((or (not (real/rationalp x))
             (<= x 0))
         0)
        ((< x 1) (+ -1 (power-of-2-helper (* 2 x))))
        ((<= 2 x) (+ 1 (power-of-2-helper (* 1/2 x))))
        ((equal x 1) 0)
        (t 0)))

(defun power-of-2-generalized (x)
  (declare (xargs :guard t))
  ;; Examples:
  ;; 4 --> 2
  ;; 1/8 --> -3
  ;; 3 --> nil
  ;; 0 --> nil
  (cond ((not (rational-constant-p x))
	 nil)
	((< 0 (unquote x))
	 (let ((c (power-of-2-helper (unquote x))))
	   (if (equal (expt 2 c) (unquote x))
	       c
	     nil)))
	((< (unquote x) 0)
	 (let ((c (power-of-2-helper (- (unquote x)))))
	   (if (equal (expt 2 c) (- (unquote x)))
	       c
	     nil)))
	(t
	 nil)))

(defun power-of-2 (x)
  (declare (xargs :guard t))
  (cond ((not (integer-constant-p x))
	 nil)
	((< 1 (unquote x))
	 (let ((c (power-of-2-helper (unquote x))))
	   (if (equal (expt 2 c) (unquote x))
	       c
	     nil)))
	((< (unquote x) -1)
	 (let ((c (power-of-2-helper (- (unquote x)))))
	   (if (equal (expt 2 c) (- (unquote x)))
	       c
	     nil)))
	(t
	 nil)))

(defun power-of-2-minus-1 (x)
  (declare (xargs :guard t))
  (cond ((not (integer-constant-p x))
	 nil)
	((< 0 (unquote x))
	 (let ((c (power-of-2-helper (+ 1 (unquote x)))))
	   (if (equal (expt 2 c) (+ 1 (unquote x)))
	       c
	     nil)))
	(t
	 nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Are we rewriting a top-level goal literal, rather than rewriting
;;; a hypothesis from a rewrite (or other) rule?  (Ancestors is a
;;; list of the negations of backchaining hypotheses being pursued.
;;; Hence we are rewriting a goal literal iff it is NIL.)

;;; Note that we are not testing whether the term being rewritten
;;; is itself a goal literal.  Only whether what we are rewriting
;;; is either
;;; 1. (possibly part of) a goal literal, or
;;; 2. derived from (possibly part of) one.

(defun rewriting-goal-literal (x mfc state)
  (declare (xargs :guard t))
  (declare (ignore x state))
  (null (mfc-ancestors mfc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We will be asking whether certain terms appear in the goal,
;;; or ancestors.  There is a wrinkle we handle here.  If the
;;; term under consideration is an equality, we have to check
;;; both orders of its args.

(defun term-equal (term1 term2)
  (declare (xargs :guard t))
  (if (equal (fn-symb term1) 'EQUAL)
      (and (equal (fn-symb term2) 'EQUAL)
	   (or (and (equal (arg1 term1) (arg1 term2))
		    (equal (arg2 term1) (arg2 term2)))
	       (and (equal (arg1 term1) (arg2 term2))
		    (equal (arg2 term1) (arg1 term2)))))
    (equal term1 term2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Is the term we are rewriting the hypothesis of a rewrite
;;; (or other) rule?

;;; Ancestors is a list of the negations of backchaining hypotheses
;;; being pursued.  Hence if it is non-empty, its car is the
;;; hypothesis currently being rewritten.

;;; Why do we not just use (not (rewriting-goal-literal ...))?
;;; Because that does not avoid application when rewriting
;;; subterms or function expansion.

(defun rewriting-hypothesis-1 (term ancestors)
  (declare (xargs :guard t))
  (if (and (consp ancestors)
	   (consp (car ancestors)))
      (let ((hyp (caar ancestors)))
	(cond ((term-equal term hyp)
	       'positive)
	      ((and (eq (fn-symb hyp) 'NOT)
		    (term-equal term (arg1 hyp)))
	       'negative)
	      (t
	       nil)))
    nil))

(defun rewriting-hypothesis (term mfc state)
  (declare (ignore state))
  (rewriting-hypothesis-1 term (mfc-ancestors mfc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Present-in-hyps is 'positive if term appears as a literal
;;; of goal, and 'negative if term appears negated.  It is NIL
;;; otherwise.  Note that due to ACL2's internal representation
;;; of a goal in disjunctive normal form, the hypotheses of a
;;; goal appear internally in the opposite form that the user
;;; sees.  Thus, a hypothesis such as (<= x y) will appear
;;; as (< y x) in the clause, while (< x y) will appear as
;;; (not (< x y)).

;;; Note that linear arithmetic will see things in the opposite
;;; sense as returned by this function.  I find all of this
;;; confusing.

;;; We do not check the conclusion (the final literal) of the
;;; goal, only the hypotheses.

;;; Note that, as distinguished from rewriting-goal-literal, we
;;; ask if term is itself in the goal (possibly negated).

;;; We assume term is, itself, not negated.

(defun present-in-hyps (term goal)
  (declare (xargs :guard t))
  (cond ((atom goal)  ; for the guard.
	 nil)
	((atom (cdr goal))
	 ;; We only check the hypotheses of a goal, not the
	 ;; conclusion.  Presumably, if a weak inequality
	 ;; appeared in the conclusion, the goal would already
	 ;; have been proven via linear arithmetic.
         nil)
        ((term-equal term (car goal))
         'positive)
        ((and (eq (fn-symb (car goal)) 'NOT)
              (term-equal term (arg1 (car goal))))
         'negative)
        (t
         (present-in-hyps term (cdr goal)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Analogous to present-in-hyps, but checks the entire goal.

(defun present-in-goal-1 (term goal)
  (declare (xargs :guard t))
  (cond ((atom goal)
	 nil)
        ((term-equal term (car goal))
         'positive)
        ((and (eq (fn-symb (car goal)) 'NOT)
              (term-equal term (arg1 (car goal))))
         'negative)
        (t
         (present-in-goal-1 term (cdr goal)))))

(defun present-in-goal (term mfc state)
  (declare (ignore state))
  (present-in-goal-1 term (mfc-clause mfc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun negate-match (match)

  ;; Match is presumably an arithmetic expression.  We return
  ;; the equivalent of `(unary-- ,match), simplifying the
  ;; expression in some cases.

  (declare (xargs :guard t))
  (cond ((variablep match)
	 `(UNARY-- ,match))
	((numeric-constant-p match)
	 (kwote (- (unquote match))))
	((eq (ffn-symb match) 'UNARY--)
	 (arg1 match))
	((and (eq (ffn-symb match) 'BINARY-*)
	      (numeric-constant-p (arg1 match)))
	 `(BINARY-* ,(kwote (- (unquote (arg1 match))))
		    ,(arg2 match)))
	;; Needed for call in invert-match
	((eq (ffn-symb match) 'BINARY-+)
	 `(BINARY-+ ,(negate-match (arg1 match))
		    ,(negate-match (arg2 match))))
	(t
	 `(UNARY-- ,match))))

;;; from when (/ (expt x n)) was the preferred form:
;;; (but was I really handling products correctly?
#|
(defun invert-match (match)
  (declare (xargs :guard t))
  (cond ((variablep match)
	 `(UNARY-/ ,match))
	((numeric-constant-p match)
	 (if (eql (unquote match) 0)
	     (kwote 0)
	   (kwote (/ (unquote match)))))
	((eq (ffn-symb match) 'UNARY-/)
	 (arg1 match))
	((eq (ffn-symb match) 'UNARY--)
	 `(UNARY-- (UNARY-/ ,match)))
	(t
	 `(UNARY-/ ,match))))
|#

(defun invert-match (match)
  (declare (xargs :guard t))
  (cond ((variablep match)
	 `(UNARY-/ ,match))
	((numeric-constant-p match)
	 (if (eql (unquote match) 0)
	     (kwote 0)
	   (kwote (/ (unquote match)))))
	((eq (ffn-symb match) 'UNARY-/)
	 (arg1 match))
	((eq (ffn-symb match) 'UNARY--)
	 `(UNARY-- ,(invert-match (arg1 match))))
	((eq (ffn-symb match) 'BINARY-*)
	 `(BINARY-* ,(invert-match (arg1 match))
		    ,(invert-match (arg2 match))))
	((eq (ffn-symb match) 'EXPT)
	 `(EXPT ,(arg1 match) ,(negate-match (arg2 match))))

	(t
	 `(UNARY-/ ,match))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Wrappers for mfc-rw.

;;; We often want to answer the question, ``` Does ACL2 know
;;; that this term is an xxx?''' where xxx is one of
;;; a. integer, b. rational, c. non-zero number, or d. non-zero
;;; rational

(defun proveably-integer (x alist mfc state)
  (declare (xargs :guard t))

  ;; Can rewriting determine that x is an integer?

  (equal (mfc-rw+ `(INTEGERP ,x)
			    alist
			    t t mfc state)
	 *t*))

(defun proveably-rational (x alist mfc state)
  (declare (xargs :guard t))

  ;; Can rewriting determine that x is rational?

  (equal (mfc-rw+ `(RATIONALP ,x)
		 alist
		 t t mfc state)
	 *t*))

(defun proveably-real/rational (x alist mfc state)
  (declare (xargs :guard t))

  ;; Can rewriting determine that x is rational?

  (equal (mfc-rw+ #-non-standard-analysis `(RATIONALP ,x)
		  #+non-standard-analysis `(REALP ,x)
		 alist
		 t t mfc state)
	 *t*))

(defun proveably-acl2-numberp (x alist mfc state)
  (declare (xargs :guard t))

  ;; Can rewriting determine that x is a number?

  (equal (mfc-rw+ `(ACL2-NUMBERP ,x)
		 alist
		 t t mfc state)
	 *t*))

(defun proveably-non-zero1 (x alist mfc state)
  (declare (xargs :guard t))
  (equal (mfc-rw+ `(NOT (EQUAL (FIX ,x) '0))
		 alist
		 t t mfc state)
	 *t*))

(defun proveably-non-zero (x alist mfc state)
  (declare (xargs :guard t))

  ;; If x is not an IF expression, can rewriting determine that it
  ;; is numeric and not equal to zero?

  (cond ((variablep x)
         (proveably-non-zero1 x alist mfc state))
        ((fquotep x)
         (and (numeric-constant-p x)
              (not (equal x ''0))))
        ((eq (ffn-symb x) 'IF)
         nil)
        (t
         (proveably-non-zero1 x alist mfc state))))

(defun proveably-non-zero-rational1 (x alist mfc state)
  (declare (xargs :guard t))
  (equal (mfc-rw+ `(NOT (EQUAL (RFIX ,x) '0))
		 alist
		 t t mfc state)
	 *t*))

(defun proveably-non-zero-rational (x alist mfc state)
  (declare (xargs :guard t))

  ;; If x is not an IF expression, can rewriting determine that it
  ;; is rational and not equal to zero?

  (cond ((variablep x)
         (proveably-non-zero-rational1 x alist mfc state))
        ((fquotep x)
         (and (rational-constant-p x)
              (not (equal x ''0))))
        ((eq (ffn-symb x) 'IF)
         nil)
        (t
         (proveably-non-zero-rational1 x alist mfc state))))

(defun proveably-non-zero-real/rational1 (x alist mfc state)
  (declare (xargs :guard t))
  (equal (mfc-rw+ #-non-standard-analysis `(NOT (EQUAL (RFIX ,x) '0))
		  #+non-standard-analysis `(NOT (EQUAL (REALFIX ,x) '0))
		  alist
		  t t mfc state)
	 *t*))

(defun proveably-non-zero-real/rational (x alist mfc state)
  (declare (xargs :guard t))

  ;; If x is not an IF expression, can rewriting determine that it
  ;; is rational and not equal to zero?

  (cond ((variablep x)
         (proveably-non-zero-real/rational1 x alist mfc state))
        ((fquotep x)
         (and (rational-constant-p x)
              (not (equal x ''0))))
        ((eq (ffn-symb x) 'IF)
         nil)
        (t
         (proveably-non-zero-real/rational1 x alist mfc state))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Before I moved the distributivity rules to distributivity.lisp, I
;;; used the following:
#|
(defun stable-under-rewriting (x bin-op mfc state)
  (declare (xargs :guard (symbolp bin-op)))
  (let* ((secret-constant ''1234789/9876321)
	 (rewritten-term (mfc-rw+ `(,bin-op ,secret-constant x)
				  `((x . ,x))
				  '? nil mfc state)))
    (and (consp rewritten-term)
	 (eq (car rewritten-term) bin-op)
	 (consp (cdr rewritten-term))
	 (consp (cddr rewritten-term))
	 (if (equal (cadr rewritten-term) secret-constant)
	     (equal (caddr rewritten-term) x)
	   (equal (cadr rewritten-term) x)))))
|#
;;; But I now believe the following is sufficient.

(defun stable-under-rewriting (x bin-op mfc state)
  (declare (xargs :guard (symbolp bin-op))
	   (ignore bin-op))
  (let ((rewritten-term (mfc-rw+ `(fix x)
				  `((x . ,x))
				  '? nil mfc state)))
    (equal rewritten-term x)))

(defun stable-under-rewriting-sums (x mfc state)
  (declare (xargs :guard t))

  ;; If x is not an IF expression, does it rewrite to itself when
  ;; inside a sum?

  ;; This function is designed to test whether it is safe to add x to
  ;; a sum in order to cancel out a matching addend.  (X is presumably
  ;; the negation of this matching addend.)  This function tests
  ;; whether it is safe to do so.  It is not safe if x would be
  ;; rewritten to something else before it got a chance to be canceled
  ;; against its match.  There are two common situations where this
  ;; can occur (and doubtless others).  First, when setting up the
  ;; initial simplify-clause-pot-lst for Goal, it is possible that the
  ;; larger expression containing (the match for) x has not been
  ;; rewritten, and so x is in some unstable form.  Second, since x
  ;; has been negated, it is possible that rewrite-solidify will
  ;; replace x with some other term.  This can cause loops since the
  ;; term x is supposed to cancel with will remain to be canceled
  ;; again.

  (cond ((variablep x)
         (stable-under-rewriting x 'BINARY-+ mfc state))
        ((fquotep x)
         t)
        ((member-eq (ffn-symb x) '(IF BINARY-+))
         nil)
        (t
         (stable-under-rewriting x 'BINARY-+ mfc state))))

(defun stable-under-rewriting-products (x mfc state)
  (declare (xargs :guard t))

  ;; If x is not an IF expression, does it rewrite to itself when
  ;; inside a product?

  (cond ((variablep x)
         (stable-under-rewriting x 'BINARY-* mfc state))
        ((fquotep x)
         t)
        ((member-eq (ffn-symb x) '(IF BINARY-*))
         nil)
        (t
         (stable-under-rewriting x 'BINARY-* mfc state))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Another source of loops is, for instance, sums in which the
;;; item we are cancelling is too far down the sum to see:
;;; (* x (* (foo x) (expt 2 x) (/ x)))

(defun in-term-order-+ (x mfc state)
  (declare (xargs :mode :program))
  (declare (ignorable mfc))
  (if (equal (fn-symb x) 'BINARY-+)
      (if (equal (fn-symb (arg2 x)) 'BINARY-+)
	  (and (term-order+ (arg1 x) (arg1 (arg2 x))
			    (invisible-fns '(BINARY-+)
					   (invisible-fns-table (w state))
					   t))
	       (in-term-order-+ (arg2 x) mfc state))
	(term-order+ (arg1 x) (arg2 x)
		     (invisible-fns '(BINARY-+)
				    (invisible-fns-table (w state))
				    t)))
    t))

(defun in-term-order-* (x mfc state)
  (declare (xargs :mode :program))
  (declare (ignorable mfc))
  (if (equal (fn-symb x) 'BINARY-*)
      (if (equal (fn-symb (arg2 x)) 'BINARY-*)
	  (and (term-order+ (arg1 x) (arg1 (arg2 x))
			    (invisible-fns '(BINARY-*)
					   (invisible-fns-table (w state))
					   t))
	       (in-term-order-* (arg2 x) mfc state))
	(term-order+ (arg1 x) (arg2 x)
		     (invisible-fns '(BINARY-*)
				    (invisible-fns-table (w state))
				    t)))
    t))

(defun in-term-order (x mfc state)
  (declare (xargs :mode :program))
  (cond ((equal (fn-symb x) 'BINARY-+)
	 (in-term-order-+ x mfc state))
	((equal (fn-symb x) 'BINARY-*)
	 (in-term-order-* x mfc state))
	(t
	 t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We next define several functions for recognizing terms of
;;; particular syntactic forms.

(defun negative-addends-p-1 (x mfc state)
  (declare (xargs :guard t))
  (cond ((variablep x)
         nil)
        ((fquotep x)
         (and (rational-constant-p x)
              (< (unquote x) 0)))
        ((eq (ffn-symb x) 'UNARY--)
	 (and (not (eq (fn-symb (arg1 x)) 'UNARY--))
	      (proveably-acl2-numberp 'x `((x . ,(arg1 x)))
				      mfc state)))
        ((eq (ffn-symb x) 'BINARY-*)
         (and (rational-constant-p (arg1 x))
              (< (unquote (arg1 x)) 0)))
        ((eq (ffn-symb x) 'BINARY-+)
	 (and (negative-addends-p-1 (arg1 x) mfc state)
              (negative-addends-p-1 (arg2 x) mfc state)))
        (t
         nil)))

(defun negative-addends-p (x mfc state)
  (declare (xargs :guard t))

  ;; X is an ACL2 term.  We return t if x is a negative addend, or a
  ;; sum of negative addends.  Here, an addend is considered to be
  ;; negative if it is a negative rational constant, or prints as
  ;; (- ...) or (* c ...) where c is a negative rational.  We also
  ;; require that x is not merely a negative constant.

  (if (quotep x)
      nil
    (negative-addends-p-1 x mfc state)))

(defun negative-addends-balance (x mfc state)
  (declare (xargs :guard t))
  (cond ((variablep x)
	 -1)
	((fquotep x)
         (if (and (rational-constant-p x)
		  (< (unquote x) 0))
	     1
	   -1))
        ((eq (ffn-symb x) 'UNARY--)
	 (if (and (not (eq (fn-symb (arg1 x)) 'UNARY--))
		  (proveably-acl2-numberp 'x `((x . ,(arg1 x)))
					  mfc state))
	     1
	   -1))
        ((eq (ffn-symb x) 'BINARY-*)
         (if (and (rational-constant-p (arg1 x))
		  (< (unquote (arg1 x)) 0))
	     1
	   -1))
        ((eq (ffn-symb x) 'BINARY-+)
	 (+ (negative-addends-balance (arg1 x) mfc state)
	    (negative-addends-balance (arg2 x) mfc state)))
        (t
         -1)))

(defun mostly-negative-addends-p (x mfc state)

  ;; Are more than half the addends negative?

  (declare (xargs :guard t))
  (if (quotep x)
      nil
    (< 0 (negative-addends-balance x mfc state))))

(defun weak-negative-addends-p-1 (x mfc state)
  (declare (xargs :guard t))
  (cond ((variablep x)
         nil)
        ((fquotep x)
         (rational-constant-p x))
        ((eq (ffn-symb x) 'UNARY--)
	 (and (not (eq (fn-symb (arg1 x)) 'UNARY--))
	      (proveably-acl2-numberp 'x `((x . ,(arg1 x)))
				      mfc state)))
        ((eq (ffn-symb x) 'BINARY-*)
         (and (rational-constant-p (arg1 x))
              (< (unquote (arg1 x)) 0)))
        ((eq (fn-symb x) 'BINARY-+)
	 (and (negative-addends-p-1 (arg1 x) mfc state)
              (negative-addends-p-1 (arg2 x) mfc state)))
        (t
         nil)))

(defun weak-negative-addends-p (x mfc state)
  (declare (xargs :guard t))

  ;; This is similar to the above, but we do not consider the sign of
  ;; rational constants.

  (if (quotep x)
      nil
    (weak-negative-addends-p-1 x mfc state)))

(defun weak-negative-addends-balance (x mfc state)
  (declare (xargs :guard t))
  (cond ((variablep x)
	 -1)
	((fquotep x)
         (if (rational-constant-p x)
	     0
	   -1))
        ((eq (ffn-symb x) 'UNARY--)
	 (if (and (not (eq (fn-symb (arg1 x)) 'UNARY--))
		  (proveably-acl2-numberp 'x `((x . ,(arg1 x)))
					  mfc state))
	     1
	   -1))
        ((eq (ffn-symb x) 'BINARY-*)
         (if (and (rational-constant-p (arg1 x))
		  (< (unquote (arg1 x)) 0))
	     1
	   -1))
        ((eq (ffn-symb x) 'BINARY-+)
	 (+ (weak-negative-addends-balance (arg1 x) mfc state)
	    (weak-negative-addends-balance (arg2 x) mfc state)))
        (t
         -1)))

(defun weak-mostly-negative-addends-p (x mfc state)

  ;; Are more than half the addends negative?

  (declare (xargs :guard t))
  (if (quotep x)
      nil
    (< 0 (weak-negative-addends-balance x mfc state))))

(defun divisive-factors-p-1 (x mfc state)
  (declare (xargs :guard t))
  (cond ((variablep x)
	 nil)
	((quotep x)
	 (and (not (integer-constant-p x))
	      (rational-constant-p x)
	      (equal (numerator (unquote x)) 1)))
	((eq (ffn-symb x) 'UNARY-/)
	 (and (not (eq (fn-symb (arg1 x)) 'UNARY-/))
	      (proveably-acl2-numberp 'x `((x . ,(arg1 x)))
				      mfc state)))
        ((eq (ffn-symb x) 'EXPT)
	 (if (quotep (arg2 x))
	     (and (integer-constant-p (arg2 x))
		  (< (unquote (arg2 x)) 0))
	   (negative-addends-p (arg2 x) mfc state)))
        ((eq (fn-symb x) 'BINARY-*)
	 (and (divisive-factors-p-1 (arg1 x) mfc state)
              (divisive-factors-p-1 (arg2 x) mfc state)))
        (t
         nil)))

(defun divisive-factors-p (x mfc state)
  (declare (xargs :guard t))

  ;; X is an ACL2 term.  We return t if x is a divisive factor, or a
  ;; product of divisive factors.  Here, an factor is considered to be
  ;; divisive if it is a non-integer rational constant of the form
  ;; 1/c, or prints as (/ ...) or (expt x n) where n is a
  ;; negative-addends-p.  We also require that x is not merely a
  ;; constant.

  (if (quotep x)
      nil
    (divisive-factors-p-1 x mfc state)))

(defun divisive-factors-balance (x mfc state)
  (declare (xargs :guard t))
  (cond ((variablep x)
	 -1)
	((quotep x)
	 (if (and (not (integer-constant-p x))
		  (rational-constant-p x)
		  (equal (numerator (unquote x)) 1))
	     1
	   -1))
	((eq (ffn-symb x) 'UNARY-/)
	 (if (and (not (eq (fn-symb (arg1 x)) 'UNARY-/))
		  (proveably-acl2-numberp 'x `((x . ,(arg1 x)))
					  mfc state))
	     1
	   -1))
        ((eq (ffn-symb x) 'EXPT)
	 (if (if (quotep (arg2 x))
		 (and (integer-constant-p (arg2 x))
		      (< (unquote (arg2 x)) 0))
	       (mostly-negative-addends-p (arg2 x) mfc state))
	     1
	   -1))
        ((eq (fn-symb x) 'BINARY-*)
	 (+ (divisive-factors-balance (arg1 x) mfc state)
	    (divisive-factors-balance (arg2 x) mfc state)))
        (t
         -1)))

(defun mostly-divisive-factors-p (x mfc state)
  (declare (xargs :guard t))

  ;; Are more than half the factors divisive?

  (if (quotep x)
      nil
    (< 0 (divisive-factors-balance x mfc state))))

(defun weak-divisive-factors-p-1 (x mfc state)
  (declare (xargs :guard t))
  (cond ((variablep x)
	 nil)
	((quotep x)
	 (rational-constant-p x))
	((eq (ffn-symb x) 'UNARY-/)
	 (and (not (eq (fn-symb (arg1 x)) 'UNARY-/))
	      (proveably-acl2-numberp 'x `((x . ,(arg1 x)))
				      mfc state)))
        ((eq (ffn-symb x) 'EXPT)
	 (if (quotep (arg2 x))
	     (and (integer-constant-p (arg2 x))
		  (< (unquote (arg2 x)) 0))
	   (weak-negative-addends-p (arg2 x) mfc state)))
        ((eq (fn-symb x) 'BINARY-*)
	 (and (weak-divisive-factors-p-1 (arg1 x) mfc state)
              (weak-divisive-factors-p-1 (arg2 x) mfc state)))
        (t
         nil)))

(defun weak-divisive-factors-p (x mfc state)
  (declare (xargs :guard t))

  ;; This is similar to the above, but we do not consider the
  ;; divisiveness of rational constants.

  (if (quotep x)
      nil
    (weak-divisive-factors-p-1 x mfc state)))

(defun weak-divisive-factors-balance (x mfc state)
  (declare (xargs :guard t))
  (cond ((variablep x)
	 -1)
	((quotep x)
	 (if (rational-constant-p x)
	     0
	   -1))
	((eq (ffn-symb x) 'UNARY-/)
	 (if (and (not (eq (fn-symb (arg1 x)) 'UNARY-/))
		  (proveably-acl2-numberp 'x `((x . ,(arg1 x)))
					  mfc state))
	     1
	   -1))
        ((eq (ffn-symb x) 'EXPT)
	 (if (if (quotep (arg2 x))
		 (and (integer-constant-p (arg2 x))
		      (< (unquote (arg2 x)) 0))
	       (mostly-negative-addends-p (arg2 x) mfc state))
	     1
	   -1))
        ((eq (fn-symb x) 'BINARY-*)
	 (+ (weak-divisive-factors-balance (arg1 x) mfc state)
	    (weak-divisive-factors-balance (arg2 x) mfc state)))
        (t
         -1)))

(defun weak-mostly-divisive-factors-p (x mfc state)
  (declare (xargs :guard t))

  ;; Are more than half the factors divisive?

  (if (quotep x)
      nil
    (< 0 (weak-divisive-factors-balance x mfc state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We try restricting if lifting to when the test is presumably
;;; useful to arithmetic reasoning.

(defun ok-to-lift-p (x)
  (declare (xargs :guard t))
  (cond ((variablep x)
	 t)
	((fquotep x)
	 t)
	((and (consp (cdr x))
	      (equal (car x) 'NOT))
	 ;; The negation of <term> is OK if <term> is.
	 (ok-to-lift-p (cadr x)))
	((and (consp (cdr x))
	      (equal (car x) 'IF)
	      (consp (cddr x))
	      (consp (cdddr x)))
	 ;; (IF <test> <t-b> <f-b>) is OK if <test>, <t-b>, and <f-b>
	 ;; are.
	 (and (ok-to-lift-p (cadr x))
	      (ok-to-lift-p (caddr x))
	      (ok-to-lift-p (cadddr x))))
	((consp x)
	 ;; The following arithmetic predicates are OK.
	 (member-eq (car x) '(acl2-numberp
			      rationalp
			      #+:non-standard-analysis realp
			      integerp
			      natp
			      posp
			      complex-rationalp
			      #+:non-standard-analysis complexp
			      equal
			      eql
			      <)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun addends (sum)
  (declare (xargs :guard t))
  (if (eq (fn-symb sum) 'BINARY-+)
      (cons (arg1 sum)
            (addends (arg2 sum)))
    (list sum)))

(defun factors (product)
  (declare (xargs :guard t))
  (if (eq (fn-symb product) 'BINARY-*)
      (cons (arg1 product)
            (factors (arg2 product)))
    (list product)))

(defun make-product (factors)
  (declare (xargs :guard t))
  (cond ((atom factors)
         ''1)
        ((atom (cdr factors))
         (car factors))
        ((atom (cddr factors))
         (list 'BINARY-* (car factors) (cadr factors)))
        (t
         (list 'BINARY-* (car factors) (make-product (cdr factors))))))

; Intersection-equal was added to ACL2 in Version 4.0.

;; [Jared] Modified 2015-04-30 to agree with the definition in data-structures.
;; FYI, this is why we need to use packages.

;; (defun set-equal (x y)
;;   (declare (xargs :guard t))
;;   (and (true-listp x)
;;        (true-listp y)
;;        (subsetp-equal x y)
;;        (subsetp-equal y x)))

(defun set-equal (a b)
  (declare (xargs :guard (and (true-listp a)
			      (true-listp b))))
  (and (subsetp-equal a b)
       (subsetp-equal b a)))


(defun common-factors (factors sum)
  (declare (xargs :measure (acl2-count sum)
                  :guard (true-listp factors)))

  ;; Factors are the common factors so far.  Sum is the rest of the
  ;; sum to be examined. Normalize-terms-such-as-1/ax+bx-fn calls this
  ;; the first time when it is examining a term of the form
  ;; (+ <addend> <rest-of-sum>), with factors the factors of <addend> and
  ;; sum <sum>.  Using intersection-equal we cull the common factors of
  ;; factors and the addends of sum.

  (cond ((atom factors)
         nil)
        ((eq (fn-symb sum) 'BINARY-+)
         (common-factors (intersection-equal factors (factors (arg1 sum)))
                         (arg2 sum)))
        (t
         (intersection-equal factors (factors sum)))))

(defun remainder (common-factors sum)
  (declare (xargs :guard (true-listp common-factors)))

  ;; We form a new sum which is the original sum but with the common
  ;; factors removed from each addend.  That is, we return
  ;; (/ sum (make-product common)) where we assume that
  ;; (make-product common) is non-zero.

  (if (eq (fn-symb sum) 'BINARY-+)
      (let ((first (make-product (set-difference-equal (factors (arg1 sum))
                                                       common-factors))))
        (list 'BINARY-+ first (remainder common-factors (arg2 sum))))
    (make-product (set-difference-equal (factors sum)
                                        common-factors))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The following is close to correct, but see the implentation of
;;; simplify-ok-p and its associated comments for the truth.

;;; When used as a syntaxp hypothesis in a simplification rule,
;;; ok-to-perform-xxx-simplification-p should prohibit the use of the
;;; rule only when type-set can
;;; 1. determine that the original lhs and rhs of the inequality are
;;;  integers, but
;;; 2. cannot determine that the new ones are alos integers.

;;; I will thus be performing the simplification unless to do so will
;;; prevent linear arithmetic from using the ``1+ trick''
;;; (implies (and (integerp lhs)
;;;               (integerp rhs))
;;;          (equal (< lhs rhs)
;;;                 (<= (+ 1 lhs) rhs)))

;;; This limitation will occasionaly allow linear arithmetic to prove
;;; theorems it would not otherwise be able to.  Here is part of an
;;; email exchange with Bill Legato on the subject:

#|
 Note: In the examples below I use the dummy function foo to force
 simplification of the inequalites before linear arithemtic can be
 brought to bear on the conclusion.  This simulates 1) the use of
 linear arithmetic during backchaining which is by far the most common
 situation linear arithmetic is used, and 2) the interaction of rewrite
 rules and linear arithmetic when an inequality appears at a goal other
 than the initial one.  I used the two events:

 (defstub foo (x) t)

 (defaxiom foo-thm
   (implies (equal x x)
          (equal (foo x)
                 x)))

 The rule that allows the other libraries to solve the problems that
 the current version of arithmetic-3 misses is, in its simplest form:

 (implies (and (rationalp x)
               (rationalp y)
               (rationalp z)
               (< 0 x))
          (equal (< (* x y) (* x z))
                 (< y z)))

 This rule allows the thm:

 (thm (implies (and (integerp x)
                    (<= 0 x)
                    (integerp y)
                    (<= 0 y)
                    (< (* 3 x) (* 3 y)))
               (foo (< (+ 2 (* 3 x)) (* 3 y)))))

 to be simplified to:

 (implies (and (integerp x)
               (<= 0 x)
               (integerp y)
               (<= 0 y)
               (< x y))
          (< (+ 2 (* 3 x)) (* 3 y)))

 when linear arithmetic can prove the goal through the use of the ``1+
 trick'', by using (<= (+ 1 x) y) rather than the weaker (< x y).

 I had not been carrying out such simplifications in cases where x was a
 constant.  I had not not been doing so, because I had seen problems like:

     (thm
      (implies (and (rationalp x)
                  (integerp (* 3 x))
                  (rationalp y)
                  (integerp (* 3 y))
                  (< (* 3 x) (* 3 y)))
             (foo (< (+ 2 (* 9 x)) (* 9 y)))))

 where carrying out the division destroys the ability to use the trick.
 As you mentioned in one of your emails, the difference in reasoning
 about integers or rationals can make quite a difference sometimes.  I
 have certainly traced down failed proofs to such issues, and this led
 me to not performing such cancelations.

 ===== Begin side bar comment one

 However, even after carrying out this division, the book
 rtl/rel5/arithmetic/top can still prove the above with the help of the
 rule:

 (defthm *-strongly-monotonic
   (implies (and (< y y+)
                 (< 0 x)
                 (case-split (rationalp x))
                 )
            (< (* x y) (* x y+)))
   :rule-classes
   ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
    (:linear)
    (:forward-chaining
     :trigger-terms ((* y x) (* y+ x))
     :corollary
     (implies (and
                   (< y y+)
                   (< 0 x)
                   (case-split (rationalp x))
                   )
              (< (* y x) (* y+ x))))
    (:linear
     :corollary
     (implies (and
                   (< y y+)
                   (< 0 x)
                   (case-split (rationalp x))
                   )
              (< (* y x) (* y+ x))))))

 I do not include this rule because I found it too expensive and
 inconsistent in its applications.  My non-linear arithmetic extensions
 can get many more theorems than can this rule (although not all of
 them) at a smaller price in time used.  In fact it was this rule and
 its variations (see the various fp2 books) and just such problems which
 led me to develop the non-linear extension.

 Note that the inconsistencies in the application of this rule have
 been somewhat alleviated in more recent versions of ACL2 by the
 ability of forward-chaining rules to take on more than one
 instantiation.  I still, however, believe that my non-linear
 arithmetic extension is better.

 ===== End side bar comment one

 ===== Begin side bar comment two

 Each of the libraries

 arithmetic/top
 arithmetic-3/bind-free/top
 rtl/rel5/arithmetic/top

 can get three of the following five thms:

 ;;; The basic example:

 (thm (implies (and (integerp x)
                    (<= 0 x)
                    (integerp y)
                    (<= 0 y)
                    (< (* 3 x) (* 3 y)))
               (foo (< (+ 2 (* 3 x)) (* 3 y)))))

 ;;; Since
 ;;; (thm
 ;;;  (implies (and (integerp x)
 ;;;                (integerp y))
 ;;;          (equal (< x y)
 ;;;                  (<= (+ 1 x) y))))
 ;;; the following is logically equivalent to the above:

 (thm (implies (and (integerp x)
                    (<= 0 x)
                    (integerp y)
                    (<= 0 y)
                    (<= (+ 1 (* 3 x)) (* 3 y)))
               (foo (< (+ 2 (* 3 x)) (* 3 y)))))

 ;;; This is just the first with x and y replaced with (* 3 x)
 ;;; and (* 3 y) respectively

 (thm
  (implies (and (rationalp x)
                (<= 0 x)
                (integerp (* 3 x))
                (rationalp y)
                (<= 0 y)
                (integerp (* 3 y))
                (< (* 3 x) (* 3 y)))
           (foo (< (+ 2 (* 9 x)) (* 9 y)))))

 ;;; A slight weakening of the above

 (thm
  (implies (and (rationalp x)
                (<= 0 x)
                (integerp (* 3 x))
                (rationalp y)
                (<= 0 y)
                (integerp (* 3 y))
                (< (+ 1 (* 3 x)) (* 3 y)))
           (foo (< (+ 2 (* 9 x)) (* 9 y)))))

 ;;; A slightly more elaborate thm.

 (thm
  (implies (and (rationalp x)
                (<= 0 x)
                (integerp (* 3 x))
                (rationalp y)
                (<= 0 y)
                (integerp (* 3 y))
                (integerp z1)
                (integerp z2)
                (< (* 3 (+ x z1)) (* 3 (+ y z2))))
           (foo (< (+ 2 (* 9 (+ x z1))) (* 9 (+ x z2))))))

 ===== End side bar comment two

 I now believe that my rejection of such simplifications --- no
 elimination of constants across equalities or inequalities --- was too
 sweeping.  The proper solution is to do so only when it is safe, but
 defining ``safe'' is probably impossible in general.  I will carry out
 such simplifications across equalities.  I will also carry out such
 simplifications across inequalities only when to do so will not
 destroy any integerp knowledge.  At its simplest:

 (implies (and (integerp (* x y))
               (integerp (* x z))
               (rationalp x)
               (< 0 x)
               (integerp y)
               (integerp z))
          (equal (< (* x y) (* x z))
                 (< y z)))

 (implies (and (not (integerp (* x y)))
               (not (integerp (* x z)))
               (rationalp x)
               (< 0 x)
               (rationalp y)
               (rationalp z))
          (equal (< (* x y) (* x z))
                 (< y z)))

 I may wish to carry out otherwise ``unsafe'' simplifications after the
 clause has stabilized under simplification, but I don't think so.

 Robert

|#

(defun mfc-obj (x mfc state)
  (declare (xargs :guard t))
  (declare (ignore x state))

  ;; Should we return something which is not a valid objective, rather
  ;; than '?.

  ;; (thm (equal (access metafunction-context mfc :obj)
  ;;             (cadr mfc)))

  (if (and (consp mfc)
	   (consp (cdr mfc)))
      (cadr mfc)
    '?))

(defun ts-fix (x)
  (declare (xargs :guard t))
  (let ((int-x (ifix x)))
    (if (and (<= *min-type-set* int-x)
	     (<= int-x *max-type-set*))
	int-x
    0)))

(defthm ts-fix-min
  (<= *min-type-set*
      (ts-fix x))
  :rule-classes :linear)

(defthm ts-fix-max
  (<= (ts-fix x)
      *max-type-set*)
  :rule-classes :linear)

(defun simplify-ok-p-1 (orig-term new-term alist mfc state)
  (declare (xargs :guard t
		  :guard-hints (("Goal" :in-theory (disable arg1 arg2 mfc-obj ts-fix)))))
  (let ((orig-lhs (arg1 orig-term))
	(orig-rhs (arg2 orig-term))
	(new-lhs (arg1 new-term))
	(new-rhs (arg2 new-term)))
    (if (and (ts-subsetp (ts-fix (mfc-ts orig-lhs mfc state)) *ts-integer*)
	     (ts-subsetp (ts-fix (mfc-ts orig-rhs mfc state)) *ts-integer*))

	;; So the original lhs and rhs are known to be integers.
	;; Will the new ones be also?

	(and (let ((rewritten-new-lhs (mfc-rw+ new-lhs
							 alist
							 '? nil mfc state)))
	       (ts-subsetp (ts-fix (mfc-ts rewritten-new-lhs mfc state))
			   *ts-integer*))
	     (let ((rewritten-new-rhs (mfc-rw+ new-rhs
							 alist
							 '? nil mfc state)))
	       (ts-subsetp (ts-fix (mfc-ts rewritten-new-rhs mfc state))
			   *ts-integer*)))

      ;; At least one of the original lhs and rhs were not known to be
      ;; integers.  Proceed with the simplification.

      t)))

(defun simplify-ok-p (orig-term new-term alist mfc state)
  (declare (xargs :guard t))

  ;; Orig-term is the original term as seen by the rule which called
  ;; this.  New-term is the right-hand side of the rules conclusion.
  ;; Alist is the binding alist which binds the vars of new-term to
  ;; their correct values.  Both orig-term and new-term are assumed to
  ;; be an equality or inequality.

  (let ((relation (fn-symb orig-term))
	(obj (mfc-obj orig-term mfc state))
	(ancestors (mfc-ancestors mfc))
	(goal (mfc-clause mfc)))
    (cond ((eq obj t)

	   ;; Since linear arithmetic works by looking for a
	   ;; contradiction, we will be adding the negation of term
	   ;; to the linear arithmetic database.

	   (cond ((eq relation '<)

		  ;; We will be adding (<= rhs lhs), so the 1+-trick
		  ;; is not applicable.  Go ahead and simplify.

		  t)
		 ((eq relation 'EQUAL)

		  ;; We will be adding (or (< lhs rhs) (< rhs lhs)),
		  ;; so we must check further before we can tell if
		  ;; the 1+-trick applies.

		  (simplify-ok-p-1 orig-term new-term
				   alist
				   mfc state))
		 (t			; This shouldn't happen
		  nil)))
	  
	  ((eq obj nil)

	   ;; Since are looking to prove term false, we will be adding
	   ;; term to the linear arithmetic database.

	   (cond ((eq relation '<)

		  ;; We will be adding (< lhs rhs), so we must check
		  ;; further before we can tell if the 1+-trick
		  ;; applies.

		  (simplify-ok-p-1 orig-term new-term
				   alist
				   mfc state))
		 ((eq relation 'EQUAL)

		  ;; We will be adding (and (<= lhs rhs) (<= rhs lhs)),
		  ;; so the 1+-trick is not applicable.

		  t)
		 (t			; This shouldn't happen
		  nil)))
	  
	  ((null ancestors)

	   ;; We are rewriting some part of the goal.

	   (let ((parity (present-in-goal-1 orig-term goal)))

	     ;; When we refer to linear arithmetic seeing some
	     ;; inequality below, we are referring to the setting up
	     ;; of the initial simlpify-clause-pot-lst, not the use of
	     ;; linear arithmetic during rewriting.

	     (cond ((eq parity 'positive)
		    (cond ((eq relation '<)

			   ;; Linear arithmetic sees this as
			   ;; (<= rhs lhs), so the 1+-trick is not
			   ;; applicable.  Go ahead and simplify.

			   t)
			  ((eq relation 'EQUAL)

			   ;; Linear arithmetic sees this as
			   ;; (or (< lhs rhs) (< rhs lhs)), so we must
			   ;; check further before we can tell if the
			   ;; 1+-trick applies.

			   (simplify-ok-p-1 orig-term new-term
					    alist
					    mfc state))
			  (t		; This shouldn't happen
			   nil)))
		   ((eq parity 'negative)
		    (cond ((eq relation '<)

			   ;; Linear arithmetic sees this as
			   ;; (< lhs rhs), so we must check further
			   ;; before we can tell if the 1+-trick
			   ;; applies.

			   (simplify-ok-p-1 orig-term new-term
					    alist
					    mfc state))
			  ((eq relation 'EQUAL)

			   ;; Linear arithmetic sees this as
			   ;; (and (<= lhs rhs) (<= rhs lhs)), so the
			   ;; 1+-trick is not applicable.

			   t)
			  (t		; This shouldn't happen
			   nil)))
		   (t

		    ;; We are rewriting the goal, but term does not
		    ;; appear as a top-level literal in the goal.
		    ;; However, if term is part of an if-expression or
		    ;; some such it may appear at the top-level of the
		    ;; next goal, so we leave it alone.

		    nil))))
	  
	  (t

	   ;; We are backchaining and we will not be using linear
	   ;; arithmetic (obj is '?).  We may as well go ahead and
	   ;; simplify.

	   t))))
