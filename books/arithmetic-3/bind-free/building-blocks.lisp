; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; building-blocks.lisp
;;;
;;; This book contains a few functions we have found helpful when
;;; defining bind-free rules.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(table acl2-defaults-table :state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Since we mostly deal with binary operations in our bind-freee
;;; rules, we define a couple of macros for accessing the first
;;; and second args.

(defmacro arg1 (x)
  `(cadr ,x))

(defmacro arg2 (x)
  `(caddr ,x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A couple of simple recognizers for constants.

(defun numeric-constant-p (x)
  (declare (xargs :guard (pseudo-termp x)))
  (and (nvariablep x)
       (fquotep x)
       (acl2-numberp (unquote x))))

(defun rational-constant-p (x)
  (declare (xargs :guard (pseudo-termp x)))
  (and (nvariablep x)
       (fquotep x)
       (rationalp (unquote x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(mutual-recursion

 (defun fns-present (fns term)
   (declare (xargs :guard (and (symbol-listp fns)
                               (pseudo-termp term))))

   ;; Fns is a list of function symbols and term is an ACL2 term.
   ;; We determine whether any fn in fns is used anywhere in term.

   (cond ((or (variablep term)
              (fquotep term))
          nil)
         ((member-eq (ffn-symb term) fns)
          t)
         (t
          (fns-present-lst fns (fargs term)))))

 (defun fns-present-lst (fns args)
   (declare (xargs :guard (and (symbol-listp fns)
                               (pseudo-term-listp args))))
   (if (endp args)
       nil
     (or (fns-present fns (car args))
         (fns-present-lst fns (cdr args)))))

 )|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun negative-addends-p (x)
  (declare (xargs :guard (pseudo-termp x)))

  ;; X is an ACL2 term.  We return t if x is a negative addend, or a
  ;; sum of negative addends.  Here, an addend is considered to be
  ;; negative if it is a negative rational constant, or prints as
  ;; (- ...) or (* c ...) where c is a negative rational.

  (cond ((variablep x)
         nil)
        ((fquotep x)
         (and (rational-constant-p x)
              (< (unquote x) 0)))
        ((eq (ffn-symb x) 'UNARY--)
         (or (variablep (arg1 x))
             (not (eq (ffn-symb (arg1 x)) 'UNARY--))))
        ((eq (ffn-symb x) 'BINARY-*)
         (and (rational-constant-p (arg1 x))
              (< (unquote (arg1 x)) 0)))
        ((eq (fn-symb x) 'BINARY-+)
         (and (negative-addends-p (arg1 x))
              (negative-addends-p (arg2 x))))
        (t
         nil)))

(defun weak-negative-addends-p (x)
  (declare (xargs :guard (pseudo-termp x)))

  ;; X is an ACL2 term.  We return t if x is a negative addend, or a
  ;; sum of negative addends.  Here, an addend is considered to be
  ;; negative if it is a rational constant, or prints as
  ;; (- ...) or (* c ...) where c is a negative rational.

  (cond ((variablep x)
         nil)
        ((fquotep x)
         (rational-constant-p x))
        ((eq (ffn-symb x) 'UNARY--)
         (or (variablep (arg1 x))
             (not (eq (ffn-symb (arg1 x)) 'UNARY--))))
        ((eq (ffn-symb x) 'BINARY-*)
         (and (rational-constant-p (arg1 x))
              (< (unquote (arg1 x)) 0)))
        ((eq (fn-symb x) 'BINARY-+)
         (and (weak-negative-addends-p (arg1 x))
              (weak-negative-addends-p (arg2 x))))
        (t
         nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rewriting-goal-literal (x mfc state)
  (declare (xargs :guard t))

  ;; Are we rewriting a top-level goal literal, rather than rewriting
  ;; a hypothesis from a rewrite (or other) rule?  (Ancestors is a
  ;; list of the negations of backchaining hypotheses being pursued.
  ;; Hence we are rewriting a goal literal iff it is NIL.)

  (declare (ignore x state))
  (null (mfc-ancestors mfc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Wrappers for mfc-rw.

;;; We often want to answer the question, ``` Does ACL2 know
;;; that this term is an xxx?''' where xxx is one of
;;; a. integer, b. rational, c. non-zero number, or d. non-zero
;;; rational

(defun proveably-integer (x mfc state)
  (declare (xargs :guard t))

  ;; Can rewriting determine that x is an integer?

  (equal (mfc-rw `(INTEGERP ,x)
		 t t mfc state)
	 *t*))

(defun proveably-rational (x mfc state)
  (declare (xargs :guard t))

  ;; Can rewriting determine that x is rational?

  (equal (mfc-rw `(RATIONALP ,x)
		 t t mfc state)
	 *t*))

(defun proveably-non-zero1 (x mfc state)
  (declare (xargs :guard t))
  (equal (mfc-rw `(NOT (EQUAL (FIX ,x) '0))
		 t t mfc state)
	 *t*))

(defun proveably-non-zero (x mfc state)

  ;; If x is not an IF expression, can rewriting determine that it
  ;; is numeric and not equal to zero?

  (declare (xargs :guard (pseudo-termp x)))
  (cond ((variablep x)
         (proveably-non-zero1 x mfc state))
        ((fquotep x)
         (and (numeric-constant-p x)
              (not (equal x ''0))))
        ((eq (ffn-symb x) 'IF)
         nil)
        (t
         (proveably-non-zero1 x mfc state))))

(defun proveably-non-zero-rational1 (x mfc state)
  (declare (xargs :guard t))
  (equal (mfc-rw `(NOT (EQUAL (FIX ,x) '0))
		 t t mfc state)
	 *t*))

(defun proveably-non-zero-rational (x mfc state)

  ;; If x is not an IF expression, can rewriting determine that it
  ;; is rational and not equal to zero?

  (declare (xargs :guard (pseudo-termp x)))
  (cond ((variablep x)
         (proveably-non-zero1 x mfc state))
        ((fquotep x)
         (and (rational-constant-p x)
              (not (equal x ''0))))
        ((eq (ffn-symb x) 'IF)
         nil)
        (t
         (proveably-non-zero1 x mfc state))))