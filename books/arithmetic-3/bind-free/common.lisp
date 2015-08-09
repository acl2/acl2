; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; common-bind-free.lisp
;;;
;;; This book containd some functions common to normalize and
;;; simplify.
;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../pass1/top"))

(include-book "building-blocks")

(defun collect-+ (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (+ x y))

(defun collect-* (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (* x y))

(defun bubble-down (x match)
  (declare (xargs :guard t))
  (declare (ignore match))
  x)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun addend-pattern (addend)
  (declare (xargs :guard (pseudo-termp addend)))
  (cond ((variablep addend)
	 addend)
	((fquotep addend)
	 addend)
	((eq (ffn-symb addend) 'UNARY--)
	 (addend-pattern (arg1 addend)))
	((and (eq (ffn-symb addend) 'BINARY-*)
	      (rational-constant-p (arg1 addend)))
	 (addend-pattern (arg2 addend)))
	(t
	 addend)))

(defun matching-addend-patterns-p (pattern1 pattern2)
  (declare (xargs :guard t))
  (cond ((quotep pattern1)
         nil)
        (t
         (equal pattern1 pattern2))))

(defun matching-addend-p (pattern addend)
  (declare (xargs :guard (pseudo-termp addend)))
  (let ((addend-pattern (addend-pattern addend)))
    (matching-addend-patterns-p pattern addend-pattern)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factor-pattern-exponent2 (addend weight)
  (declare (xargs :guard (and (pseudo-termp addend)
                              (rationalp weight)
                              (not (equal weight 0)))))
  (if (and (eq (fn-symb addend) 'BINARY-*)
           (rational-constant-p (arg1 addend)))
      (if (eql (unquote (arg1 addend)) weight)
          (arg2 addend)
        `(BINARY-* ,(kwote (/ (unquote (arg1 addend))
                              weight))
                   ,(arg2 addend)))
    `(BINARY-* ,(kwote (/ weight)) ,addend)))

(defun factor-pattern-exponent1 (exponent weight)
  (declare (xargs :guard (and (pseudo-termp exponent)
                              (rationalp weight)
                              (not (equal weight 0)))))
  (if (eq (fn-symb exponent) 'BINARY-+)
      `(BINARY-+ ,(factor-pattern-exponent2 (arg1 exponent) weight)
		 ,(factor-pattern-exponent1 (arg2 exponent) weight))
    (factor-pattern-exponent2 exponent weight)))

(defun factor-pattern-exponent (exponent)
  (declare (xargs :guard (pseudo-termp exponent)))
  (cond ((or (variablep exponent)
             (fquotep exponent))
         exponent)
        ((eq (ffn-symb exponent) 'UNARY--)
         (factor-pattern-exponent (arg1 exponent)))
        ((eq (ffn-symb exponent) 'BINARY-*)
         (if (rational-constant-p (arg1 exponent))
             (arg2 exponent)
           exponent))
        ((eq (ffn-symb exponent) 'BINARY-+)
         (if (and (eq (fn-symb (arg1 exponent)) 'BINARY-*)
                  (rational-constant-p (arg1 (arg1 exponent)))
                  (not (equal (arg1 (arg1 exponent)) ''0)))
             (let ((weight (unquote (arg1 (arg1 exponent)))))
               (factor-pattern-exponent1 exponent weight))
           exponent))
        (t
         exponent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factor-pattern-gather-exponents (factor)
  (declare (xargs :guard (pseudo-termp factor)))

; We only consider the base of an exponential when determining
; a match.  We handle quotep's carefully.  We want 2 to match
; with (expt 1/2 n), but not with 3 or (expt 3 n).  We
; also want (expt 2 n) to match with (expt 3 n) and
; (expt 2 m) but not with (expt 3 i).  See pattern-matchp.

  (cond ((variablep factor)
         factor)
        ((fquotep factor)
         (let ((c (unquote factor)))
           (cond ((eql c 0)
                  0)
                 ((rationalp c)
                  (if (< (abs c) 1)
                      (/ c)
                    c))
                 ((acl2-numberp c)
                  c)
                 (t
                  0))))
        ((eq (ffn-symb factor) 'UNARY-/)
         (factor-pattern-gather-exponents (arg1 factor)))
        ((eq (ffn-symb factor) 'UNARY--)
         (factor-pattern-gather-exponents (arg1 factor)))
        ((eq (ffn-symb factor) 'EXPT)
         (let ((base (factor-pattern-gather-exponents (arg1 factor)))
               (exponent (factor-pattern-exponent (arg2 factor))))
           (if (acl2-numberp base)
               (list 'do-not-use-this-symbol base exponent)
             base)))
        (t
         factor)))

(defun matching-factor-gather-exponents-patterns-p (pattern1 pattern2)
  (declare (xargs :guard t))
  (cond ((acl2-numberp pattern1)
         (and (consp pattern2)
              (eq (car pattern2) 'do-not-use-this-symbol)
              (consp (cdr pattern2))
              (equal pattern1 (cadr pattern2))))
        ((and (consp pattern1)
              (eq (car pattern1) 'do-not-use-this-symbol)
              (consp (cdr pattern1)))
         (or  (equal (cadr pattern1) pattern2)
              (and (consp pattern2)
                   (eq (car pattern2) 'do-not-use-this-symbol)
                   (consp (cdr pattern2))
                   (or (equal (cadr pattern1) (cadr pattern2)) ; same base
                       (and (consp (cddr pattern1))
                            (consp (cddr pattern2))
                            (equal (caddr pattern1) (caddr pattern2))))))) ; same exponent
        (t
         (equal pattern1 pattern2))))

(defun matching-factor-gather-exponents-p (pattern factor)
  (declare (xargs :guard (pseudo-termp factor)))
  (let ((factor-pattern (factor-pattern-gather-exponents factor)))
    (matching-factor-gather-exponents-patterns-p pattern factor-pattern)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factor-pattern-scatter-exponents (factor)
  (declare (xargs :guard (pseudo-termp factor)))

; This function is similar to factor-pattern-match-base with the
; added twist that we consider exponents also.  Here, 2 will match
; 3 but not (expt 2 n).  Also, (expt 2 n) will match
; (expt 1/2 (* 3 n)) but not (expt 3 n).

  (cond ((variablep factor)
         factor)
        ((fquotep factor)
         (let ((c (unquote factor)))
           (cond ((eql c 0)
                  0)
                 ((rationalp c)
                  (if (< (abs c) 1)
                      (/ c)
                    c))
                 ((acl2-numberp c)
                  c)
                 (t
                  0))))
        ((eq (ffn-symb factor) 'UNARY-/)
         (factor-pattern-scatter-exponents (arg1 factor)))
        ((eq (ffn-symb factor) 'UNARY--)
         (factor-pattern-scatter-exponents (arg1 factor)))
        ((eq (ffn-symb factor) 'EXPT)
         (let ((base (factor-pattern-scatter-exponents (arg1 factor)))
               (exponent (factor-pattern-exponent (arg2 factor))))
           (if (acl2-numberp base)
               (list 'do-not-use-this-symbol base exponent)
             (cond ((variablep exponent)
                    `(EXPT ,base ,exponent))
                   ((fquotep exponent)
                    base)
                   (t
                    `(EXPT ,base ,exponent))))))
        (t
         factor)))

(defun matching-factor-scatter-exponents-patterns-p (pattern1 pattern2)
  (declare (xargs :guard t))
  (and (consp pattern1)
       (eq (car pattern1) 'do-not-use-this-symbol)
       (consp pattern2)
       (eq (car pattern2) 'do-not-use-this-symbol)
       (consp (cdr pattern1))
       (consp (cdr pattern2))
       (consp (cddr pattern1))
       (consp (cddr pattern2))
       (equal (caddr pattern1) (caddr pattern2)))) ; same exponent

(defun matching-factor-scatter-exponents-p (pattern factor)
  (declare (xargs :guard (pseudo-termp factor)))
  (let ((factor-pattern (factor-pattern-scatter-exponents factor)))
    (matching-factor-scatter-exponents-patterns-p pattern factor-pattern)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun arith-factor-pattern-gather-exponents (factor)
  (declare (xargs :guard (pseudo-termp factor)))
  (cond ((variablep factor)
         factor)
        ((fquotep factor)
         (let ((c (unquote factor)))
           (cond ((eql c 0)
                  0)
                 ((rationalp c)
                  (if (< (abs c) 1)
                      (/ c)
                    c))
                 ((acl2-numberp c)
                  c)
                 (t
                  0))))
        ((eq (ffn-symb factor) 'UNARY-/)
         (arith-factor-pattern-gather-exponents (arg1 factor)))
        ((eq (ffn-symb factor) 'UNARY--)
         (arith-factor-pattern-gather-exponents (arg1 factor)))
        ((eq (ffn-symb factor) 'EXPT)
         (let ((base (arith-factor-pattern-gather-exponents (arg1 factor)))
               (exponent (factor-pattern-exponent (arg2 factor))))
           (if (acl2-numberp base)
               (list 'do-not-use-this-symbol base exponent)
             base)))
        (t
         factor)))

(defun arith-matching-factor-gather-exponents-patterns-p (pattern1 pattern2)
  (declare (xargs :guard t))
  (cond ((acl2-numberp pattern1)
         (and (consp pattern2)
              (eq (car pattern2) 'do-not-use-this-symbol)
              (consp (cdr pattern2))
              (equal pattern1 (cadr pattern2))))
        ((and (consp pattern1)
              (eq (car pattern1) 'do-not-use-this-symbol)
              (consp (cdr pattern1)))
         (or  (equal (cadr pattern1) pattern2)
              (and (consp pattern2)
                   (eq (car pattern2) 'do-not-use-this-symbol)
                   (consp (cdr pattern2))
                   (or (equal (cadr pattern1) (cadr pattern2)) ; same base
                       (and (consp (cddr pattern1))
                            (consp (cddr pattern2))
                            (equal (caddr pattern1) (caddr pattern2))))))) ; same exponent
        (t
         (equal pattern1 pattern2))))

(defun arith-matching-factor-gather-exponents-p (pattern factor)
  (declare (xargs :guard (pseudo-termp factor)))
  (let ((factor-pattern (arith-factor-pattern-gather-exponents factor)))
    (arith-matching-factor-gather-exponents-patterns-p pattern factor-pattern)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun arith-factor-pattern-scatter-exponents (factor)
  (declare (xargs :guard (pseudo-termp factor)))
  (cond ((variablep factor)
         factor)
        ((fquotep factor)
         (let ((c (unquote factor)))
           (cond ((eql c 0)
                  0)
                 ((rationalp c)
                  (if (< (abs c) 1)
                      (/ c)
                    c))
                 ((acl2-numberp c)
                  c)
                 (t
                  0))))
        ((eq (ffn-symb factor) 'UNARY-/)
         (list 'do-not-use-this-symbol-either
               (arith-factor-pattern-scatter-exponents (arg1 factor))))
        ((eq (ffn-symb factor) 'UNARY--)
         (arith-factor-pattern-scatter-exponents (arg1 factor)))
        ((eq (ffn-symb factor) 'EXPT)
         (let ((base (arith-factor-pattern-scatter-exponents (arg1 factor)))
               (exponent (factor-pattern-exponent (arg2 factor))))
           (if (acl2-numberp base)
               (list 'do-not-use-this-symbol base exponent)
             (cond ((variablep exponent)
                    `(EXPT ,base ,exponent))
                   ((fquotep exponent)
                    base)
                   (t
                    `(EXPT ,base ,exponent))))))
        (t
         factor)))

(defun arith-matching-factor-scatter-exponents-patterns-p (pattern1 pattern2)
  (declare (xargs :guard t))
  (cond ((acl2-numberp pattern1)
         nil)
        ((and (consp pattern1)
              (eq (car pattern1) 'do-not-use-this-symbol)
              (consp pattern2)
              (eq (car pattern2) 'do-not-use-this-symbol))
         (and (consp (cdr pattern1))
              (consp (cdr pattern2))
              (not (eql (cadr pattern1) 0))
              (not (eql (cadr pattern2) 0))
              (equal (cadr pattern1) (cadr pattern2))
              (consp (cddr pattern1))
              (consp (cddr pattern2))
              (equal (caddr pattern1) (caddr pattern2))))
        ((and (consp pattern1)
              (eq (car pattern1) 'do-not-use-this-symbol-either)
              (consp (cdr pattern1)))
         (equal (cadr pattern1) pattern2))
        ((and (consp pattern2)
              (eq (car pattern2) 'do-not-use-this-symbol-either)
              (consp (cdr pattern2)))
         (equal pattern1 (cadr pattern2)))
        (t
         nil)))

(defun arith-matching-factor-scatter-exponents-p (pattern factor)
  (declare (xargs :guard (and (or (true-listp pattern)
                                  (acl2-numberp pattern)
                                  (variablep pattern))
                              (pseudo-termp factor))))
  (let ((factor-pattern (arith-factor-pattern-scatter-exponents factor)))
    (arith-matching-factor-scatter-exponents-patterns-p pattern factor-pattern)))
