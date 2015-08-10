; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; common.lisp
;;;
;;; This book contains some functions common to normalize.lisp and
;;; simplify.lisp.
;;;
;;; We wish to be able to ``combine like pieces'' of sums and products
;;; as well as of equalities and inequatities between them.  A couple
;;; of simple examples:
;;;
;;; ``normalization:''
;;; (+ x (* 3 x)) ==> (* 4 x)
;;;
;;; ``simplification:''
;;; (< (* x (expt y n)) (* y z)) ==> (cond ((equal y 0)
;;;                                         nil)
;;;                                        ((< 0 y)
;;;                                         (< (* x (expt y (+ -1 n)))
;;;                                            (fix z)))
;;;                                        (t
;;;                                         (< (fix z)
;;;                                            (* x (expt y (+ -1 n))))))
;;;
;;; The four files common.lisp, normalize.lisp, simplify.lisp, and
;;; collect.lisp cooperate to achieve this.  The strategy we use
;;; follows several steps.  We first describe ``normalization.''
;;;
;;; Normalization is the combining of like pieces within an individual
;;; sum or product.
;;;
;;; Step 1. We look for pairs of addends or factors which are like
;;; each other, i.e., have matching patterns.  The functions in this
;;; file define how to extract a piece's pattern and how to determine
;;; if two patterns match.  The simplest of these functions are
;;; addend-pattern and matching-addend-p.  The pattern of an addend is
;;; its ``variable part:''
;;;
;;; x ==> x
;;; (- (* x y)) ==> (* x y)
;;; (* 3 (foo x)) ==> (foo x)
;;;
;;; Two addend patterns match if they are non-constant and equal.
;;; That is, 3 does not match with 3, and (foo x) matches only with
;;; (foo x).  The other pattern extraction and matching functions
;;; follow a similar spirit but are more complicated.  Note that this
;;; process does not have to be as inefficient as it seems at first
;;; glance, since ACL2 rewrites from the inside-out.  We therefore
;;; only need to check whether the left-most addend or factor matches
;;; with anything else.  All the rest has already been normalized.
;;;
;;; Step 2. Let us assume that we are examining the expression
;;; (+ x y), where y may itself be a sum, and that x matches y or
;;; some addend inside it.  We form the new expression:
;;; (+ (bubble-down x match) y)
;;; where match is the matching addend.

;;; Bubble-down is a ``dummy'' function which is the identity on its
;;; first argument.  This function is disabled and all that ACL2 knows
;;; about it is how to ``bubble-down'' (named after the operation used
;;; in a bubble sort) is how to bring it along side the addend match.
;;; Once it is brought along side the addend match, ACL2 forms an
;;; expression similar to:
;;; (+ (collect-+ x match) z)
;;; See the various bubble-down-xxx rules in collect.lisp.
;;;
;;; Step 3. The addends of the expression (collect-+ x match) are
;;; combined appropriately.  See the various collect-xxx rules in
;;; collect.lisp.
;;;
;;; Simplification is the combining of like pieces accross an equality
;;; or inequality.  The strategy used is an elaboration of that for
;;; normalization.
;;;
;;; Step 1. Form a list of the patterns found on each side of the
;;; equality or inequality, and find the first match.  Then add or
;;; multiply as appropriate both sides of the equality or inequality
;;; by the inverse of the smaller matching pieces.  The inverse of
;;; an addend x is (- x), and the inverse of a factor x is (/ x).
;;; The variable x is smaller than (* 3 x) or (expt x n).
;;;
;;; Step 2. Each side of the equality or inequality is now treated
;;; as above.
;;;
;;; This multi step process has made the writing and verifying of
;;; these rules much easier than earlier trials.  In particular,
;;; writing and verifying meta rules such as those in meta or
;;; arithmetic-2/meta was quite a task.  Furthermore, the result of a
;;; meta rule is rewritten completely from the inside out which was
;;; quite inefficient at times.  The disadvantge of this strategy is
;;; that it is not easy to ensure that one has a sufficient variety of
;;; collect-xxx rules, and we did in fact miss some in earlier versions
;;; of these books.  We (again) believe that we have now sufficient
;;; coverage.
;;;
;;; We document the functions in this book only lightly if at all.  It
;;; is not clear that english is well suited to such tasks.  There are
;;; a lot of cases (each one simple), and I find the code at least as
;;; clear as any english description I have been able to generate.
;;; Read the code and try running various examples.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

(local
 (include-book "../../support/top"))

(table acl2-defaults-table :state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;; addend patterns

(defun addend-pattern (addend)
  (declare (xargs :guard t))
  (cond ((variablep addend)
	 addend)
	((fquotep addend)
	 addend)
	((eq (ffn-symb addend) 'UNARY--)
	 (arg1 addend))
	((and (eq (ffn-symb addend) 'BINARY-*)
	      (rational-constant-p (arg1 addend)))
	 (arg2 addend))
	(t
	 addend)))

(defun matching-addend-patterns-p (pattern-1 pattern-2)
  (declare (xargs :guard t))
  (cond ((quotep pattern-1)
         nil)
        (t
         (equal pattern-1 pattern-2))))

(defun matching-addend-p (pattern addend)
  (declare (xargs :guard t))
  (let ((addend-pattern (addend-pattern addend)))
    (matching-addend-patterns-p pattern addend-pattern)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factor-pattern-base (x)
  (declare (xargs :guard t))
  (cond ((variablep x)
         x)
        ((and (fquotep x)
	      (consp (cdr x)))
	 (if (and (power-of-2 x)
		  (not (equal x ''1))
		  (not (equal x ''-1)))
	     2
	   (unquote x)))
        (t
         x)))

(defun matching-exponents (exp-1 exp-2)
  (declare (xargs :guard t))
  (equal (addend-pattern exp-1)
	 (addend-pattern exp-2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; factor patterns --- gather exponents

(defun factor-pattern-gather-exponents (factor)
  (declare (xargs :guard t))
  (cond ((variablep factor)
         factor)
        ((and (fquotep factor)
	      (consp (cdr factor)))
           (cond ((and (power-of-2-generalized factor)
		       (not (equal factor ''1))
		       (not (equal factor ''-1)))
		  2)   ; powers of 2 are handled specially.
                 ((rational-constant-p factor)
                  (abs (unquote factor)))
                 (t
                  (unquote factor))))
        ((eq (ffn-symb factor) 'UNARY-/)
         (factor-pattern-gather-exponents (arg1 factor)))
        ((eq (ffn-symb factor) 'EXPT)
         (let ((base (factor-pattern-base (arg1 factor)))
               (exponent (arg2 factor)))
           (if (acl2-numberp base)
               `(EXPT-WITH-CONST-BASE ,base ,exponent)
             base)))
        (t
         factor)))

(defun matching-factor-gather-exponents-patterns-p (pattern-1 pattern-2)
  (declare (xargs :guard t))
  (cond ((acl2-numberp pattern-1)
         (and (not (equal pattern-1 0))
	      (eq (fn-symb pattern-2) 'EXPT-WITH-CONST-BASE)
	      (equal pattern-1 (arg1 pattern-2))))
        ((eq (fn-symb pattern-1) 'EXPT-WITH-CONST-BASE)
	 (cond ((equal (arg1 pattern-1) 0)
		nil)
	       ((equal (arg1 pattern-1) pattern-2)
		t)
	       ((eq (fn-symb pattern-2) 'EXPT-WITH-CONST-BASE)
		(or (equal (arg1 pattern-1) (arg1 pattern-2))
		    (equal (arg2 pattern-1) (arg2 pattern-2))))
	       (t
		nil)))
        (t
         (equal pattern-1 pattern-2))))

(defun matching-factor-gather-exponents-p (pattern factor)
  (declare (xargs :guard t))
  (let ((factor-pattern (factor-pattern-gather-exponents factor)))
    (matching-factor-gather-exponents-patterns-p pattern factor-pattern)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; factor patterns --- scatter exponents

(defun factor-pattern-scatter-exponents (factor)
  (declare (xargs :guard t))
  (cond ((variablep factor)
         factor)
        ((fquotep factor)
	 0)  ; Doesn't matter, because we do not match numbers.
        ((eq (ffn-symb factor) 'UNARY-/)
         (factor-pattern-scatter-exponents (arg1 factor)))
        ((eq (ffn-symb factor) 'EXPT)
         (let ((base (factor-pattern-base (arg1 factor)))
               (exponent (arg2 factor)))
           (cond ((acl2-numberp base)
		  `(EXPT-WITH-CONST-BASE ,base ,exponent))
		 ((quotep exponent)  ; Presumably too large to expand
		  base)
		 (t
		  `(EXPT ,base ,exponent)))))
        (t
         factor)))

(defun matching-factor-scatter-exponents-patterns-p (pattern-1 pattern-2)
  (declare (xargs :guard t))
  (cond ((acl2-numberp pattern-1)
         nil)
        ((eq (fn-symb pattern-1) 'EXPT-WITH-CONST-BASE)
	 (cond ((equal (arg1 pattern-1) 0)
		nil)
	       ((eq (fn-symb pattern-2) 'EXPT-WITH-CONST-BASE)
		(matching-exponents (arg2 pattern-1) (arg2 pattern-2)))
	       (t
		nil)))
        ((eq (fn-symb pattern-1) 'EXPT)
	 (cond ((equal (arg1 pattern-1) 0)
		nil)
	       ((eq (fn-symb pattern-2) 'EXPT)
		(and (equal (arg1 pattern-1) (arg1 pattern-2))
		     (matching-exponents (arg2 pattern-1) (arg2 pattern-2))))
	       (t
		nil)))
        (t
         (equal pattern-1 pattern-2))))

(defun matching-factor-scatter-exponents-p (pattern factor)
  (declare (xargs :guard t))
  (let ((factor-pattern (factor-pattern-scatter-exponents factor)))
    (matching-factor-scatter-exponents-patterns-p pattern factor-pattern)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; we now include a bunch of stuff that used to be in simplify.lisp.
;;; We want to use these pieces in floor-mod.llisp.  It really should
;;; be cleaned up.



(defun good-val-triple-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (real/rationalp (car x))
       (consp (cdr x))
       (real/rationalp (cadr x))
       (consp (cddr x))
       (real/rationalp (caddr x))))

(defun val-< (x y)
  (declare (xargs :guard (and (good-val-triple-p x)
			      (good-val-triple-p y))))

  ;; x and y are triples of rationals.  We use a dictionary type
  ;;order.

  (cond ((< (car x) (car y))
	 t)
	((< (car y) (car x))
	 nil)
	((< (cadr x) (cadr y))
	 t)
	((< (cadr y) (cadr x))
	 nil)
	((< (caddr x) (caddr y))
	 t)
	(t
	 nil)))

(defun info-entry-p (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (good-val-triple-p (cadr x))))

(defun info-list-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (info-entry-p (car x))
           (info-list-p (cdr x)))
    (eq x nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factor-val-gather-exponents1 (exponent)
  (declare (xargs :guard t
		  :verify-guards nil))
  (cond ((variablep exponent)
         1)
        ((rational-constant-p exponent)
         (abs (unquote exponent)))
        ((eq (ffn-symb exponent) 'BINARY-*)
         (if (rational-constant-p (arg1 exponent))
             (abs (unquote (arg1 exponent)))
           1))
        ((eq (ffn-symb exponent) 'BINARY-+)
         (+ (factor-val-gather-exponents1 (arg1 exponent))
            (factor-val-gather-exponents1 (arg2 exponent))))
        (t
         1)))

 (local
  (defthm factor-val-gather-exponents1-thm
    (acl2-numberp (factor-val-gather-exponents1 x))))

 (verify-guards factor-val-gather-exponents1)

(defun factor-val-gather-exponents (factor)
  (declare (xargs :guard t))
  (cond ((variablep factor)
	 (list 0 1 0))
	((constant-p factor)
	 (let ((val (unquote factor)))
	   (if (rationalp val)   ; OK to use instead of real/rationalp because there all realp *constants* are rationalp
	       (list 0 0 (abs val))
	     (list 0 0 1))))
	((eq (ffn-symb factor) 'UNARY-/)
	 (factor-val-gather-exponents (arg1 factor)))
	((eq (ffn-symb factor) 'UNARY--)
	 (factor-val-gather-exponents (arg1 factor)))
	((eq (ffn-symb factor) 'EXPT)
         (list (factor-val-gather-exponents1 (arg2 factor)) 0 0))
	(t
	 (list 0 1 0))))

(defun factor-val-scatter-exponents1 (exponent)
  (declare (xargs :guard t
		  :verify-guards nil))
  (cond ((variablep exponent)
         1)
        ((rational-constant-p exponent)
         (abs (unquote exponent)))
        ((eq (ffn-symb exponent) 'BINARY-*)
         (if (rational-constant-p (arg1 exponent))
             (abs (unquote (arg1 exponent)))
           1))
        ((eq (ffn-symb exponent) 'BINARY-+)
         (+ (factor-val-scatter-exponents1 (arg1 exponent))
            (factor-val-scatter-exponents1 (arg2 exponent))))
        (t
         1)))

 (local
  (defthm factor-val-scatter-exponents1-thm
    (acl2-numberp (factor-val-scatter-exponents1 x))))

 (verify-guards factor-val-scatter-exponents1)

(defun factor-val-scatter-exponents (factor)
  (declare (xargs :guard t))
  (cond ((variablep factor)
	 (list 0 1 0))
	((constant-p factor)
	 (let ((val (unquote factor)))
	   (if (rationalp val)  ; Again OK.  No non-rationalp realp constants
	       (list 0 0 (abs val))
	     (list 0 0 1))))
	((eq (ffn-symb factor) 'UNARY-/)
	 (factor-val-scatter-exponents (arg1 factor)))
	((eq (ffn-symb factor) 'UNARY--)
	 (factor-val-scatter-exponents (arg1 factor)))
	((eq (ffn-symb factor) 'EXPT)
         (list (factor-val-scatter-exponents1 (arg2 factor)) 0 0))
	(t
	 (list 0 1 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factor-gather-exponents-info-entry (x)
  (declare (xargs :guard t))
  (list (factor-pattern-gather-exponents x)
        (factor-val-gather-exponents x)
        x))

(defun assoc-factor-gather-exponents (x info-list)
  (declare (xargs :guard (info-list-p info-list)))
  (cond ((endp info-list)
         nil)
        ((matching-factor-gather-exponents-patterns-p x (caar info-list))
         (car info-list))
        (t
         (assoc-factor-gather-exponents x (cdr info-list)))))

(defun factor-gather-exponents-intersect-info-lists (info-list1 info-list2)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-gather-exponents (caar info-list1) info-list2)))
      (cond ((not temp)
             (factor-gather-exponents-intersect-info-lists (cdr info-list1)
                                                           info-list2))
            ((val-< (cadr temp) (cadr (car info-list1)))
             (cons temp
                   (factor-gather-exponents-intersect-info-lists (cdr info-list1)
                                                                 info-list2)))
            (t
             (cons (car info-list1)
                   (factor-gather-exponents-intersect-info-lists (cdr info-list1)
                                                                 info-list2)))))))

(defun factor-gather-exponents-info-list (x)
  (declare (xargs :guard t
		  :verify-guards nil))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (let ((temp (factor-gather-exponents-info-list (arg2 x))))
           (if temp
               (factor-gather-exponents-intersect-info-lists
                temp
                (factor-gather-exponents-info-list (arg1 x)))
             nil)))
        ((eq (fn-symb x) 'BINARY-*)
         (cons (factor-gather-exponents-info-entry (arg1 x))
               (factor-gather-exponents-info-list (arg2 x))))
	((eq (fn-symb x) 'UNARY--)
	 (factor-gather-exponents-info-list (arg1 x)))
        (t
         (list (factor-gather-exponents-info-entry x)))))

(local
 (encapsulate
  ()

  (local
   (defthm temp-1
     (implies (and (info-list-p info-list)
		   (assoc-factor-gather-exponents x info-list))
	      (info-entry-p (assoc-factor-gather-exponents x info-list)))))

  (local
   (defthm temp-2
     (implies (and (info-list-p info-list-1)
		   (info-list-p info-list-2))
	      (info-list-p (factor-gather-exponents-intersect-info-lists
			    info-list-1
			    info-list-2)))))

  (local
   (defthm temp-3
     (rationalp (factor-val-gather-exponents1 x))))

  (local
   (defthm temp-4
     (good-val-triple-p (factor-val-gather-exponents x))))

  (defthm factor-gather-exponents-info-list-thm
    (info-list-p (factor-gather-exponents-info-list x)))

  ))

 (verify-guards factor-gather-exponents-info-list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun first-match-in-factor-gather-exponents-info-lists (info-list1 info-list2
								     mfc state)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))
		  :guard-hints (("Goal" :in-theory (disable good-val-triple-p
							    invert-match
							    val-<)))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-gather-exponents (car (car info-list1)) info-list2)))
      (if temp
	  (cond ((and ;; We want the ``smaller'' match
		      (val-< (cadr (car info-list1))
			     (cadr temp))
		      ;; prevent various odd loops
		      (stable-under-rewriting-products (invert-match
							(caddr (car info-list1)))
						       mfc state))
		 (list (cons 'x (invert-match (caddr (car info-list1))))))
		((stable-under-rewriting-products (invert-match
						   (caddr temp))
						  mfc state)
		 (list (cons 'x (invert-match (caddr temp)))))
		(t
		 (first-match-in-factor-gather-exponents-info-lists
		  (cdr info-list1) info-list2
		  mfc state)))
        (first-match-in-factor-gather-exponents-info-lists (cdr info-list1) info-list2
							   mfc state)))))

(defun find-matching-factors-gather-exponents (lhs rhs mfc state)
  (declare (xargs :guard t
		  :verify-guards nil))
  (let* ((info-list1 (factor-gather-exponents-info-list lhs))
         (info-list2 (if info-list1
                         (factor-gather-exponents-info-list rhs)
                       nil)))
    (if info-list2
	(first-match-in-factor-gather-exponents-info-lists info-list1
							   info-list2
							   mfc state)
      nil)))

(verify-guards find-matching-factors-gather-exponents)

(defun first-rational-match-in-factor-gather-exponents-info-lists
    (info-list1 info-list2 mfc state)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))
		  :guard-hints (("Goal" :in-theory (disable good-val-triple-p
							    invert-match
							    val-<)))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-gather-exponents (car (car info-list1)) info-list2)))
      (if (and temp
               (proveably-real/rational 'x `((x . ,(caddr temp))) mfc state))
          (cond ((and ;; We want the ``smaller'' match
		      (val-< (cadr (car info-list1))
			     (cadr temp))
		      ;; prevent various odd loops
		      (stable-under-rewriting-products (invert-match
							(caddr (car info-list1)))
						       mfc state))
		 (list (cons 'x (invert-match (caddr (car info-list1))))))
		((stable-under-rewriting-products (invert-match
						   (caddr temp))
						  mfc state)
		 (list (cons 'x (invert-match (caddr temp)))))
		(t
		 (first-rational-match-in-factor-gather-exponents-info-lists
		  (cdr info-list1) info-list2
		  mfc state)))
        (first-rational-match-in-factor-gather-exponents-info-lists (cdr info-list1) info-list2
                                                                    mfc state)))))

(defun find-rational-matching-factors-gather-exponents (lhs rhs mfc state)
  (declare (xargs :guard t
		  :verify-guards nil))
  (let* ((info-list1 (factor-gather-exponents-info-list lhs))
         (info-list2 (if info-list1
                         (factor-gather-exponents-info-list rhs)
                       nil)))
    (if info-list2
	(first-rational-match-in-factor-gather-exponents-info-lists info-list1
								    info-list2
								    mfc state)
      nil)))

 (verify-guards find-rational-matching-factors-gather-exponents)

(defun first-non-zero-rational-match-in-factor-gather-exponents-info-lists
    (info-list1 info-list2 mfc state)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))
		  :guard-hints (("Goal" :in-theory (disable good-val-triple-p
							    invert-match
							    val-<)))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-gather-exponents (car (car info-list1)) info-list2)))
      (if (and temp
               (proveably-non-zero-real/rational 'x `((x . ,(caddr temp))) mfc state))
          (cond ((and ;; We want the ``smaller'' match
		      (val-< (cadr (car info-list1))
			     (cadr temp))
		      ;; prevent various odd loops
		      (stable-under-rewriting-products (invert-match
							(caddr (car info-list1)))
						       mfc state))
		 (list (cons 'x (invert-match (caddr (car info-list1))))))
		((stable-under-rewriting-products (invert-match
						   (caddr temp))
						  mfc state)
		 (list (cons 'x (invert-match (caddr temp)))))
		(t
		 (first-non-zero-rational-match-in-factor-gather-exponents-info-lists
		  (cdr info-list1) info-list2
		  mfc state)))
        (first-non-zero-rational-match-in-factor-gather-exponents-info-lists (cdr info-list1) info-list2
                                                                    mfc state)))))

(defun find-non-zero-rational-matching-factors-gather-exponents (lhs rhs mfc state)
  (declare (xargs :guard t
		  :verify-guards nil))
  (let* ((info-list1 (factor-gather-exponents-info-list lhs))
         (info-list2 (if info-list1
                         (factor-gather-exponents-info-list rhs)
                       nil)))
    (if info-list2
	(first-non-zero-rational-match-in-factor-gather-exponents-info-lists info-list1
								    info-list2
								    mfc state)
      nil)))

 (verify-guards find-non-zero-rational-matching-factors-gather-exponents)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factor-scatter-exponents-info-entry (x)
  (declare (xargs :guard t))
  (list (factor-pattern-scatter-exponents x)
        (factor-val-scatter-exponents x)
        x))

(defun assoc-factor-scatter-exponents (x info-list)
  (declare (xargs :guard (info-list-p info-list)))
  (cond ((endp info-list)
         nil)
        ((matching-factor-scatter-exponents-patterns-p x (caar info-list))
         (car info-list))
        (t
         (assoc-factor-scatter-exponents x (cdr info-list)))))

;; I should speed this guard proof up.

(local
 (in-theory (disable MATCHING-FACTOR-SCATTER-EXPONENTS-PATTERNS-P)))

(defun factor-scatter-exponents-intersect-info-lists (info-list1 info-list2)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-scatter-exponents (caar info-list1) info-list2)))
      (cond ((not temp)
             (factor-scatter-exponents-intersect-info-lists (cdr info-list1)
                                                           info-list2))
            ((val-< (cadr temp) (cadr (car info-list1)))
             (cons temp
                   (factor-scatter-exponents-intersect-info-lists (cdr info-list1)
                                                                 info-list2)))
            (t
             (cons (car info-list1)
                   (factor-scatter-exponents-intersect-info-lists (cdr info-list1)
                                                                 info-list2)))))))

(defun factor-scatter-exponents-info-list (x)
  (declare (xargs :guard t
		  :verify-guards nil))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (let ((temp (factor-scatter-exponents-info-list (arg2 x))))
           (if temp
               (factor-scatter-exponents-intersect-info-lists
                temp
                (factor-scatter-exponents-info-list (arg1 x)))
             nil)))
	((eq (fn-symb x) 'UNARY--)
	 (factor-gather-exponents-info-list (arg1 x)))
        ((eq (fn-symb x) 'BINARY-*)
         (cons (factor-scatter-exponents-info-entry (arg1 x))
               (factor-scatter-exponents-info-list (arg2 x))))
        (t
         (list (factor-scatter-exponents-info-entry x)))))

;;; I should spped this up also.

(local
 (encapsulate
  ()

  (local
   (defthm temp-1
     (implies (and (info-list-p info-list)
		   (assoc-factor-scatter-exponents x info-list))
	      (info-entry-p (assoc-factor-scatter-exponents x info-list)))))

  (local
   (defthm temp-2
     (implies (and (info-list-p info-list-1)
		   (info-list-p info-list-2))
	      (info-list-p (factor-scatter-exponents-intersect-info-lists
			    info-list-1
			    info-list-2)))))

  (local
   (defthm temp-3
     (rationalp (factor-val-scatter-exponents1 x))))

  (local
   (defthm temp-4
     (good-val-triple-p (factor-val-scatter-exponents x))))

  (defthm factor-scatter-exponents-info-list-thm
    (info-list-p (factor-scatter-exponents-info-list x5)))

  ))

(verify-guards factor-scatter-exponents-info-list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Another one to speed up.

(defun first-match-in-factor-scatter-exponents-info-lists (info-list1 info-list2
								      mfc state)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))
		  :guard-hints (("Goal" :in-theory (disable good-val-triple-p
							    invert-match
							    val-<)))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-scatter-exponents (car (car info-list1)) info-list2)))
      (if temp
          (cond ((and ;; We want the ``smaller'' match
		      (val-< (cadr (car info-list1))
			     (cadr temp))
		      ;; prevent various odd loops
		      (stable-under-rewriting-products (invert-match
							(caddr (car info-list1)))
						       mfc state))
		 (list (cons 'x (invert-match (caddr (car info-list1))))))
		((stable-under-rewriting-products (invert-match
						   (caddr temp))
						  mfc state)
		 (list (cons 'x (invert-match (caddr temp)))))
		(t
		 (first-match-in-factor-scatter-exponents-info-lists
		  (cdr info-list1) info-list2
		  mfc state)))
        (first-match-in-factor-scatter-exponents-info-lists (cdr info-list1) info-list2
							    mfc state)))))

(defun find-matching-factors-scatter-exponents (lhs rhs mfc state)
  (declare (xargs :guard t
		  :verify-guards nil))
  (let* ((info-list1 (factor-scatter-exponents-info-list lhs))
         (info-list2 (if info-list1
                         (factor-scatter-exponents-info-list rhs)
                       nil)))
    (if info-list2
	(first-match-in-factor-scatter-exponents-info-lists info-list1
							    info-list2
							    mfc state)
      nil)))

(verify-guards find-matching-factors-scatter-exponents)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Speed this up also.

(defun first-rational-match-in-factor-scatter-exponents-info-lists
    (info-list1 info-list2 mfc state)
    (declare (xargs :guard (and (info-list-p info-list1)
                                (info-list-p info-list2))
		  :guard-hints (("Goal" :in-theory (disable good-val-triple-p
							    invert-match
							    val-<)))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-scatter-exponents (car (car info-list1)) info-list2)))
      (if (and temp
               (proveably-real/rational 'x `((x . ,(caddr temp))) mfc state))
          (cond ((and ;; We want the ``smaller'' match
		      (val-< (cadr (car info-list1))
			     (cadr temp))
		      ;; prevent various odd loops
		      (stable-under-rewriting-products (invert-match
							(caddr (car info-list1)))
						       mfc state))
		 (list (cons 'x (invert-match (caddr (car info-list1))))))
		((stable-under-rewriting-products (invert-match
						   (caddr temp))
						  mfc state)
		 (list (cons 'x (invert-match (caddr temp)))))
		(t
		 (first-rational-match-in-factor-scatter-exponents-info-lists
		  (cdr info-list1) info-list2
		  mfc state)))
        (first-rational-match-in-factor-scatter-exponents-info-lists (cdr info-list1) info-list2
                                                                     mfc state)))))

(defun find-rational-matching-factors-scatter-exponents (lhs rhs mfc state)
  (declare (xargs :guard t
		  :verify-guards nil))
  (let* ((info-list1 (factor-scatter-exponents-info-list lhs))
         (info-list2 (if info-list1
                         (factor-scatter-exponents-info-list rhs)
                       nil)))
    (if info-list2
	(first-rational-match-in-factor-scatter-exponents-info-lists info-list1
								     info-list2
								     mfc state)
      nil)))

(verify-guards find-rational-matching-factors-scatter-exponents)

(defun first-non-zero-rational-match-in-factor-scatter-exponents-info-lists
    (info-list1 info-list2 mfc state)
    (declare (xargs :guard (and (info-list-p info-list1)
                                (info-list-p info-list2))
		  :guard-hints (("Goal" :in-theory (disable good-val-triple-p
							    invert-match
							    val-<)))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-scatter-exponents (car (car info-list1)) info-list2)))
      (if (and temp
               (proveably-non-zero-real/rational 'x `((x . ,(caddr temp))) mfc state))
          (cond ((and ;; We want the ``smaller'' match
		      (val-< (cadr (car info-list1))
			     (cadr temp))
		      ;; prevent various odd loops
		      (stable-under-rewriting-products (invert-match
							(caddr (car info-list1)))
						       mfc state))
		 (list (cons 'x (invert-match (caddr (car info-list1))))))
		((stable-under-rewriting-products (invert-match
						   (caddr temp))
						  mfc state)
		 (list (cons 'x (invert-match (caddr temp)))))
		(t
		 (first-non-zero-rational-match-in-factor-scatter-exponents-info-lists
		  (cdr info-list1) info-list2
		  mfc state)))
        (first-non-zero-rational-match-in-factor-scatter-exponents-info-lists (cdr info-list1) info-list2
                                                                     mfc state)))))

(defun find-non-zero-rational-matching-factors-scatter-exponents (lhs rhs mfc state)
  (declare (xargs :guard t
		  :verify-guards nil))
  (let* ((info-list1 (factor-scatter-exponents-info-list lhs))
         (info-list2 (if info-list1
                         (factor-scatter-exponents-info-list rhs)
                       nil)))
    (if info-list2
	(first-non-zero-rational-match-in-factor-scatter-exponents-info-lists info-list1
								     info-list2
								     mfc state)
      nil)))

(verify-guards find-non-zero-rational-matching-factors-scatter-exponents)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun arith-factor-pattern-scatter-exponents (factor)
  (declare (xargs :guard t))
  (cond ((variablep factor)
         factor)
	((fquotep factor)
	 0)  ; Doesn't matter, because we do not match numbers.
        ((eq (ffn-symb factor) 'UNARY-/)
	 `(UNARY-/ ,(arith-factor-pattern-scatter-exponents (arg1 factor))))
        ((eq (ffn-symb factor) 'EXPT)
         (let ((base (factor-pattern-base (arg1 factor)))
               (exponent (arg2 factor)))
           (if (acl2-numberp base)
               (list 'EXPT-WITH-CONST-BASE base exponent)
             (if (quotep exponent)  ; Presumably too large to expand
		 base
	       `(EXPT ,base ,exponent)))))
        (t
         factor)))

(defun arith-matching-factor-scatter-exponents-patterns-p (pattern-1 pattern-2)
  (declare (xargs :guard t))
  (cond ((acl2-numberp pattern-1)
         nil)
	((eq (fn-symb pattern-1) 'EXPT-WITH-CONST-BASE)
	 (cond ((equal (arg1 pattern-1) 0)
		nil)
	       ((eq (fn-symb pattern-2) 'EXPT-WITH-CONST-BASE)
		(matching-exponents (arg2 pattern-1) (arg2 pattern-2)))
	       ((eq (fn-symb pattern-2) 'UNARY-/)
		(matching-exponents pattern-1 (arg1 pattern-2)))
	       (t
		nil)))
        ((eq (fn-symb pattern-1) 'EXPT)
	 (cond ((equal (arg1 pattern-1) 0)
		nil)
	       ((eq (fn-symb pattern-2) 'EXPT)
		(and (equal (arg1 pattern-1) (arg1 pattern-2))
		     (matching-exponents (arg2 pattern-1) (arg2 pattern-2))))
	       ((eq (fn-symb pattern-2) 'UNARY-/)
		(let ((pattern-2-arg1 (arg1 pattern-2)))
		  (and (eq (fn-symb pattern-2-arg1) 'EXPT)
		       (equal (arg1 pattern-1) (arg1 pattern-2-arg1))
		       (matching-exponents (arg2 pattern-1) (arg2 pattern-2-arg1)))))
	       (t
		nil)))
	((eq (fn-symb pattern-1) 'UNARY-/)
	 (equal (arg1 pattern-1) pattern-2))
	((eq (fn-symb pattern-2) 'UNARY-/)
	 (equal pattern-1 (arg1 pattern-2)))
	(t
	 nil)))

(defun arith-matching-factor-scatter-exponents-p (pattern factor)
  (declare (xargs :guard t))
  (let ((factor-pattern (arith-factor-pattern-scatter-exponents factor)))
    (arith-matching-factor-scatter-exponents-patterns-p pattern factor-pattern)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This is left over from some experiments with using factorization
;;; of constants to influence simplification.  The idea was to
;;; simplify:
#|
(equal (* 15 x) (* 21 y))
to
(equal (* 5 x) (* 7 y))
||#
;;; but I never got things working to my satisfaction.  This is probably
;;; worth revisiting some day --- perhaps in conjunction with
;;; simplify-ok-p to see what I can do when simplify-ok-p returns
;;; NIL.

;;; prime factorization
;;; used by factor pattern --- both gather and scatter

(defconst *first-1000-prime-numbers*
  ;; taken from http://primes.utm.edu/lists/small/1000.txt
  '(  2      3      5      7     11     13     17     19     23     29
     31     37     41     43     47     53     59     61     67     71
     73     79     83     89     97    101    103    107    109    113
    127    131    137    139    149    151    157    163    167    173
    179    181    191    193    197    199    211    223    227    229
    233    239    241    251    257    263    269    271    277    281
    283    293    307    311    313    317    331    337    347    349
    353    359    367    373    379    383    389    397    401    409
    419    421    431    433    439    443    449    457    461    463
    467    479    487    491    499    503    509    521    523    541
    547    557    563    569    571    577    587    593    599    601
    607    613    617    619    631    641    643    647    653    659
    661    673    677    683    691    701    709    719    727    733
    739    743    751    757    761    769    773    787    797    809
    811    821    823    827    829    839    853    857    859    863
    877    881    883    887    907    911    919    929    937    941
    947    953    967    971    977    983    991    997   1009   1013
   1019   1021   1031   1033   1039   1049   1051   1061   1063   1069
   1087   1091   1093   1097   1103   1109   1117   1123   1129   1151
   1153   1163   1171   1181   1187   1193   1201   1213   1217   1223
   1229   1231   1237   1249   1259   1277   1279   1283   1289   1291
   1297   1301   1303   1307   1319   1321   1327   1361   1367   1373
   1381   1399   1409   1423   1427   1429   1433   1439   1447   1451
   1453   1459   1471   1481   1483   1487   1489   1493   1499   1511
   1523   1531   1543   1549   1553   1559   1567   1571   1579   1583
   1597   1601   1607   1609   1613   1619   1621   1627   1637   1657
   1663   1667   1669   1693   1697   1699   1709   1721   1723   1733
   1741   1747   1753   1759   1777   1783   1787   1789   1801   1811
   1823   1831   1847   1861   1867   1871   1873   1877   1879   1889
   1901   1907   1913   1931   1933   1949   1951   1973   1979   1987
   1993   1997   1999   2003   2011   2017   2027   2029   2039   2053
   2063   2069   2081   2083   2087   2089   2099   2111   2113   2129
   2131   2137   2141   2143   2153   2161   2179   2203   2207   2213
   2221   2237   2239   2243   2251   2267   2269   2273   2281   2287
   2293   2297   2309   2311   2333   2339   2341   2347   2351   2357
   2371   2377   2381   2383   2389   2393   2399   2411   2417   2423
   2437   2441   2447   2459   2467   2473   2477   2503   2521   2531
   2539   2543   2549   2551   2557   2579   2591   2593   2609   2617
   2621   2633   2647   2657   2659   2663   2671   2677   2683   2687
   2689   2693   2699   2707   2711   2713   2719   2729   2731   2741
   2749   2753   2767   2777   2789   2791   2797   2801   2803   2819
   2833   2837   2843   2851   2857   2861   2879   2887   2897   2903
   2909   2917   2927   2939   2953   2957   2963   2969   2971   2999
   3001   3011   3019   3023   3037   3041   3049   3061   3067   3079
   3083   3089   3109   3119   3121   3137   3163   3167   3169   3181
   3187   3191   3203   3209   3217   3221   3229   3251   3253   3257
   3259   3271   3299   3301   3307   3313   3319   3323   3329   3331
   3343   3347   3359   3361   3371   3373   3389   3391   3407   3413
   3433   3449   3457   3461   3463   3467   3469   3491   3499   3511
   3517   3527   3529   3533   3539   3541   3547   3557   3559   3571
   3581   3583   3593   3607   3613   3617   3623   3631   3637   3643
   3659   3671   3673   3677   3691   3697   3701   3709   3719   3727
   3733   3739   3761   3767   3769   3779   3793   3797   3803   3821
   3823   3833   3847   3851   3853   3863   3877   3881   3889   3907
   3911   3917   3919   3923   3929   3931   3943   3947   3967   3989
   4001   4003   4007   4013   4019   4021   4027   4049   4051   4057
   4073   4079   4091   4093   4099   4111   4127   4129   4133   4139
   4153   4157   4159   4177   4201   4211   4217   4219   4229   4231
   4241   4243   4253   4259   4261   4271   4273   4283   4289   4297
   4327   4337   4339   4349   4357   4363   4373   4391   4397   4409
   4421   4423   4441   4447   4451   4457   4463   4481   4483   4493
   4507   4513   4517   4519   4523   4547   4549   4561   4567   4583
   4591   4597   4603   4621   4637   4639   4643   4649   4651   4657
   4663   4673   4679   4691   4703   4721   4723   4729   4733   4751
   4759   4783   4787   4789   4793   4799   4801   4813   4817   4831
   4861   4871   4877   4889   4903   4909   4919   4931   4933   4937
   4943   4951   4957   4967   4969   4973   4987   4993   4999   5003
   5009   5011   5021   5023   5039   5051   5059   5077   5081   5087
   5099   5101   5107   5113   5119   5147   5153   5167   5171   5179
   5189   5197   5209   5227   5231   5233   5237   5261   5273   5279
   5281   5297   5303   5309   5323   5333   5347   5351   5381   5387
   5393   5399   5407   5413   5417   5419   5431   5437   5441   5443
   5449   5471   5477   5479   5483   5501   5503   5507   5519   5521
   5527   5531   5557   5563   5569   5573   5581   5591   5623   5639
   5641   5647   5651   5653   5657   5659   5669   5683   5689   5693
   5701   5711   5717   5737   5741   5743   5749   5779   5783   5791
   5801   5807   5813   5821   5827   5839   5843   5849   5851   5857
   5861   5867   5869   5879   5881   5897   5903   5923   5927   5939
   5953   5981   5987   6007   6011   6029   6037   6043   6047   6053
   6067   6073   6079   6089   6091   6101   6113   6121   6131   6133
   6143   6151   6163   6173   6197   6199   6203   6211   6217   6221
   6229   6247   6257   6263   6269   6271   6277   6287   6299   6301
   6311   6317   6323   6329   6337   6343   6353   6359   6361   6367
   6373   6379   6389   6397   6421   6427   6449   6451   6469   6473
   6481   6491   6521   6529   6547   6551   6553   6563   6569   6571
   6577   6581   6599   6607   6619   6637   6653   6659   6661   6673
   6679   6689   6691   6701   6703   6709   6719   6733   6737   6761
   6763   6779   6781   6791   6793   6803   6823   6827   6829   6833
   6841   6857   6863   6869   6871   6883   6899   6907   6911   6917
   6947   6949   6959   6961   6967   6971   6977   6983   6991   6997
   7001   7013   7019   7027   7039   7043   7057   7069   7079   7103
   7109   7121   7127   7129   7151   7159   7177   7187   7193   7207
   7211   7213   7219   7229   7237   7243   7247   7253   7283   7297
   7307   7309   7321   7331   7333   7349   7351   7369   7393   7411
   7417   7433   7451   7457   7459   7477   7481   7487   7489   7499
   7507   7517   7523   7529   7537   7541   7547   7549   7559   7561
   7573   7577   7583   7589   7591   7603   7607   7621   7639   7643
   7649   7669   7673   7681   7687   7691   7699   7703   7717   7723
   7727   7741   7753   7757   7759   7789   7793   7817   7823   7829
   7841   7853   7867   7873   7877   7879   7883   7901   7907   7919))

(local
(in-theory (enable natp)))

(encapsulate
 ()

 (local
  (defthm foo-0
    (implies (and (not (zp x))
		  (real/rationalp y)
		  (<= 2 y))
	     (< (* x (/ y)) x))
    :hints (("Goal" :in-theory (enable NORMALIZE-<-/-TO-*-3-3)))))

 (local
  (in-theory (disable foo-0)))

 (defun prime-factors-2 (n i ith-prime factors)
   (declare (xargs :guard (and (integerp i)
			       (<= 0 i))
		   :measure (nfix (+ (- 1001 i) n))
		   :hints (("Subgoal 2" :use (:instance foo-0
							(x n)
							(y ith-prime))
			    :in-theory (disable <-*-X-Y-Y)))))
   (cond ((or (zp i)
	      (<= 1000 i)
	      (not (integerp n))
	      (not (integerp ith-prime))
	      (< ith-prime 2))
	  nil)
	 ((< n (* ith-prime ith-prime))
	  (cons n factors))
	 ((integerp (/ n ith-prime))
	  (prime-factors-2 (/ n ith-prime) i ith-prime
			   (cons ith-prime factors)))
	 ((<= 998 i)
	  (cons n factors))
	 (t
	  (prime-factors-2 n (+ 1 i)
			   (nth (+ 1 i) *first-1000-prime-numbers*)
			   factors))))
 )

(defun but-nth (list n)
  (declare (xargs :guard (integerp n)))
  (cond ((atom list)
	 nil)
	((<= n 0)
	 (cdr list))
	(t
	 (but-nth (cdr list) (+ -1 n)))))

(defun how-many-factors (x list ans)
  ;; [Jared]: Previously this was named "how-many."  I changed its name to
  ;; avoid a conflict with, e.g., sorting/convert-perm-to-how-many.lisp, so
  ;; that we can include both books in the XDOC manual, etc.
  (declare (xargs :guard (integerp ans)))
  ;; We assume that any instances of x appear at the head of list.
  (cond ((atom list)
	 ans)
	((equal (car list) x)
	 (how-many-factors x (cdr list) (+ 1 ans)))
	(t
	 ans)))

(encapsulate
 ()

 (local
  (defthm foo-1
    (implies (and (consp list)
		  (integerp ans))
	     (<= (+ 1 ans) (how-many-factors (car list) list ans)))))

 (local
  (defthm foo-2
    (implies (and (<= 0 count)
		  (consp factors))
	     (< (ACL2-COUNT (BUT-NTH FACTORS
				     count))
		(ACL2-COUNT FACTORS)))))

 (local
  (defthm foo-3
    (implies (integerp ans)
	     (integerp (how-many-factors x list ans)))
    :rule-classes :type-prescription))

 (defun condense-factors (factors ans)
   (declare (xargs :guard t))
   (if (atom factors)
       ans
     (let ((count (how-many-factors (car factors) factors 0)))
       (condense-factors (but-nth factors (+ -1 count))
			 (cons (cons (car factors) count)
			       ans)))))

 )

(defun prime-factors-1 (n i ith-prime factors)
  (declare (xargs :guard (and (integerp i)
			      (<= 0 i)
			      (integerp ith-prime))))
  (condense-factors (prime-factors-2 n i ith-prime factors)
		    nil))

(defun prime-factors (n)
  (declare (xargs :guard t))

  ;; We return a list of the prime factors of n.

  ;; There are some exceptions, however.  Negative numbers have -1 as
  ;; a prime factor, -1, 0, and 1 have themselves as their ony prime
  ;; factors.  Also, we do not check for prime factors larger than
  ;; 7919.  In affect, we assume that any integer not divisible by one
  ;; of the first 1000 primes is itself prime.

  ;; This last exception, however, itself has an exception.  We check
  ;; a table of factorizations containing factorizations for
  ;; (+ (expt 2 n) c), where 0 < n <= 64 and -3 <= c <= 3 on the
  ;; assumption that we will see these (at least for -1 <= c <= 1)
  ;; in proofs about hardware or bit-vectors.

  (cond ((not (integerp n))
	 nil)
	((equal n -1)
	 '((-1 . 1)))
	((equal n 0)
	 '((0 . 1)))
	((equal n 1)
	 `((1 . 1)))
	((< 0 n)
	 (prime-factors-1 n 0 2 nil))
	(t
	 (prime-factors-1 (- n) 0 2 '(-1)))))