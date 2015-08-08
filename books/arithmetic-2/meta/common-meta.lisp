; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; common-meta.lisp
;;;
;;;
;;; This book contains some of the work-horse functions that will
;;; be called by the meta-rules developed in the other books.
;;;
;;; Organization of file:
;;;
;;; 0. Brief Overview.
;;; 1. Background.
;;; 2. "Dummy Functions" and their lemmatta.
;;; 3. Pattern extraction and matching functions.
;;; 4. Tree manipulation functions.
;;; 5. Proofs of correctness.
;;; 6. Clean-up.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 0. Brief Overview.

; See integerp-meta.lisp for a general essay on meta functions.

; In this book, we develop the pieces common to two other books ---
; collect-terms-meta, and cancel-terms-meta.  These pieces fall
; into three categories:
; 1. "Dummy Functions" and their lemmatta.
; 2. Pattern extraction and matching functions.
; 3. Tree manipulation functions.
;
; The pattern extraction and matching functions are worth
; at least a brief inspection by all.  If one wishes to tinker with
; the functionality of collect-terms-meta or cancel-terms-meta,
; these functions are the place to start.  I have attempted to
; document them more fully than the rest of the book.
;
; The dummy functions and there lemmatta should be of no concern
; to the user.  The idea behind them is, however, useful for the
; implementor of meta rules and is discussed in the documentation
; in integerp-meta.lisp.
;
; Similarly, the tree manipulation functions should not be of
; interest to the user of these books.  The function new-term
; is the "main" or "workhorse" function
; exported from this book and is  discussed further in section 4.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 1. Background.

; We start with some simple utility type functions.

(in-package "ACL2")

(local (include-book "../pass1/top"))

(local
 (defthm hide-revealed
   (equal (hide x)
	  x)
   :hints (("Goal" :expand (hide x)))))

(defabbrev acl2-nump (x)
  (and (nvariablep x)
       (fquotep x)
       (acl2-numberp (cadr x))))

(defabbrev ratp (x)
  (and (nvariablep x)
       (fquotep x)
       (rationalp (cadr x))))

(defabbrev arg1 (x)
  (fargn x 1))

(defabbrev arg2 (x)
  (fargn x 2))
#|
(defabbrev unquote (x)
  (cadr x))
|#
(defun zfix (x)
  (if (and (acl2-numberp x)
	   (not (eql x 0)))
      x
    1))
#|
(defun fn-symb (x)
  (cond ((variablep x)
         nil)
        ((fquotep x)
         nil)
        (t
         (car x))))
|#
(defun package-witness ()
  t)

(defun intern-name (lst)
  (declare (xargs :mode :program))
  (acl2::intern-in-package-of-symbol (coerce (acl2::packn1 lst) 'string)
                                     'package-witness))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2. "Dummy Functions" and their lemmatta.

; We define a few "dummy functions" and simple rules about them.
; Our meta rules will rewrite terms so that these rules can fire, and
; do the real work.  I find this to be a handy separation of concerns.
; See the more detailed essay in integerp-meta.lisp.

; Note here that although there are a large number of rules about
; the dummy functions, they are all simple to write and prove.  Also
; the work done by them must be done somewhere.

; See collect-terms-meta.lisp and cancel-terms-meta.lisp for some
; pseudo-examples of the kinds of terms the meta rules will
; generate.

(defun un-hide-* (x y)
  (* x y))

(defun un-hide-+ (x y)
  (+ x y))

(defun collect-* (x y)
  (* x y))

(defun collect-+ (x y)
  (+ x y))


(defevaluator eva eva-list
  ((un-hide-+ x y)
   (un-hide-* x y)
   (collect-* x y)
   (collect-+ x y)
   (binary-* x y)
   (binary-+ x y)
   (unary-/ x)
   (unary-- x)
   (expt x y)
   (equal x y)
   (< x y)
   (if x y z)
   (rationalp x)
   #+:non-standard-analysis (realp x)
   (acl2-numberp x)
   (fix x)
   (rfix x)
   (not x)
   (hide x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2. "Dummy Functions" and their lemmatta, continued.

; See "A note on the use of 'HIDE:" below.

(defthm un-hide-plus
  (equal (un-hide-+ x (hide y))
	 (+ x y)))

(defthm collect-plus-0
  (implies (equal x x)
	   (equal (collect-+ (hide x) (hide y))
		  (+ x y))))

(defthm collect-plus-0a
  (implies (and (syntaxp (consp x))
                (syntaxp (equal (car x) 'quote))
                (syntaxp (consp y))
                (syntaxp (equal (car y) 'quote)))
  (equal (collect-+ (hide x) (hide y))
         (+ x y))))

(defthm collect-plus-1a
  (equal (collect-+ (hide x) (hide x))
	 (* 2 x)))

(defthm collect-plus-1b
  (equal (collect-+ (hide x) (hide (- x)))
	 0))

(defthm collect-plus-1c
  (equal (collect-+ (hide (- x)) (hide x))
	 0))

(defthm collect-plus-1d
  (equal (collect-+ (hide (- x)) (hide (- x)))
	 (* -2 x)))

(defthm collect-plus-2a
  (equal (collect-+ (hide x) (hide (* a x)))
	 (* (+ a 1) x)))

(defthm collect-plus-2b
  (equal (collect-+ (hide (* a x)) (hide x))
	 (* (+ a 1) x)))

(defthm collect-plus-2c
  (equal (collect-+ (hide (- x)) (hide (* a x)))
	 (* (- a 1) x)))

(defthm collect-plus-2d
  (equal (collect-+ (hide (* a x)) (hide (- x)))
	 (* (- a 1) x)))

(defthm collect-plus-3
  (equal (collect-+ (hide (* a x)) (hide (* b x)))
	 (* (+ a b) x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2. "Dummy Functions" and their lemmatta, continued.

(defthm un-hide-times
  (equal (un-hide-* x (hide y))
	 (* x y)))

(defthm collect-times-0
  (implies (equal x x)
	   (equal (collect-* (hide x) (hide y))
		  (* x y))))

(defthm collect-times-0a
  (equal (collect-* (hide x) (hide 0))
	 0))

(defthm collect-times-0b
  (equal (collect-* (hide 0) (hide x))
	 0))

(defthm collect-times-0c
  (implies (and (syntaxp (consp x))
                (syntaxp (equal (car x) 'quote))
                (syntaxp (consp y))
                (syntaxp (equal (car y) 'quote)))
  (equal (collect-* (hide x) (hide y))
         (* x y))))

(defthm collect-times-1a
  (equal (collect-* (hide x) (hide x))
	 (expt x 2)))

(defthm collect-times-1b
  (equal (collect-* (hide x) (hide (/ x)))
         (if (equal (fix x) 0)
             0
	   1)))

(defthm collect-times-1c
  (equal (collect-* (hide (/ x)) (hide x))
         (if (equal (fix x) 0)
             0
	   1)))

(defthm collect-times-1d
  (equal (collect-* (hide (/ x)) (hide (/ x)))
	 (expt x -2))
  :hints (("Subgoal 1" :expand ((expt x -2)))))

(defthm collect-times-2a
  (implies (integerp i)
	   (equal (collect-* (hide x) (hide (expt x i)))
		  (if (equal (fix x) 0)
		      0
		    (expt x (+ i 1))))))

(defthm collect-times-2b
  (implies (integerp i)
	   (equal (collect-* (hide (expt x i)) (hide x))
		  (if (equal (fix x) 0)
		      0
		    (expt x (+ i 1))))))

(defthm collect-times-2c
  (implies (integerp i)
	   (equal (collect-* (hide x) (hide (expt (/ x) i)))
		  (if (equal (fix x) 0)
		      0
		    (expt (/ x) (- i 1))))))

(defthm collect-times-2d
  (implies (integerp i)
	   (equal (collect-* (hide (expt (/ x) i)) (hide x))
		  (if (equal (fix x) 0)
		      0
		    (expt (/ x) (- i 1))))))

(defthm collect-times-2e
  (implies (integerp i)
	   (equal (collect-* (hide (/ x)) (hide (expt x i)))
		  (if (equal (fix x) 0)
		      0
		    (expt x (- i 1))))))

(defthm collect-times-2f
  (implies (integerp i)
	   (equal (collect-* (hide (expt x i)) (hide (/ x)))
		  (if (equal (fix x) 0)
		      0
		    (expt x (- i 1))))))

(defthm collect-times-2g
  (implies (integerp i)
	   (equal (collect-* (hide (/ x)) (hide (expt (/ x) i)))
		  (if (equal (fix x) 0)
		      0
		    (expt (/ x) (+ i 1))))))

(defthm collect-times-2h
  (implies (integerp i)
	   (equal (collect-* (hide (expt (/ x) i)) (hide (/ x)))
		  (if (equal (fix x) 0)
		      0
		    (expt (/ x) (+ i 1))))))

(defthm collect-times-3a
  (implies (and (integerp i)
		(integerp j))
	   (equal (collect-* (hide (expt x i)) (hide (expt x j)))
		  (if (and (equal (fix x) 0)
			   (not (equal i 0))
			   (not (equal j 0)))
		      0
		    (expt x (+ i j))))))

(defthm collect-times-3b
  (implies (and (integerp i)
		(integerp j))
	   (equal (collect-* (hide (expt (/ x) i)) (hide (expt x j)))
		  (if (and (equal (fix x) 0)
			   (not (equal i 0))
			   (not (equal j 0)))
		      0
		    (expt x (- j i))))))

(defthm collect-times-3c
  (implies (and (integerp i)
		(integerp j))
	   (equal (collect-* (hide (expt x i)) (hide (expt (/ x) j)))
		  (if (and (equal (fix x) 0)
			   (not (equal i 0))
			   (not (equal j 0)))
		      0
		    (expt x (- i j))))))

(defthm collect-times-3d
  (implies (and (integerp i)
		(integerp j))
	   (equal (collect-* (hide (expt (/ x) i)) (hide (expt (/ x) j)))
		  (if (and (equal (fix x) 0)
			   (not (equal i 0))
			   (not (equal j 0)))
		      0
		    (expt (/ x) (+ i j))))))

(defthm collect-times-4
  (implies (integerp n)
           (equal (collect-* (hide (expt x n)) (hide (expt y n)))
                  (expt (* x y) n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 3. Pattern extraction and matching functions.

; The functions addend-pattern, factor-pattern-gather-exponents, and
; factor-pattern-scatter-exponents extract the "important" part of
; an addend/factor.  This pattern will be compared, via
; pattern-matchp, with the corresponding pattern from another
; addend/factor to determine if they match.  If they do match,
; we consider the two original addends/factors to be "like"
; each other.

(defun addend-pattern (addend)

; Note that we do not want to match on zero.

  (cond ((variablep addend)
	 addend)
	((fquotep addend)
	 (if (equal addend ''0)
	     nil   ; We do not want to match on zero.
	   (unquote addend)))
	((eq (ffn-symb addend) 'UNARY--)
	 (addend-pattern (arg1 addend)))
	((and (eq (ffn-symb addend) 'BINARY-*)
	      (acl2-nump (arg1 addend)))
	 (addend-pattern (arg2 addend)))
	(t
	 addend)))

(defun factor-pattern-gather-exponents (factor)

; We only consider the base of an exponential when determining
; a match.  We handle quotep's carefully.  We want 2 to match
; with (expt 1/2 n) and 3, but not with (expt 3 n).  We
; also want (expt 2 n) to match with (expt 3 n) and
; (expt 2 (* -1/2 n)) but not with (expt 3 i).  See pattern-matchp.

; Pseudo-examples:
; x ===> x
; (* 3 x (foo y)) ===> (* 3 x (foo y))
; 2 ===> 2
; 2/3 ===> 3/2
; (expt x i) ===> x
; (expt 1/2 i) ===> (:mark1 2)

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
		 (t
		  c))))
	((eq (ffn-symb factor) 'UNARY-/)
	 (factor-pattern-gather-exponents (arg1 factor)))
	((eq (ffn-symb factor) 'EXPT)
	 (let ((base (arg1 factor))
               (exponent (arg2 factor)))
	   (cond ((quotep base)
		  (let ((c (unquote base)))
		    (cond ((eql c 0)
			   nil)   ; We do not want to match on this.
			  ((rationalp c)
			   (if (< (abs c) 1)
			       (list :mark1 (/ c) exponent)
			     (list :mark1 c exponent)))
			  (t
			   (list :mark1 c exponent)))))
		 ((member-eq (fn-symb base) '(UNARY-- UNARY-/))
		  (factor-pattern-gather-exponents (arg1 base)))
		 (t
		  base))))
	(t
	 factor)))

(defun factor-pattern-exponent2 (addend weight)
  (let ((weight (zfix weight)))
    (if (and (eq (fn-symb addend) 'BINARY-*)
	     (quotep (arg1 addend)))
	(if (eql (unquote (arg1 addend)) weight)
	    (arg2 addend)
	  `(BINARY-* ,(kwote (/ (zfix (unquote (arg1 addend)))
				weight))
		     ,(arg2 addend)))
      `(BINARY-* ,(kwote (/ weight)) ,addend))))

(defun factor-pattern-exponent1 (exponent weight)
  (if (eq (fn-symb exponent) 'BINARY-+)
      `(BINARY-+ ,(factor-pattern-exponent2 (arg1 exponent) weight)
		 ,(factor-pattern-exponent1 (arg2 exponent) weight))
    (factor-pattern-exponent2 exponent weight)))

(defun factor-pattern-exponent (exponent)

; We return two values --- a re-normalized
; exponent with a leading coefficient of 1, and the original
; leading cofficient.

; Pseudo-examples:
; x  ===> x  1
; (* x (foo y)) ===> (* x (foo y))  1
; (* 3 x (foo y)) ==> (* x (foo y))  3

  (cond ((or (variablep exponent)
             (fquotep exponent))
         (mv 1 exponent))
        ((eq (ffn-symb exponent) 'BINARY-*)
         (if (quotep (arg1 exponent))
             (mv (arg1 exponent) (arg2 exponent))
           (mv 1 exponent)))
        ((eq (ffn-symb exponent) 'BINARY-+)
         (if (and (eq (fn-symb (arg1 exponent)) 'BINARY-*)
                  (acl2-nump (arg1 (arg1 exponent)))) ; ratp?
             (let ((weight (unquote (arg1 (arg1 exponent)))))
               (mv weight (factor-pattern-exponent1 exponent weight)))
           (mv 1 exponent)))
        (t
         (mv 1 exponent))))

(defun factor-pattern-scatter-exponents (factor)

; This function is similar to factor-pattern-gather-exponents with the
; added twist that we consider exponents also.  Here, 2 will match
; 3 but not (expt 2 n).  Also, (expt 2 n) will match
; (expt 1/2 (* 3 n)) but not (expt 3 n).

; Pseudo-examples:
; x ===> x
; (* 3 x (foo y)) ===> (* 3 x (foo y))
; 2 ===> 2
; 2/3 ===> 3/2
; (expt x 3) ===> x
; (expt x i) ===> (expt x i)
; (expt x (* 3 i)) ===> (expt x i)
; (expt 1/2 i) ===> (:mark2 2 1 i)
; (expt 1/2 (* 3 i)) ===> (:mark2 2 3 i)

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
		 (t
		  c))))
	((eq (ffn-symb factor) 'UNARY-/)
	 (factor-pattern-scatter-exponents (arg1 factor)))
	((eq (ffn-symb factor) 'EXPT)
	 (let ((base (cond ((quotep (arg1 factor))
			    (unquote factor))
			   ((member-eq (fn-symb (arg1 factor))
				       '(UNARY-- UNARY-/))
			    (arg1 (arg1 factor)))
			   (t
			    (arg1 factor))))
	       (exponent (arg2 factor)))
	   (if (acl2-numberp base)
	       (cond ((variablep exponent)
		      `(:mark2 ,base 1 ,exponent))
		     ((fquotep exponent)  ; This should not happen.
		      `(:mark2 ,base 1 ,exponent))
		     ((eq (ffn-symb exponent) 'BINARY-*)
		      (if (quotep (arg1 exponent))
			  `(:mark2 ,base
				   ,(unquote (arg1 exponent))
				   ,(arg2 exponent))
			`(:mark2 ,base 1 ,(arg2 exponent))))
		     ((eq (ffn-symb exponent) 'BINARY-+)
		      (mv-let (weight new-exponent)
			      (factor-pattern-exponent exponent)
			      `(:mark2 ,base ,weight ,new-exponent)))
		     (t
		      `(:mark2 ,base 1 ,exponent)))
	     (cond ((variablep exponent)
		    `(EXPT ,base ,exponent))
		   ((fquotep exponent)
		    base)
		   ((eq (ffn-symb exponent) 'BINARY-*)
		    (if (quotep (arg1 exponent))
			`(EXPT ,base ,(arg2 exponent))
		      factor))
		   ((eq (ffn-symb exponent) 'BINARY-+)
		    (mv-let (weight new-exponent)
			    (factor-pattern-exponent exponent)
			    (declare (ignore weight))
			    `(EXPT ,base ,new-exponent)))
		   (t
		    `(EXPT ,base ,exponent))))))
	(t
	 factor)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 3. Pattern extraction and matching functions, continued.

(defun pattern-matchp (x y)

; We test whether the patterns extracted via addend-pattern,
; factor-pattern-gather-exponents, or factor-pattern-scatter-exponents
; ``match''.

  (cond ((or (eq x nil)
	     (eq y nil))
	 nil)
	((or (eq x t)
	     (eq y t))
	 t)
        ((or (eql x 0)
             (eql y 0))
         (not (and (eql x 0)
                   (eql y 0))))  ; Prevent loops (should not happen)
	((acl2-numberp x)
	 (or (acl2-numberp y)
	     (and (consp y)
		  (eq (car y) :mark1)
		  (equal (cadr y) x))))
	((and (consp x)
	      (eq (car x) :mark1))  ; factor-pattern-gather-exponents
	 (or (equal y (cadr x))
	     (and (consp y)
		  (eq (car y) :mark)
		  (or (equal (cadr y) (cadr x))  ; same base
                      (equal (caddr y) (caddr x))))))  ; same exponent
	((and (consp x)
	      (eq (car x) :mark2))  ; factor-pattern-scatter-exponents
	 (and (consp y)
	      (eq (car y) :mark2)
	      (equal (cadr x) (cadr y))  ; same base
	      (equal (cadddr x) (cadddr y))))  ; same exponent
	(t
	 (equal x y))))

(local
 (in-theory (disable pattern-matchp)))

(defun assoc-pattern-matchp (key alist)
  (cond ((endp alist)
	 nil)
	((pattern-matchp key (caar alist))
	 (car alist))
	(t
	 (assoc-pattern-matchp key (cdr alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 3. Pattern extraction and matching functions, continued.

; When canceling like terms, we will want to be able to pick one
; of them for cancelation.  Pseudo-example:  from
; (< (+ a b (* 2 c))
;    (+ e f (* 117 c)))
; we would want to cancel the (* 2 c), rather than the (* 117 c).
; These functions generate values which we can then compare.
; See cancel-terms-meta.lisp.

(defun fix-val (x)
  (let ((temp (rfix (unquote x))))
    (if (eql temp 0)
	0
      (/ temp))))

(defun addend-val (addend)
  (cond ((variablep addend)
	 1)
	((fquotep addend)
	 (fix-val addend))
	((eq (ffn-symb addend) 'UNARY--)
	 -1)
	((and (eq (ffn-symb addend) 'BINARY-*)
	      (quotep (arg1 addend)))
	 (fix-val (arg1 addend)))
	(t
	 1)))

(defun factor-val1 (exponent)
  (cond ((variablep exponent)
	 1)
	((fquotep exponent)
	 (fix-val exponent))
	((eq (ffn-symb exponent) 'BINARY-*)
	 (if (quotep (arg1 exponent))
	     (fix-val (arg1 exponent))
	   1))
	((eq (ffn-symb exponent) 'BINARY-+)
	 (+ (factor-val1 (arg1 exponent))
	    (factor-val1 (arg2 exponent))))
	(t
	 1)))

(defun factor-val (factor)
  (cond ((variablep factor)
	 1)
	((fquotep factor)
	 (if (or (equal factor ''0)   ;; Prevent looping with cancellation
		 (equal factor ''1))
	     0
	   1))
	((eq (ffn-symb factor) 'UNARY-/)
	 -1)
	((eq (ffn-symb factor) 'EXPT)
	 (factor-val1 (arg2 factor)))
	(t
	 1)))

(defun use-firstp (val1 val2 bin-op)
  (declare (ignore bin-op))
  (cond ((eql (abs val1) (abs val2))
         (< val1 0))
        (t
         (< (abs val2) (abs val1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 3. Pattern extraction and matching functions, continued.

; We implement a scrap of higher order lisp.  We want to be able
; to pass these function(-names) around.

(defun my-apply-1 (fun arg)
  (case fun
    (addend-pattern
     (addend-pattern arg))
    (factor-pattern-gather-exponents
     (factor-pattern-gather-exponents arg))
    (factor-pattern-scatter-exponents
     (factor-pattern-scatter-exponents arg))
    (addend-val
     (addend-val arg))
    (factor-val
     (factor-val arg))))

(local (in-theory (disable my-apply-1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 4. Tree manipulation functions.

; A note on the use of 'HIDE:

; When a meta rule returns a term,
; the entire term is given to ACL2's rewriter.  In the event that
; a large or complicated subterm is re-used verbatim from the origial
; term, this can be an expensive waste of time.  We, therefore,
; wrap the subterms in 'HIDE and "unhide" them using our rewrite
; rules above.

; While this method works, it seems to me to indicate a lack in our
; current design for meta rules.  A better alternative would be to
; mimic a regular rewrite rule more fully, and to return a new term
; and a substitution-alist.

(defun pull-piece-out (term pattern pattern-fun bin-op)

; Term is a bin-op tree, we recur through the tree
; looking for a sub-term whose pattern (as determined by pattern-fun)
; will match pattern.  If we succeed, we extract the matching piece
; from term.  We return three values: a flag, the extracted piece,
; and the remainder of term.

; Pseudo-example:
; (pull-piece-put (BINARY-+ (- a) (BINARY-+ (* 2 b) (BINARY-+ d (* b c))))
;                 b
;                 addend-pattern
;                 BINARY-+)
; ===>
; (t (* 2 b) (BINARY-+ (- a) (BINARY-+ d (* b c))))

  (cond ((or (variablep term)
	     (fquotep term))
	 (mv nil nil term))   ; For termination.
	((pattern-matchp (my-apply-1 pattern-fun (arg1 term))
			 pattern)
	 (mv t (arg1 term) (arg2 term)))
	((eq (fn-symb (arg2 term)) bin-op)
	 (mv-let (flag piece rest)
	   (pull-piece-out (arg2 term) pattern pattern-fun bin-op)
	   (if flag
	       (mv t
		   piece
		   `(,bin-op ,(arg1 term) ,rest))
	     (mv nil nil term))))
	((pattern-matchp (my-apply-1 pattern-fun (arg2 term))
			 pattern)
	 (mv t (arg2 term) (arg1 term)))
	(t
	 (mv nil nil term))))

(defun new-term1 (term new-piece pattern pattern-fun bin-op)

; We return two values; the first is a boolean flag indicating
; whether we did anything useful, and the second is, in essence,
; `(,bin-op ,new-piece ,term).

; Pseudo-example:
; (new-term1 (BINARY-+ (- a) (BINARY-+ (* 2 b) (BINARY-+ d (* b c))))
;            (* 3/2 b)
;            b
;            addend-pattern
;            BINARY-+)
; ===>
; (t (UN-HIDE-+ (COLLECT-+ (HIDE (* 3/2 b))
;                          (HIDE (* 2 b)))
;               (HIDE (BINARY-+ (- a) (BINARY-+ d (* b c)))))
; Recall that UN-HIDE-+ and COLLECT-+ are defined to be BINARY-+,
; and that HIDE is the identity.

  (if (member-eq bin-op '(BINARY-+ BINARY-*))
      (cond ((eq (fn-symb term) bin-op)
	     (mv-let (flag piece rest)
	       (pull-piece-out term pattern pattern-fun bin-op)
	       (if flag
		   (case bin-op
		     ((BINARY-+)
		      (mv t `(UN-HIDE-+ (COLLECT-+ (HIDE ,new-piece)
						   (HIDE ,piece))
					(HIDE ,rest))))
		     ((BINARY-*)
		      (mv t `(UN-HIDE-* (COLLECT-* (HIDE ,new-piece)
						   (HIDE ,piece))
					(HIDE ,rest))))
		     (otherwise
		      (mv t `(,bin-op ,new-piece ,term))))
		 (mv nil `(,bin-op ,new-piece ,term)))))
	    ((pattern-matchp (my-apply-1 pattern-fun term)
			     pattern)
	     (if (eq bin-op 'BINARY-+)
		 (mv t `(COLLECT-+ (HIDE ,new-piece) (HIDE ,term)))
	       (mv t `(COLLECT-* (HIDE ,new-piece) (HIDE ,term)))))
	    (t
	     (mv nil `(,bin-op ,new-piece ,term))))
    (mv nil `(,bin-op ,new-piece ,term))))

(defun new-term (term new-piece pattern pattern-fun bin-op)

; Term and new-piece are an acl2 terms, pattern is a pattern
; as extracted by pattern-fun (presently one of addend-pattern,
; factor-pattern-gather-exponents, or factor-pattern-scatter-exponents)
; and bin-op is one of 'BINARY-* or 'BINARY-+.
; We return two values; the first is a boolean flag indicating
; whether we did anything useful, and the second is, in essence,
; `(,bin-op ,new-piece ,term).

  (if (and (eq bin-op 'BINARY-*)
	   (eq (fn-symb term) 'BINARY-+))
      (mv-let (flag1 new-term1)
	(new-term1 (arg1 term) new-piece
		   pattern pattern-fun bin-op)
	(mv-let (flag2 new-term2)
	  (new-term (arg2 term) new-piece
		    pattern pattern-fun bin-op)
	  (mv (or flag1 flag2)   ; and/or?
	      `(BINARY-+ ,new-term1 ,new-term2))))
    (new-term1 term new-piece
	       pattern pattern-fun bin-op)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 5. Proofs of correctness.

; Note how easy these are.

(encapsulate
 ()

 (local
  (defun pull-piece-up (term pattern pattern-fun bin-op)
    (if (and (member-eq bin-op '(BINARY-+ BINARY-*))
	     (eq (fn-symb term) bin-op))
	(mv-let (flag piece new-term)
		(pull-piece-out term pattern pattern-fun bin-op)
		(if flag
		    `(,bin-op ,piece ,new-term)
		  term))
      term)))

 (local
  (defthm pull-piece-up-correct
    (equal (eva (pull-piece-up term pattern pattern-fun bin-op) a)
	   (eva term a))
    :hints (("Subgoal 2'" :induct t)
	    ("Subgoal 1'" :induct t))
    :rule-classes nil))

 (local
  (defthm new-term1-correct
    (mv-let (flag new-term)
      (new-term1 term new-piece pattern pattern-fun bin-op)
      (declare (ignore flag))
      (equal (eva new-term a)
	     (eva `(,bin-op ,new-piece ,term) a)))
    :hints (("Goal" :in-theory (disable pull-piece-out))
;fcd/Satriani v3.7 Moore - used to be Subgoals 6'' and 5''
	    ("Subgoal 7''" :use ((:instance pull-piece-up-correct
					    (bin-op 'BINARY-+))))
	    ("Subgoal 3''" :use ((:instance pull-piece-up-correct
					     (bin-op 'BINARY-*)))))))

 ; This is the only theorem we export.

 (defthm new-term-correct
   (mv-let (flag new-term)
      (new-term term new-piece pattern pattern-fun bin-op)
      (declare (ignore flag))
      (equal (eva new-term a)
	     (eva `(,bin-op ,new-piece ,term) a)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
	           :in-theory (disable new-term1))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 6. Clean-up.

(in-theory (disable factor-pattern-exponent2
		    factor-pattern-exponent1
		    factor-pattern-exponent
		    factor-val1))

(in-theory (disable addend-pattern
		    factor-pattern-gather-exponents
		    factor-pattern-scatter-exponents
		    fix-val addend-val factor-val))

(in-theory (disable pattern-matchp))

(in-theory (disable assoc-pattern-matchp))

(in-theory (disable my-apply-1))

(in-theory (disable pull-piece-out new-term1 new-term))

(in-theory (disable un-hide-times
		    collect-times-0
		    collect-times-0a collect-times-0b
		    collect-times-1a collect-times-1b
		    collect-times-1c collect-times-1d
		    collect-times-2a collect-times-2b
		    collect-times-2c collect-times-2d
		    collect-times-2e collect-times-2f
		    collect-times-2g collect-times-2h
		    collect-times-3a collect-times-3b
		    collect-times-3c collect-times-3d
		    collect-times-4))

(in-theory (disable un-hide-plus
		    collect-plus-0
		    collect-plus-1a collect-plus-1b
		    collect-plus-1c collect-plus-1d
		    collect-plus-2a collect-plus-2b
		    collect-plus-2c collect-plus-2d
		    collect-plus-3))

