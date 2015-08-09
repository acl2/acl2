; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; cancel-terms-meta.lisp
;;;
;;; This book contains the code for constructing some meta-rules
;;; which will 1. cancel "like" sub-expressions from both sides
;;; of an (in)equality. 2. move "negative" sub-expressions to
;;; the other side of an (in)equality.  The meta rules massage
;;; terms into forms such that the rules for collect-+ and
;;; friends (in common-meta.lisp) can do the real work.
;;;
;;; See top.lisp for a description of the theories exprted from
;;; this book and collect-terms-meta.
;;;
;;; Pseudo-examples:
;;;
;;; cancel-addends-equal:
;;; (equal (+ (* 2 a) c (- e))
;;;        (+ b (* 3 c)))
;;; ===>
;;; (equal (un-hide-+ (collect-+ (hide c) (hide (- c)))
;;;                   (hide (+ (* 2 a) (- e))))
;;;        (un-hide-+ (collect-+ (hide (* 3 c)) (hide (- c)))
;;;                   (hide b)))
;;;
;;; prefer-positive-factors-gather-exponents-<:
;;; (< (* y (expt x n))
;;;    (expt z (* -2 c)))
;;; ===>
;;; (if (real/rationalp (expt z (* 2 c)))
;;;     (if (not (equal (expt z (* 2 c)) 0))
;;;         (if (< 0 (expt z (* 2 c)))
;;;             (< (* (expt z (* 2 c))
;;;                   (* y (expt x n)))
;;;                (collect-* (hide (expt z (* -2 c)))
;;;                           (hide (expt z (* 2 c)))))
;;;           (< (collect-* (hide (expt z (* -2 c)))
;;;                         (hide (expt z (* 2 c))))
;;;              (* (expt z (* 2 c))
;;;                 (* y (expt x n)))))
;;;       (< (* y (expt x n))
;;;          (expt 0 (* -2 c))))
;;;   (< (* y (expt x n))
;;;      (expt z (* -2 c))))
;;;
;;; Organization of Book:
;;;
;;; 1. Background.
;;; 2. Info-list.
;;; 3. First-match/First-negative.
;;; 4. Misc.
;;; 5. Making the meta-functions and -rules.
;;; 6. Cleanup.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 1. Background.

(in-package "ACL2")

(include-book "common-meta")

(local (include-book "../pass1/top"))

(local (include-book "cancel-terms-helper"))

(table acl2-defaults-table :state-ok t)

(local
 (defthm hide-revealed
   (equal (hide x)
	  x)
   :hints (("Goal" :expand (hide x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 2. Info-list.

; We create a small data-base which we can scan through to find
; candidate sub-expressions to operate on.  An info-list is a
; list of entries, each of the form (pattern value . term).
; Pattern is the pattern extracted from term, and value is its
; associated numeric value.  This last will be used to decide
; between two candidates when such a decision is needed.

; We define some constructors/destructors for info-list entries.

(defun info-list-entry (piece pattern-fun val-fun)
  (cons (my-apply-1 pattern-fun piece)
	(cons (rfix (my-apply-1 val-fun piece))
	      piece)))

(defabbrev pattern (info-list-entry)
  (car info-list-entry))

(defabbrev val (info-list-entry)
  (cadr info-list-entry))

(defabbrev piece (info-list-entry)
  (cddr info-list-entry))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here is how we create an info-list.
; (pattern value . term)

(defun info-list-intersect (info-list1 info-list2 bin-op)
  (declare (xargs :hints (("Goal" :in-theory (enable ASSOC-PATTERN-MATCHP)))))
  (if (atom info-list1)
      nil
    (let ((temp (assoc-pattern-matchp (pattern (first info-list1))
				      info-list2)))
      (if temp
	  (cons (if (use-firstp (val (first info-list1)) (val temp) bin-op)
		    (first info-list1)
		  temp)
		(info-list-intersect (rest info-list1) info-list2 bin-op))
	(info-list-intersect (rest info-list1) info-list2 bin-op)))))

(defun info-list1 (term pattern-fun val-fun bin-op)
; (pattern . (val . piece))
  (if (and (consp term)
	   (eq (ffn-symb term) bin-op))
      (cons (info-list-entry (arg1 term) pattern-fun val-fun)
	    (info-list1 (arg2 term)
			      pattern-fun val-fun bin-op))
    (list (info-list-entry term pattern-fun val-fun))))

(defun info-list (term pattern-fun val-fun bin-op)
  (cond ;((equal term ''0)
	; '((t 0 . '0)))  ; Fix me.  !!!???!!!
	((and (eq bin-op 'BINARY-*)
	      (eq (fn-symb term) 'BINARY-+))
	 (let ((temp (info-list (arg2 term) pattern-fun val-fun bin-op)))
	   (if temp
	       (info-list-intersect (info-list1 (arg1 term)
						pattern-fun val-fun bin-op)
				    temp
				    bin-op)
	     nil)))
	(t
	 (info-list1 term pattern-fun val-fun bin-op))))

(local (in-theory (disable info-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proveably-rational (x mfc state)
  (equal (mfc-rw `(#-:non-standard-analysis
                   RATIONALP
                   #+:non-standard-analysis
                   REALP
                   ,x)
		 t t mfc state)
	 *t*))

;; [Jared] 2014-10 commented out and removed its only use (in my-apply-2) to
;; avoid name conflict with std/basic.
;;
;; (defun true (x mfc state)
;;   (declare (ignore x mfc state))
;;   t)

(defun my-apply-2 (fun arg mfc state)
  (case fun
    (proveably-rational
     (proveably-rational arg mfc state))
    (true
     ;; [Jared] 2014-10 was formerly (true arg mfc state)
     t)))

(local
 (in-theory (disable my-apply-2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 3. First-match/First-negative.

(defun cancelling-piece (piece bin-op)

; We return the inverse of piece as determined by bin-op.
; This is currently a hack, and needs to be re-done properly.
; It may not be entirely correct.

  (if (eq bin-op 'BINARY-*)
      (if (eq (fn-symb piece) 'EXPT)
          `(EXPT (UNARY-/ ,(fargn piece 1))
                          ,(fargn piece 2))
        `(UNARY-/ ,piece))
    (cond ((eq (fn-symb piece) 'UNARY--)
           (fargn piece 1))
          ((and (eq (fn-symb piece) 'BINARY-*)
                (quotep (fargn piece 1)))
           `(BINARY-* ,(kwote (- (unquote (fargn piece 1))))
                      ,(fargn piece 2)))
          (t
           `(UNARY-- ,piece)))))

(local
 (in-theory (disable cancelling-piece)))

(defun strip-cancelling-piece (cancelling-piece)

; This is the approximate inverse of cancelling-piece.

  (if (member-eq (fn-symb cancelling-piece)
		 '(UNARY-- UNARY-/ EXPT))
      (strip-cancelling-piece (arg1 cancelling-piece))
    cancelling-piece))

(defun first-match (info-list1 info-list2
			       criterion
			       bin-op mfc state)

; Info-list1 and Info-list2 are the info-lists derived from the
; two sides of an (in)equality.  We scan through info-list1, trying
; to find a match in info-list2 which satisfies criterion.  This is
; one of the main functions which control the operation of the various
; cancel-* meta-functions and -rules.

  (if (endp info-list1)
      (mv nil nil nil)
    (let* ((temp (assoc-pattern-matchp (pattern (first info-list1))
				       info-list2))
	   (use-first (if temp
                           (use-firstp (val (first info-list1))
                                            (val temp)
                                            bin-op)
                         nil))
	   (piece (if temp
		      (if use-first
			  (piece (first info-list1))
			(piece temp))
		    nil))
	   (pattern (if temp
		      (if use-first
			  (pattern (first info-list1))
			(pattern temp))
		    nil))
	   (cancelling-piece (if temp
				 (cancelling-piece piece bin-op)
			       nil)))
       (if (and temp
		(my-apply-2 criterion cancelling-piece
			    mfc state))
	   (mv t
	       pattern
	       cancelling-piece)
	 (first-match (rest info-list1) info-list2
		      criterion
		      bin-op mfc state)))))

(local
 (in-theory (disable first-match)))

(defun first-negative2 (term pattern-fun val-fun criterion
			     bin-op mfc state)
  (let ((val (rfix (my-apply-1 val-fun term))))
    (if (and (< val 0)
	     (my-apply-2 criterion term
			 mfc state))
	(mv t
	    (my-apply-1 pattern-fun term)
	    (cancelling-piece term bin-op))
      (mv nil nil nil))))

(defun first-negative1 (term pattern-fun val-fun criterion
			     bin-op mfc state)
  (declare (xargs :hints (("Goal" :in-theory (disable FIRST-NEGATIVE2)))))
  (if (and (consp term)
	   (eq (fn-symb term) bin-op))
      (mv-let (flag to-match cancelling-piece)
	(first-negative2 (arg1 term) pattern-fun val-fun criterion
			 bin-op mfc state)
	(if flag
	    (mv t to-match cancelling-piece)
	  (first-negative1 (arg2 term) pattern-fun val-fun criterion
		     bin-op mfc state)))
    (first-negative2 term pattern-fun val-fun criterion
			    bin-op mfc state)))

(defun first-negative (term pattern-fun val-fun criterion
			    bin-op mfc state)

; This function is analogous in purpose to first-match.  We search
; term for a "negative" sub-term which we can move to the other side
; of the original (in)equality.

  (if (and (eq bin-op 'BINARY-*)
	   (eq (fn-symb term) 'BINARY-+))
      (mv-let (flag to-match cancelling-piece)
        (first-negative1 (arg1 term) pattern-fun val-fun criterion
			 bin-op mfc state)
	(if flag
	    (mv flag to-match cancelling-piece)

	  (first-negative (arg2 term) pattern-fun val-fun criterion
			   bin-op mfc state)))
    (first-negative1 term pattern-fun val-fun criterion
		     bin-op mfc state)))

(local
 (in-theory (disable first-negative)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm hack957
  (implies (equal (fix (eva term a)) 0)
	   (equal (fix (eva (strip-cancelling-piece term) a)) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 4. Misc.

(defun insert-zero (sub-term term)

; Term is one of the arguments of an (in)equality from which we are
; cancelling the common factor sub-term.  We want to avoid looping
; in the case that sub-term is zero, so we use this function to
; replace those occurrences of sub-term which we would see with
; zero.


  (cond ((or (null term)
	     (variablep term)
	     (fquotep term))
	 (if (equal sub-term term)
	     ''0
	   term))
	(t
	 (case (ffn-symb term)
	   ((BINARY-+ BINARY-*)
	    (if (equal sub-term term)
		''0
	      (list (ffn-symb term)
		    (insert-zero sub-term (arg1 term))
		    (insert-zero sub-term (arg2 term)))))
	   ((UNARY-- UNARY-/)
	    (list (ffn-symb term)
		  (insert-zero sub-term (arg1 term))))
	   (EXPT

; Why do I not just return zero?  Because (equal (expt 0 n) 0)
; is true only if n is non-zero.

	    (list (ffn-symb term)
		  (insert-zero sub-term (arg1 term))
		  (arg2 term)))
	   (t
	    (if (equal sub-term term)
		''0
	      term))))))

(defthm insert-zero-correct0
  (implies (and (equal (fix (eva sub-term a)) 0)
		(not (acl2-numberp (eva term a))))
	   (equal (eva (insert-zero sub-term term) a)
		  (if (equal sub-term term)
		      0
		    (eva term a)))))

(defthm insert-zero-correcta
  (implies (and (equal (fix (eva sub-term a)) 0)
		(case-split (acl2-numberp (eva term a))))
	   (equal (eva (insert-zero sub-term term) a)
		  (eva term a))))

(local
 (in-theory (disable strip-cancelling-piece insert-zero)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun new-term-nf (term new-piece pattern pattern-fun bin-op)
  (mv-let (flag new-term)
    (new-term term new-piece pattern pattern-fun bin-op)
    (declare (ignore flag))
    new-term))

(defun good-arg (arg)
  (member-eq (fn-symb arg) '(BINARY-+ BINARY-* EXPT UNARY-- UNARY-/)))

(defthm test926
  (implies (good-arg term)
	   (acl2-numberp (eva term a)))
  :rule-classes (:type-prescription))

(local
 (in-theory (disable good-arg)))

(defun good-args-* (arg1 arg2)
  (cond ((or (null arg1)
             (null arg2))
         nil)
        ((member-eq (fn-symb arg1) '(EXPT UNARY-- UNARY-/))
	 (not (equal arg2 ''0)))
	((member-eq (fn-symb arg2) '(EXPT UNARY-- UNARY-/))
	 (not (equal arg1 ''0)))
	(t
	 t)))

(defthm nil-not-good-args-*
    (and (not (good-args-* x nil))
         (not (good-args-* nil x))))

(defun good-args-+ (arg1 arg2)
  (and (not (equal arg1 ''0))
       (not (equal arg2 ''0))))

(local
 (in-theory (disable good-args-+ good-args-*)))

(defun good-args (arg1 arg2 bin-op)
  (and (or (good-arg arg1)
	   (good-arg arg2))
       (if (eq bin-op 'BINARY-*)
	   (good-args-* arg1 arg2)
	 (good-args-+ arg1 arg2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 5. Making the meta-functions and -rules.

(defmacro make-cancelling-meta (name bin-op rel
				     pattern-fun val-fun
				     criterion result)

  (let ((fn-name (intern-name (list name "-FN")))
	(thm-name (intern-name (list name "-THM"))))

    `(progn

       (defun ,FN-NAME (term mfc state)
	 (if (and (consp term)
		  (eq (ffn-symb term) ,REL))
	     (let ((arg1 (arg1 term))
		   (arg2 (arg2 term)))
	       (if (good-args arg1 arg2 ,bin-op)
		   (mv-let (flag pattern cancelling-piece)
		     (let* ((info-list1 (info-list arg1 ,PATTERN-FUN
						   ,VAL-FUN ,BIN-OP))
			    (info-list2 (if (null info-list1)
					    nil
					  (info-list arg2 ,PATTERN-FUN
						     ,VAL-FUN ,BIN-OP))))
		       (first-match info-list1 info-list2
				    ,CRITERION
				    ,BIN-OP mfc state))
		     (if flag
			 (let ((new-arg1 (new-term-nf arg1
						      cancelling-piece
						      pattern ,PATTERN-FUN
						      ,BIN-OP))
			       (new-arg2 (new-term-nf arg2
						      cancelling-piece
						      pattern ,PATTERN-FUN
						      ,BIN-OP)))
			   ,RESULT)
		       term))
		 term))
	   term))

       (defthm ,THM-NAME
         (equal (eva term a)
	        (eva (,FN-NAME term mfc state) a))
         :rule-classes ((:meta :trigger-fns (,(unquote REL))))
         :otf-flg t)

       (local
	(in-theory (disable ,THM-NAME))))))

(defmacro make-prefer-positives-meta (name bin-op rel
					 pattern-fun val-fun
					 criterion result)

  (let ((fn-name (intern-name (list name "-FN")))
	(thm-name (intern-name (list name "-THM"))))

    `(progn

       (defun ,FN-NAME (term mfc state)
	 (if (and (consp term)
		  (eq (ffn-symb term) ,REL))
	     (let ((arg1 (arg1 term))
		   (arg2 (arg2 term)))
	       (if (or (good-arg arg1)
		       (good-arg arg2))
		   (mv-let (flag pattern cancelling-piece)
		     (mv-let (temp-flag temp-pattern temp-cancelling-piece)
		       (first-negative arg1 ,PATTERN-FUN
				       ,VAL-FUN
				       ,CRITERION
				       ,BIN-OP mfc state)
		       (if temp-flag
			   (mv temp-flag temp-pattern temp-cancelling-piece)
			 (first-negative arg2 ,PATTERN-FUN
					 ,VAL-FUN
					 ,CRITERION
					 ,BIN-OP mfc state)))
		     (if flag
			 (let ((new-arg1 (new-term-nf arg1
						      cancelling-piece
						      pattern ,PATTERN-FUN
						      ,BIN-OP))
			       (new-arg2 (new-term-nf arg2
						      cancelling-piece
						      pattern ,PATTERN-FUN
						      ,BIN-OP)))
			   ,RESULT)
		       term))
		 term))
	   term))

       (defthm ,THM-NAME
         (equal (eva term a)
	        (eva (,FN-NAME term mfc state) a))
         :rule-classes ((:meta :trigger-fns (,(unquote REL)))))

       (local
	(in-theory (disable ,THM-NAME))))))

(defmacro addends-equal-result ()
  '`(IF (ACL2-NUMBERP ,arg1)
       (IF (ACL2-NUMBERP ,arg2)
           (EQUAL ,new-arg1 ,new-arg2)
         'NIL)
      'NIL))

(defmacro addends-<-result ()
  '`(< ,new-arg1 ,new-arg2))

(defmacro factors-equal-result ()
  '`(IF (ACL2-NUMBERP ,arg1)
       (IF (ACL2-NUMBERP ,arg2)
           (IF (NOT (EQUAL (FIX ,cancelling-piece) '0))
               (EQUAL ,new-arg1 ,new-arg2)
              (EQUAL ,(insert-zero (strip-cancelling-piece cancelling-piece)
                                   arg1)
                     ,(insert-zero (strip-cancelling-piece cancelling-piece)
                                   arg2)))
          'NIL)
      'NIL))

(defmacro factors-<-result ()
  '`(IF (#-:non-standard-analysis
         RATIONALP
         #+:non-standard-analysis
         REALP
         ,cancelling-piece)
	(IF (NOT (EQUAL ,cancelling-piece '0))
	    (IF (< '0 ,cancelling-piece)
		(< ,new-arg1 ,new-arg2)
		(< ,new-arg2 ,new-arg1))
	    (< ,(insert-zero (strip-cancelling-piece cancelling-piece)
			     arg1)
	       ,(insert-zero (strip-cancelling-piece cancelling-piece)
			     arg2)))
	,term))


(local
 (in-theory (disable good-args)))


(local
 (in-theory (enable rewrite-linear-equalities-to-iff)))

(local
 (in-theory (enable good-args)))

(local (in-theory (disable cancelling-piece first-match new-term
			   info-list my-apply-1)))

(local
 (in-theory (disable good-arg good-args-+ good-args-*)))

(make-cancelling-meta cancel-addends-equal
		'BINARY-+
		'EQUAL
		'addend-pattern
		'addend-val
		'true
		(addends-equal-result))

(make-cancelling-meta cancel-addends-<
		'BINARY-+
		'<
		'addend-pattern
		'addend-val
		'true
		(addends-<-result))


(make-cancelling-meta cancel-factors-gather-exponents-equal
		'BINARY-*
		'EQUAL
		'factor-pattern-gather-exponents
		'factor-val
		'true
		(factors-equal-result))

(make-cancelling-meta cancel-factors-scatter-exponents-equal
		'BINARY-*
		'EQUAL
		'factor-pattern-scatter-exponents
		'factor-val
		'true
		(factors-equal-result))

(make-cancelling-meta cancel-factors-gather-exponents-<
		'BINARY-*
		'<
		'factor-pattern-gather-exponents
		'factor-val
		'proveably-rational
		(factors-<-result))

(make-cancelling-meta cancel-factors-scatter-exponents-<
		'BINARY-*
		'<
		'factor-pattern-scatter-exponents
		'factor-val
		'proveably-rational
		(factors-<-result))

(make-prefer-positives-meta prefer-positive-addends-equal
		'BINARY-+
		'EQUAL
		'addend-pattern
		'addend-val
		'true
		(addends-equal-result))

(make-prefer-positives-meta prefer-positive-addends-<
		'BINARY-+
		'<
		'addend-pattern
		'addend-val
		'true
		(addends-<-result))


(make-prefer-positives-meta prefer-positive-factors-gather-exponents-equal
		'BINARY-*
		'EQUAL
		'factor-pattern-gather-exponents
		'factor-val
		'true
		(factors-equal-result))

(make-prefer-positives-meta prefer-positive-factors-scatter-exponents-equal
		'BINARY-*
		'EQUAL
		'factor-pattern-scatter-exponents
		'factor-val
		'true
		(factors-equal-result))

(make-prefer-positives-meta prefer-positive-factors-gather-exponents-<
		'BINARY-*
		'<
		'factor-pattern-scatter-exponents
		'factor-val
		'proveably-rational
		(factors-<-result))

(make-prefer-positives-meta prefer-positive-factors-scatter-exponents-<
		'BINARY-*
		'<
		'factor-pattern-scatter-exponents
		'factor-val
		'proveably-rational
		(factors-<-result))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(table acl2-defaults-table :state-ok nil)
