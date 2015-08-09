(in-package "ACL2")

(include-book "pstate")
(include-book "gensym-e")

(mutual-recursion

 (defun progstmt (s)
   (declare (xargs :guard t))
   (cond ((statementp s) t)
	 ((and (>= (len s) 3)
	       (equal (car s) 'if)
	       (expressionp (second s)))
	  (proglistelse (cddr s)))

	 ((and (>= (len s) 3)
	       (equal (car s) 'while)
	       (expressionp (second s)))
	  (proglist (cddr s)))
	 (t nil)))

 (defun proglistelse (s)  ;; list of progstmts with at most one 'else
   (declare (xargs :guard t))
   (cond ((atom s) (null s))
	 ((equal (car s) 'else) (proglist (cdr s)))
	 (t (and (progstmt (car s))
		 (proglistelse (cdr s))))))

 (defun proglist (s)  ;; list of progstmts
   (declare (xargs :guard t))
   (cond ((atom s) (null s))
	 (t (and (progstmt (car s))
		 (proglist (cdr s))))))
 )

(defun prog-i (flg s)
  (declare (xargs :guard t))
  (cond ((equal flg 0)
	 (cond ((statementp s) 'leaf)
	       ((and (>= (len s) 3)
		     (equal (car s) 'if)
		     (expressionp (second s))) (prog-i 1 (cddr s)))

	       ((and (>= (len s) 3)
		     (equal (car s) 'while)
		     (expressionp (second s))) (prog-i 2 (cddr s)))
	       (t 'leaf)))
	((equal flg 1)
	 (cond ((atom s) 'leaf)
	       ((equal (car s) 'else) (prog-i 2 (cdr s)))
	       (t (cons (prog-i 0 (car s))
			(prog-i 1 (cdr s))))))
	(t
	 (cond ((atom s) 'leaf)
	       (t (cons (prog-i 0 (car s))
			(prog-i 2 (cdr s))))))
	))

(mutual-recursion

 (defun labels-stmt (s)
   (declare (xargs :guard (progstmt s)
		   :verify-guards nil))
   (cond ((statementp s) (if (equal (first s) 'label)
			     (list (second s))
			   nil))
	 ((and (>= (len s) 3)
	       (equal (car s) 'if)
	       (expressionp (second s))) (labels-list (cddr s)))

	 ((and (>= (len s) 3)
	       (equal (car s) 'while)
	       (expressionp (second s))) (labels-list (cddr s)))
	 (t nil)))

 (defun labels-list (s)
   (declare (xargs :guard (proglist s)))
   (cond ((atom s) nil)
	 (t (append (labels-stmt (car s))
		    (labels-list (cdr s))))))
 )

#|
;; To make this section doesn work, i think we'd have to either make
;; the mutual recursion of labels-stmt like that of progstmt, or
;; make a speical induction function for labels-stmt.

(defthm labels-symbol-listp-flg
  (if flg
      (symbol-listp (labels-stmt s))
    (symbol-listp (labels-list s)))
  :hints (("Goal"
	   :induct (prog-i flg s)))
  :rule-classes nil)

(defthm labels-stmt-symbol-listp
  (symbol-listp (labels-stmt x))
  :hints (("Goal"
	   :by (:instance labels-symbol-listp-flg (flg t)))))

(defthm labels-list-symbol-listp
  (symbol-listp (labels-list x))
  :hints (("Goal"
	   :by (:instance labels-symbol-listp-flg (flg nil)))))

(defthm symbol-list-is-true-list
  (implies (symbol-listp x)
	   (true-listp x)))

(verify-guards labels-stmt
	       :otf-flg t)

|#

(defun then-part (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((atom l) nil)
	((equal (car l) 'else) nil)
	(t (cons (car l) (then-part (cdr l))))))

(defun else-part (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((atom l) nil)
	((equal (car l) 'else) (cdr l))
	(t (else-part (cdr l)))))

(mutual-recursion

 (defun compile-stmt (s labs)  ;; return a list of statements
   (declare (xargs :guard (and (progstmt s)
			       (symbol-listp labs))
		   :verify-guards nil))

   (cond ((and (>= (len s) 3)
	       (equal (car s) 'if)
	       (expressionp (second s)))

	  (let ((cond (second s))
		(then (then-part (cddr s)))
		(else (else-part (cddr s)))
		(else-label (gen-symbol 'else- labs))
		(endif-label (gen-symbol 'endif- labs)))
	    (let* ((then-seg (compile-list
			      then
			      (list* else-label endif-label labs)))
		   (then-labels (labels-list then-seg)))

	      (append (list (list 'branch (list 'not cond) else-label))
		      then-seg
		      (list (list 'goto endif-label))
		      (list (list 'label else-label))
		      (compile-list
		       else
		       (append (list* else-label endif-label labs)
			       then-labels))

		      (list (list 'label endif-label))))))

	 ((and (>= (len s) 3)
	       (equal (car s) 'while)
	       (expressionp (second s)))

	  (let ((cond (second s))
		(body (cddr s))
		(start-label (gen-symbol 'startwhile- labs))
		(end-label (gen-symbol 'endwhile- labs)))
	    (append (list (list 'label start-label))
		    (list (list 'branch (list 'not cond) end-label))
		    (compile-list body (list* start-label end-label labs))
		    (list (list 'goto start-label))
		    (list (list 'label end-label)))))
	 (t (list s))))

 (defun compile-list (c labs)
   (declare (xargs :guard (and (proglist c)
			       (symbol-listp labs))))

   (cond ((atom c) nil)
	 (t (let* ((cc (compile-stmt (car c) labs))
		   (cclabs (labels-list cc)))
	      (append cc
		      (compile-list (cdr c) (append labs cclabs))))))))

;;-------------------

;;  A few things have been omitted.
;;  To prove things about compile-stmt/list, I think we need a special
;;  induction scheme, because of the label arguments.  In particular,
;;  1. to verify guards,
;;  2. to prove that compiling a prog-list gives a statement-listp.

;; (verify-guards compile-stmt
;;	       :otf-flg t)

;  for example,

#|
(compile-list '(
		(while p1 (return))
		)
	      '(else-6 lkj-9))

(compile-list '(
		(if c1
		    (return)
		    (if c2
			(return)
		        (return)
			else
			(return))
		    (return)
		    else
		    (return)
		    (return)
		    (return))
		(while p1
		  (return)
		  (while c2 (return) (return))
		  (return))
		)
	      '(else-6 lkj-9))
|#
