; deflist.lisp -- defining typed lists
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bill Bevier (bevier@cli.com) and Bishop Brock
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    deflist.lisp
;;;
;;;    A package for defining a recognizer for a typed list. Rewrite
;;;    rules describing how the recognizer interacts with functions
;;;    from the list theory can be automatically generated.
;;;
;;;    Bill Bevier
;;;    Computational Logic, Inc.
;;;    1717 West 6th Street, Suite 290
;;;    Austin, Texas 78703
;;;    bevier@cli.com
;;;
;;;    Modified by Bishop Brock, brock@cli.com
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

; Modified by Jared Davis, October 2014, to port documentation to xdoc.
; Includes tweaks made by Mihir Mehta 4/2019 for a change to the
; definition of take.

(in-package "ACL2")

(include-book "list-defuns")
(include-book "utilities")
(local (include-book "list-defthms"))

; ------------------------------------------------------------
; This section introduces three pairs of predicates
;
;  ELEM-TYPE00, LIST-TYPE00
;  ELEM-TYPE10, LIST-TYPE10
;  ELEM-TYPE11, LIST-TYPE11
;
; ELEM-type00 is a unary predicate, and LIST-type00 is a unary predicate
; that recognizes lists in which every element satisfies ELEM-type00.
; ELEM-TYPE11 and LIST-TYPE11 are similar, but allow an extra
; parameter. The parameter that represents the value to be tested is
; the left one. For example, ELEM-TYPE10 can be instantiated with
; the function  (lambda (x lub) (and (numberp x) (< x lub)))
; and LIST-TYPE10 can be similarly instantiated.
;
; The only difference between ELEM-TYPE11 and ELEM-TYPE10 is the
; order of the parameters. In 11, the tested arg is second;
; in 10, the tested arg is first.
;
; Note: do not change the names of these functions. The names are
; used in subsequent macros.
; ------------------------------------------------------------

(encapsulate ((elem-type00 (x) boolean)
	      (list-type00 (l) boolean))
  (local (in-theory '(ground-zero)))
  (local (defun elem-type00 (x)
	   (declare (ignore))
	   (integerp x)))
  (local (defun list-type00 (l)
	   (cond ((atom l) (eq l nil))
		 (t (and (elem-type00 (car l))
			 (list-type00 (cdr l)))))))
  (defthm list-type00-defun
    (iff (list-type00 l)
	 (cond ((atom l) (eq l nil))
	       (t (and (elem-type00 (car l))
		       (list-type00 (cdr l))))))
    :rule-classes ((:rewrite :corollary
			     (implies (atom l)
				      (equal (list-type00 l) (null l))))
		   (:rewrite :corollary
			     (equal (list-type00 (cons x l))
				    (and (elem-type00 x)
					 (list-type00 l))))))
  )

(encapsulate ((elem-type10 (x a) boolean)
	      (list-type10 (l a) boolean))
  (local (in-theory '(ground-zero)))
  (local (defun elem-type10 (x a)
	   (declare (ignore a))
	   (integerp x)))
  (local (defun list-type10 (l a)
	   (cond ((atom l) (eq l nil))
		 (t (and (elem-type10 (car l) a)
			 (list-type10 (cdr l) a))))))
  (defthm list-type10-defun
    (iff (list-type10 l a)
	 (cond ((atom l) (eq l nil))
	       (t (and (elem-type10 (car l) a)
		       (list-type10 (cdr l) a)))))
    :rule-classes ((:rewrite :corollary
			     (implies (atom l)
				      (equal (list-type10 l a) (null l))))
		   (:rewrite :corollary
			     (equal (list-type10 (cons x l) a)
				    (and (elem-type10 x a)
					 (list-type10 l a))))))
  )

(encapsulate ((elem-type11 (a x) boolean)
	      (list-type11 (a l) boolean))
  (local (in-theory '(ground-zero)))
  (local (defun elem-type11 (a x)
	   (declare (ignore a))
	   (integerp x)))
  (local (defun list-type11 (a l)
	   (cond ((atom l) (eq l nil))
		 (t (and (elem-type11 a (car l))
			 (list-type11 a (cdr l)))))))
  (defthm list-type11-defun
    (iff (list-type11 a l)
	 (cond ((atom l) (eq l nil))
	       (t (and (elem-type11 a (car l))
		       (list-type11 a (cdr l))))))
    :rule-classes ((:rewrite :corollary
			     (implies (atom l)
				      (equal (list-type11 a l) (null l))))
		   (:rewrite :corollary
			     (equal (list-type11 a (cons x l))
				    (and (elem-type11 a x)
					 (list-type11 a l))))))
  )

;; Some utility functions

(defun replace-equal (a b l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) nil)
	((equal (car l) a) (cons b (replace-equal a b (cdr l))))
	(t (cons (car l) (replace-equal a b (cdr l))))))

(defun my-conjoin (termlist1 termlist2)
  (declare (xargs :guard (and (true-listp termlist1)
			      (true-listp termlist2)
			      (or (consp termlist1) (consp termlist2)))))
  (let ((termlist (append termlist1 termlist2)))
    (cond ((= (len termlist) 1)
	   (car termlist))
	  (t (fcons-term 'and termlist)))))

(mutual-recursion

 (defun my-conjuncts (term)
   (cond ((eq term t) ())
	 ((atom term) (list term))
	 ((eq (car term) 'and) (my-conjuncts-list (cdr term)))
	 (t (list term))))

 (defun my-conjuncts-list (termlist)
   (cond ((atom termlist) nil)
	 (t (append (my-conjuncts (car termlist))
		    (my-conjuncts-list (cdr termlist))))))
 )

; For each lemma in the theory, the lemma term is defined by a macro
; to make it easy to instantiate. The lemma is then proved.

; The macros in the following script generate forms that are believed to be
; lemmas about list predicates. The arguments to these macros have the following meanings.
; elem-type-fn: a symbol that names a predicate, or a lambda expression of one argument
; list-type-fn: a symbol that names a predicate which recognizes a list of elem types
; formals:      the formal parameter list to list-type-fn
;               The convention is that the formal parameter L represents the list argument.
;               If elem-type-fn is a symbol, then the formal parameter list to elem-type-fn
;               assumes that the parameter in this position represents an element in the list.
; guard         either 't, or an expression in the formal parameters
;
; Example:
;
;  (defun bound-numberp (x lub)
;    (and (acl2-numberp x) (acl2-numberp lub) (< x lub)))
;
;  (defun bound-number-listp (l lub)
;    (cond ((atom l) t)
;          (t (and (bound-numberp (car l) lub)
;                  (bound-number-listp (cdr l) lub)))))
;

; ---------- TRUE-LISTP ----------

(defmacro list-type-true-listp-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  `(implies ,(my-conjoin (my-conjuncts guard)
			 `((,list-type-fn ,@formals)))
	    (true-listp l)))

(defthm list-type-true-listp00
  (list-type-true-listp-lemma elem-type00 list-type00 (l))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct t)))

(defthm list-type-true-listp10
  (list-type-true-listp-lemma elem-type10 list-type10 (l a))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct t)))

(defthm list-type-true-listp11
  (list-type-true-listp-lemma elem-type11 list-type11 (a l))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct t)))


; ---------- CONS ----------

(defmacro list-type-cons-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "X" list-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,elem-type-fn ,@(if (symbolp elem-type-fn) (replace-equal 'l var formals) (list var)))
			     (,list-type-fn ,@formals)))
	      (,list-type-fn ,@(replace-equal 'l `(cons ,var l) formals)))))

(defthm list-type-cons00
  (list-type-cons-lemma elem-type00 list-type00 (l))
  :rule-classes nil)

(defthm list-type-cons10
  (list-type-cons-lemma elem-type10 list-type10 (l a))
  :rule-classes nil)

(defthm list-type-cons11
  (list-type-cons-lemma elem-type11 list-type11 (a l))
  :rule-classes nil)

; ---------- CDR ----------

(defmacro list-type-cdr-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  `(implies ,(my-conjoin (my-conjuncts guard)
 			 `((,list-type-fn ,@formals)))
 	    (,list-type-fn ,@(replace-equal 'l '(cdr l) formals))))

(defthm list-type-cdr00
  (list-type-cdr-lemma elem-type00 list-type00 (l)))

(defthm list-type-cdr10
  (list-type-cdr-lemma elem-type10 list-type10 (l a)))

(defthm list-type-cdr11
  (list-type-cdr-lemma elem-type11 list-type11 (a l)))

(in-theory (disable list-type-cdr00 list-type-cdr10
 		    list-type-cdr11))


; ---------- APPEND ----------

(defmacro list-type-append-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  (let* ((vars (u::unique-symbols 2 (intern-in-package-of-symbol "L" list-type-fn) formals))
	 (var1 (car vars))
	 (var2 (cadr vars)))
    `(implies ,(my-conjoin (my-conjuncts guard) `((true-listp ,var1)))
	      (equal (,list-type-fn ,@(replace-equal 'l `(append ,var1 ,var2) formals))
		     (and (,list-type-fn ,@(replace-equal 'l var1 formals))
			  (,list-type-fn ,@(replace-equal 'l var2 formals)))))))

(defthm list-type-append00
  (list-type-append-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :induct t)))

(defthm list-type-append10
  (list-type-append-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :induct t)))

(defthm list-type-append11
  (list-type-append-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :induct t)))

; ---------- FIRSTN ----------

(defmacro list-type-firstn-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "N" list-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,list-type-fn ,@formals)))
	      (,list-type-fn ,@(replace-equal 'l `(firstn ,var l) formals)))))

(defthm list-type-firstn00
  (list-type-firstn-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00))))

(defthm list-type-firstn10
  (list-type-firstn-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10))))

(defthm list-type-firstn11
  (list-type-firstn-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11))))

; ---------- LAST ----------

(defmacro list-type-last-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  `(implies ,(my-conjoin (my-conjuncts guard)
			 `((,list-type-fn ,@formals)))
	    (,list-type-fn ,@(replace-equal 'l '(last l) formals))))

(defthm list-type-last00
  (list-type-last-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :induct t)))

(defthm list-type-last10
  (list-type-last-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :induct t)))

(defthm list-type-last11
  (list-type-last-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :induct t)))


; ---------- MAKE-LIST ----------

(defmacro list-type-make-list-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (let* ((vars (u::unique-symbols 3 (intern-in-package-of-symbol "X" list-type-fn) formals))
	 (var1 (car vars))
	 (var2 (cadr vars))
	 (var3 (caddr vars))
	 (guards (my-conjuncts guard))
	 (rule `(iff (,list-type-fn ,@(replace-equal 'l `(make-list-ac ,var1 ,var2 ,var3) formals))
		     (and (or (zp ,var1)
			      (,elem-type-fn ,@(if (symbolp elem-type-fn) (replace-equal 'l var2 formals) (list var2))))
			  (,list-type-fn ,@(replace-equal 'l var3 formals))))))
    (cond (guards `(implies ,(my-conjoin guards nil)
			    ,rule))
	  (t rule))))

(defthm list-type-make-list00
  (list-type-make-list-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00))))

(defthm list-type-make-list10
  (list-type-make-list-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10))))

(defthm list-type-make-list11
  (list-type-make-list-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11))))

; ---------- NTHCDR ----------

(defmacro list-type-nthcdr-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "N" list-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,list-type-fn ,@formals)))
	      (,list-type-fn ,@(replace-equal 'l `(nthcdr ,var l) formals)))))

(defthm list-type-nthcdr00
  (list-type-nthcdr-lemma elem-type00 list-type00 (l))
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00))))

(defthm list-type-nthcdr10
  (list-type-nthcdr-lemma elem-type10 list-type10 (l a))
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10))))

(defthm list-type-nthcdr11
  (list-type-nthcdr-lemma elem-type11 list-type11 (a l))
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11))))

; ---------- NTH-SEG ----------

(defmacro list-type-nth-seg-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  (let* ((vars (u::unique-symbols 2 (intern-in-package-of-symbol "N" list-type-fn) formals))
	 (var1 (car vars))
	 (var2 (cadr vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,list-type-fn ,@formals)))
	      (,list-type-fn ,@(replace-equal 'l `(nth-seg ,var1 ,var2 l) formals)))))

(defthm list-type-nth-seg00
  (list-type-nth-seg-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00))))

(defthm list-type-nth-seg10
  (list-type-nth-seg-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10))))

(defthm list-type-nth-seg11
  (list-type-nth-seg-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11))))

; ---------- PUT-NTH ----------

(defmacro list-type-put-nth-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (let* ((vars (u::unique-symbols 2 (intern-in-package-of-symbol "N" list-type-fn) formals))
	 (var1 (car vars))
	 (var2 (cadr vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,list-type-fn ,@formals)))
	      (iff (,list-type-fn ,@(replace-equal 'l `(put-nth ,var1 ,var2 l) formals))
		   (if (< (nfix ,var1) (len l))
		       (,elem-type-fn ,@(if (symbolp elem-type-fn) (replace-equal 'l var2 formals) (list var2)))
		     t)))))

(defthm list-type-put-nth00
  (list-type-put-nth-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00))))

(defthm list-type-put-nth10
  (list-type-put-nth-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10))))

(defthm list-type-put-nth11
  (list-type-put-nth-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11))))

; ---------- PUT-SEG ----------

(defmacro list-type-put-seg-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  (let* ((vars (u::unique-symbols 2 (intern-in-package-of-symbol "N" list-type-fn) formals))
	 (var1 (car vars))
	 (var2 (cadr vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,list-type-fn ,@formals)
			     (,list-type-fn ,@(replace-equal 'l var2 formals))))
	      (,list-type-fn ,@(replace-equal 'l `(put-seg ,var1 ,var2 l) formals)))))

(defthm list-type-put-seg00
  (list-type-put-seg-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00))))

(defthm list-type-put-seg10
  (list-type-put-seg-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10))))

(defthm list-type-put-seg11
  (list-type-put-seg-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11))))

; ---------- REMOVE-EQUAL ----------

(defmacro list-type-remove-equal-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "N" list-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,list-type-fn ,@formals)))
	      (,list-type-fn ,@(replace-equal 'l `(remove-equal ,var l) formals)))))

(defthm list-type-remove-equal00
  (list-type-remove-equal-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00))))

(defthm list-type-remove-equal10
  (list-type-remove-equal-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10))))

(defthm list-type-remove-equal11
  (list-type-remove-equal-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11))))

; ---------- REVAPPEND ----------

(defmacro list-type-revappend-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  (let* ((vars (u::unique-symbols 2
				  (intern-in-package-of-symbol "L" list-type-fn)
				  formals))
	 (var1 (car vars))
	 (var2 (cadr vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,list-type-fn ,@(replace-equal 'l var1 formals))
			     (,list-type-fn ,@(replace-equal 'l var2 formals))))
	      (,list-type-fn ,@(replace-equal 'l `(revappend ,var1 ,var2) formals)))))

(defthm list-type-revappend00
  (list-type-revappend-lemma elem-type00 list-type00 (l))
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00))))

(defthm list-type-revappend10
  (list-type-revappend-lemma elem-type10 list-type10 (l a))
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10))))

(defthm list-type-revappend11
  (list-type-revappend-lemma elem-type11 list-type11 (a l))
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11))))

(in-theory (disable list-type-revappend00
		    list-type-revappend10
		    list-type-revappend11))

; ---------- REVERSE ----------

(defmacro list-type-reverse-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  `(implies ,(my-conjoin (my-conjuncts guard)
			 `((,list-type-fn ,@formals)))
	    (,list-type-fn ,@(replace-equal 'l '(reverse l) formals))))


(defthm list-type-reverse00
  (list-type-reverse-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (enable list-type-revappend00))))

(defthm list-type-reverse10
  (list-type-reverse-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (enable list-type-revappend10))))

(defthm list-type-reverse11
  (list-type-reverse-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (enable list-type-revappend11))))

; ---------- TAKE ----------

(defmacro list-type-take-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  (let* ((nvars (u::unique-symbols 1 (intern-in-package-of-symbol "N" list-type-fn) formals))
	 (nvar (car nvars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,list-type-fn ,@formals)
			     (<= ,nvar (len l))))
	      (,list-type-fn
	       ,@(replace-equal 'l `(take ,nvar l) formals)))))

(defthm list-type-take00
  (list-type-take-lemma elem-type00 list-type00 (l))
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00 list-type-revappend00))))

(defthm list-type-take10
  (list-type-take-lemma elem-type10 list-type10 (l a))
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10 list-type-revappend10))))

(defthm list-type-take11
  (list-type-take-lemma elem-type11 list-type11 (a l))
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11 list-type-revappend11))))

; ---------- BUTLAST ----------

(defmacro list-type-butlast-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "N" list-type-fn) formals))
	 (var (car vars)))
    `(IMPLIES ,(my-conjoin (my-conjuncts guard)
			   `((,LIST-TYPE-fn ,@formals)
			     (<= 0 ,var)))
	      (,LIST-TYPE-fn ,@(replace-equal 'l `(BUTLAST L ,var) formals)))))

(defthm list-type-butlast00
  (list-type-butlast-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (butlast) (take-is-xfirstn first-n-ac-non-recursive)))))

(defthm list-type-butlast10
  (list-type-butlast-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (butlast) (take-is-xfirstn first-n-ac-non-recursive)))))

(defthm list-type-butlast11
  (list-type-butlast-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (butlast) (take-is-xfirstn first-n-ac-non-recursive)))))

; ---------- SUBSEQ ----------

(defmacro list-type-subseq-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  (let* ((startvars (u::unique-symbols 1 (intern-in-package-of-symbol "START" list-type-fn) formals))
	 (startvar (car startvars))
	 (endvars (u::unique-symbols 1 (intern-in-package-of-symbol "END" list-type-fn) formals))
	 (endvar (car endvars)))
    `(IMPLIES ,(my-conjoin (my-conjuncts guard)
			   `((,LIST-TYPE-fn ,@formals)
			     (integerp ,startvar)
			     (<= 0 ,startvar)
			     (<= ,startvar (len l))
			     (or (null ,endvar)
				 (and (integerp ,endvar)
				      (<= ,endvar (len l))))))
	      (,LIST-TYPE-fn ,@(replace-equal 'l `(subseq L ,startvar ,endvar) formals)))))

(defthm list-type-subseq00
  (list-type-subseq-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (subseq) (take-is-xfirstn first-n-ac-non-recursive)))))

(defthm list-type-subseq10
  (list-type-subseq-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (subseq) (take-is-xfirstn first-n-ac-non-recursive)))))

(defthm list-type-subseq11
  (list-type-subseq-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (subseq) (take-is-xfirstn first-n-ac-non-recursive)))))

; ---------- UPDATE-NTH ----------

(defmacro list-type-update-nth-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (let* ((nvars (u::unique-symbols 1 (intern-in-package-of-symbol "N" list-type-fn) formals))
	 (nvar (car nvars))
	 (valvars (u::unique-symbols 1 (intern-in-package-of-symbol "VAL" list-type-fn) formals))
	 (valvar (car valvars)))
    `(IMPLIES ,(my-conjoin (my-conjuncts guard)
			   `((,LIST-TYPE-fn ,@formals)
			     (,elem-type-fn ,@(if (symbolp elem-type-fn) (replace-equal 'l valvar formals) (list valvar)))
			     (<= ,nvar (len l))))
	      (,LIST-TYPE-fn ,@(replace-equal 'l `(update-nth ,nvar ,valvar L) formals)))))

(defthm list-type-update-nth00
  (list-type-update-nth-lemma elem-type00 list-type00 (l))
  :rule-classes nil)

(defthm list-type-update-nth10
  (list-type-update-nth-lemma elem-type10 list-type10 (l a))
  :rule-classes nil)

(defthm list-type-update-nth11
  (list-type-update-nth-lemma elem-type11 list-type11 (a l))
  :rule-classes nil)

; ---------- INITIAL-SUBLISTP-EQUAL ----------

(defmacro list-type-initial-sublistp-equal-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  (let* ((xvars (u::unique-symbols 1 (intern-in-package-of-symbol "X" list-type-fn) formals))
	 (xvar (car xvars)))
    `(IMPLIES ,(my-conjoin (my-conjuncts guard)
			   `((,LIST-TYPE-fn ,@formals)
			     (true-listp ,xvar)
			     (initial-sublistp-equal ,xvar l)))
	      (,LIST-TYPE-fn ,@(replace-equal 'l xvar formals)))))

(defthm list-type-initial-sublistp-equal00
  (list-type-initial-sublistp-equal-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00))))

(defthm list-type-initial-sublistp-equal10
  (list-type-initial-sublistp-equal-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10))))

(defthm list-type-initial-sublistp-equal11
  (list-type-initial-sublistp-equal-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11))))

; ---------- MEMBER-EQUAL ----------

(defmacro list-type-member-equal-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "X" list-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((member-equal ,var l)
			     (,list-type-fn ,@formals)))
	      (,elem-type-fn ,@(if (symbolp elem-type-fn) (replace-equal 'l var formals) (list var))))))

(defthm list-type-member-equal00
  (list-type-member-equal-lemma elem-type00 list-type00 (l))
  :rule-classes :rewrite
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00))))

(defthm list-type-member-equal10
  (list-type-member-equal-lemma elem-type10 list-type10 (l a))
  :rule-classes :rewrite
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10))))

(defthm list-type-member-equal11
  (list-type-member-equal-lemma elem-type11 list-type11 (a l))
  :rule-classes :rewrite
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11))))


; ---------- MEMBERP-EQUAL ----------

; This is an odd case. Apparently, because MEMBERP-EQUAL is a
; non-recursive function, the theorem prover cannot automatically
; guess an induction strategy. Therefore, we must explictly give an
; induction hint in the three following DEFTHMs. The fallout is that
; we can't automatically generate a unique variable in the macro
; LIST-TYPE-MEMBERP-EQUAL-LEMMA.  We must pick one that is unlikely to
; appear as an auxiliary argument to a list-type predicate, so that we
; can mention it explicitly in the induction hints in the lemmas.

(defmacro list-type-memberp-equal-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (let ((var (intern-in-package-of-symbol "X" 'x-unlikely-variable-name-x)))
    `(implies ,(my-conjoin `((memberp-equal ,var l)
			   (,list-type-fn ,@formals))
			 (my-conjuncts guard))
	    (,elem-type-fn ,@(if (symbolp elem-type-fn) (replace-equal 'l var formals) (list var))))))

(defthm list-type-memberp-equal00
  (list-type-memberp-equal-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :induct (member-equal x-unlikely-variable-name-x l) :in-theory (enable list-type-cdr00 memberp-equal))))

(defthm list-type-memberp-equal10
  (list-type-memberp-equal-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :induct (member-equal x-unlikely-variable-name-x l) :in-theory (enable list-type-cdr10))))

(defthm list-type-memberp-equal11
  (list-type-memberp-equal-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :induct (member-equal x-unlikely-variable-name-x l) :in-theory (enable list-type-cdr11))))

; ---------- REMOVE-DUPLICATES-EQUAL ----------

(defmacro list-type-remove-duplicates-equal-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (declare (ignore elem-type-fn))
  `(implies ,(my-conjoin (my-conjuncts guard)
			 `((,list-type-fn ,@formals)))
	    (,list-type-fn ,@(replace-equal 'l `(remove-duplicates-equal l) formals))))

(defthm list-type-remove-duplicates-equal00
  (list-type-remove-duplicates-equal-lemma elem-type00 list-type00 (l))
  :hints (("Goal" :induct t)))

(defthm list-type-remove-duplicates-equal10
  (list-type-remove-duplicates-equal-lemma elem-type10 list-type10 (l a))
  :hints (("Goal" :induct t)))

(defthm list-type-remove-duplicates-equal11
  (list-type-remove-duplicates-equal-lemma elem-type11 list-type11 (a l))
  :hints (("Goal" :induct t)))

; ---------- CAR ----------

(defmacro list-type-car-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  `(implies ,(my-conjoin (my-conjuncts guard)
			 `((,list-type-fn ,@formals)
			   l))
	    (,elem-type-fn ,@(if (symbolp elem-type-fn) (replace-equal 'l '(car l) formals) (list '(car l))))))

(defthm list-type-car00
  (list-type-car-lemma elem-type00 list-type00 (l))
  :rule-classes nil)

(defthm list-type-car10
  (list-type-car-lemma elem-type10 list-type10 (l a))
  :rule-classes nil)

(defthm list-type-car11
  (list-type-car-lemma elem-type11 list-type11 (a l))
  :rule-classes nil)

; ---------- NTH ----------

(defmacro list-type-nth-lemma (elem-type-fn list-type-fn formals &optional (guard 't))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "N" list-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,list-type-fn ,@formals)
			     (< (nfix ,var) (len l))))
	      (,elem-type-fn ,@(if (symbolp elem-type-fn) (replace-equal 'l `(nth ,var l) formals) (list `(nth ,var l)))))))

(defthm list-type-nth00
  (list-type-nth-lemma elem-type00 list-type00 (l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr00))))

(defthm list-type-nth10
  (list-type-nth-lemma elem-type10 list-type10 (l a))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr10))))

(defthm list-type-nth11
  (list-type-nth-lemma elem-type11 list-type11 (a l))
  :rule-classes nil
  :hints (("Goal" :induct t :in-theory (enable list-type-cdr11))))

; ------------------------------------------------------------
; Typed Lists
; ------------------------------------------------------------

(defun pack-intern-names (name1 name2)
  (u::pack-intern name1 name1 "-" name2))

(u::defloop pack-intern-all-names (name l)
	    (for ((x in l))
		 (collect (pack-intern-names name x))))

; DEFLIST-DEFTHMS.
; Generate a list of DEFTHM forms. These defthms explain
; the properties of standard list operations with
; respect to a typed list predicate.
; For arguments, see documentation for DEF-TYPED-LIST
; macro below.

(u::defloop deflist-defthms (list-type-fn formals elem-type-fn guard theory car-rule-classes nth-rule-classes)
	    (declare (xargs :guard (and (symbolp list-type-fn)
					(arglistp formals)
					(consp formals)
					(or (symbolp elem-type-fn)
					    (and (consp elem-type-fn)
						 (eq (car elem-type-fn) 'acl2::lambda)
						 (<= (len (cadr elem-type-fn)) 2)))
					(symbol-listp theory))
			    :mode :program))
	    (for ((fn in theory))
		 (collect (let ((lemmaname (pack-intern-names list-type-fn fn))
				(lemma-macro-name (u::pack-intern list-type-fn 'list-type- fn '-lemma))
				(rule-classes (case fn
						(car car-rule-classes)
						(nth nth-rule-classes)
						(true-listp '(:forward-chaining))
						(t '(:rewrite))))
				;; If guards are present, or the number of formals is greater then 2, then
				;; the proofs must be done by induction. Otherwise, we can get the proofs
				;; much more quickly by functional instantiation.
				(hints (if (or (consp (my-conjuncts guard))
					       (> (len formals) 2))
					   `(("Goal" :induct t))
					 (let* ((numparams (1- (len formals)))
						(posn (position-equal 'l formals))
						(numparams-string (coerce (explode-nonnegative-integer numparams 10 nil) 'string))
						(posn-string (coerce (explode-nonnegative-integer posn 10 nil) 'string))
						(canonical-elem-type-fn (u::pack-intern list-type-fn 'elem-type numparams-string posn-string))
						(canonical-list-type-fn (u::pack-intern list-type-fn 'list-type numparams-string posn-string))
						(lemma-name (u::pack-intern list-type-fn 'list-type- fn numparams-string posn-string))
						;; The functional instance of the elem-type-fn is presented as a lambda form
						;; since the elem-type recognizer may be a macro.
						(elem-type-instance (cond ((and (consp elem-type-fn)
										(eq (car elem-type-fn) 'acl2::lambda))
									   elem-type-fn)
									  (t (let ((elem-formals (replace-equal 'l 'x formals)))
									       `(lambda ,elem-formals (,elem-type-fn ,@elem-formals))))))
						(subst (case (length formals)
							 (2 `((a ,(car (remove 'l formals)))))
							 (t nil))))
					   `(("Goal" :do-not-induct t
					      :use (:functional-instance
						    (:instance ,lemma-name ,@subst)
						    (,canonical-elem-type-fn ,elem-type-instance)
						    (,canonical-list-type-fn ,list-type-fn))))
					   )))
				)
			    `(DEFTHM ,lemmaname
			       (,lemma-macro-name ,elem-type-fn ,list-type-fn ,formals ,guard)
			       :rule-classes ,rule-classes
			       :hints ,hints)))))

(defconst *deflist-options*
  '(:CAR-RULE-CLASSES :NTH-RULE-CLASSES :THEORY :OMIT-DEFUN :THEORY-NAME)
  "This list contains all of the  valid keyword options for DEFLIST.")

(defconst *deflist-theory-options*
  '((append)
    (butlast)
    (cons)
    (car)
    (cdr)
    (firstn)
    (initial-sublistp-equal)
    (last)
    (make-list)
    (member-equal)
    (memberp-equal)
    (nth)
    (nth-seg)
    (nthcdr)
    (put-nth)
    (put-seg)
    (remove-duplicates-equal)
    (remove-equal)
    (reverse)
    (subseq)
    (true-listp)
    (update-nth))
  "This Alist contains all of the symbols recognized as valid options for
   the DEFLIST :THEORY option. Each symbol is associated with the other functions
   that must be present due to functional dependencies.")

(defconst *forward-chaining-elem-types*
  '(integerp rationalp complex-rationalp symbolp true-listp stringp characterp
	     alistp acl2-numberp
             #+:non-standard-analysis realp
             #+:non-standard-analysis complexp)
  "When an element type recognizer is one of these, then CAR-RULE-CLASSES and
NTH-RULE-CLASSES defaults to :forward-chaining, otherwise :rewrite.")

(defun my-set-difference (l1 l2)
  (cond ((atom l1) nil)
	((member-equal (car l1) l2)
	 (my-set-difference (cdr l1) l2))
	(t (cons (car l1) (my-set-difference (cdr l1) l2)))))


(defun insert-dependencies (l alist already-seen)
  (cond ((atom l) nil)
	((member (car l) already-seen)
	 (insert-dependencies (cdr l) alist already-seen))
	(t (let ((pair (assoc-equal (car l) alist)))
	     (let ((new (my-set-difference (cdr pair) already-seen)))
	       (append new (list (car l)) (insert-dependencies (cdr l) alist (cons (car l) (append new already-seen)))))))))

(deftheory minimal-theory-for-deflist
  (union-theories
   (current-theory 'ground-zero)
   (current-theory 'list-defuns)))

(defun deflist-check-syntax (name formals body)
  "Return NIL if no errors, otherwise crash."
  (declare (xargs :mode :program))
  (cond
   ((not (symbolp name))
    (u::bomb 'DEFLIST "The function name must be a symbol, but ~p0 is not."
	     name))
   ((not (true-listp formals))
    (u::bomb 'DEFLIST "The argument list ~p0 is not a true list." formals))
   ((not (arglistp formals))
    (mv-let (elmt msg) (find-first-bad-arg formals)
      (u::bomb 'DEFLIST "The argument list ~p0 is not valid because the ~
                         element ~p1 ~@2." formals elmt msg)))
   ((let* ((formal-strings (u::mapcar-string formals))
	   (l-tail (member-equal "L" formal-strings))
	   (multiple-ls (member-equal "L" (cdr l-tail))))
      (or (not l-tail) multiple-ls))
    (u::bomb 'DEFLIST "The formal argument list to DEFLIST must be a valid ~
                       functional argument list that contains exactly 1 ~
                       symbol whose print-name is \"L\", but ~p0 is not."
	     formals))
   ((null body) (u::bomb 'DEFLIST "The function body is empty!"))
   (t (let* ((last-form (car (last body)))
	     (options? (and (>= (len body) 2)
			    (true-listp last-form)
			    (eq (car last-form) :OPTIONS)))
	     (predicate (if options?
			    (car (last (butlast body 1)))
			  last-form)))
	(cond
	 ((or (symbolp predicate)
	      (and (true-listp predicate)
		   (equal (len predicate) 3)
		   (eq (first predicate) 'ACL2::LAMBDA)
		   (arglistp (second predicate))
		   (<= (len (second predicate)) 2)))
	  NIL)
	 (t (u::bomb 'DEFLIST "The DEFLIST predicate designator must either ~
                             be a symbol, or a 1 or 2-argument LAMBDA function, ~
                             but ~p0 is not." predicate)))))))

(defsection deflist
  :parents (data-structures)
  :short "Define a new list type, and a theory of the list type."
  :long "<p>Examples</p>

@({
  (deflist integer-listp (l)
    \"Recognizes true-lists of integers.\"
    integerp)

  (deflist bnatural-listp (l lub)
    \"Recognizes lists of naturals bounded by lub.\"
    (lambda (x) (bnaturalp x lub)))

  (deflist symbol-listp (l)
    \"Define a list theory for this function which is already defined by
      Acl2.\"
    symbolp
    (:options :omit-defun))

  (deflist stringp-listp (l)
    \"Recognizes lists of strings; produce a minimal theory, and store the NTH
     lemma as a :TYPE-PRESCRIPTION.\"
    stringp
    (:options (:theory nth put-nth) (:nth-rule-classes :type-prescription)))
})

<p>Syntax:</p>

@({
   DEFLIST name arglist [documentation] {declaration}* predicate [option-list]

   option-list ::= (:OPTIONS <<!options>>)

   options ::= !car-rule-classes-option |
               !nth-rule-classes-option |
               !omit-defun-option |
               !theory-option |
               !theory-name-option

   theory-name-option ::= (:THEORY-NAME theory-name)

   theory-option ::= (:THEORY <<!list-functions>>)

   list-functions ::= APPEND | BUTLAST | CONS | CAR | CDR |
                      FIRSTN | INITIAL-SUBLISTP-EQUAL | LAST |
                      MAKE-LIST | MEMBER-EQUAL | MEMBERP-EQUAL |
                      NTH | NTH-SEG | NTHCDR | PUT-NTH | PUT-SEG |
                      REMOVE-DUPLICATES-EQUAL | REMOVE-EQUAL |
                      REVERSE | SUBSEQ | UPDATE-NTH

   car-rule-classes-option ::= (:CAR-RULE-CLASSES rule-classes)

   nth-rule-classes-option ::= (:NTH-RULE-CLASSES rule-classes)

   omit-defun-option ::= :OMIT-DEFUN
})

<p>Arguments and Values:</p>

@({
   arglist -- an argument list satisfying ACL2::ARGLISTP, and containing
     exactly one symbol whose `print-name' is \"L\".

   declaration -- any valid declaration.

   documentation -- a string; not evaluated.

   name -- a symbol.

   predicate -- Either a symbol or a one argument LAMBDA function;
     designates a predicate to be applied to each element of the list.

   rule-classes -- any form legal as an argument to the :RULE-CLASSES keyword
    of DEFTHM.

   theory-name -- any symbol that is a legal name for a deftheory event.
})

<p>DEFLIST defines a recognizer for true lists whose elements all satisfy a
given predicate, and by default creates an extensive theory for lists of the
newly defined type.</p>

<p>To define a list type with DEFLIST you must supply a name for the
recognizer, an argument list, and predicate designator.  The name may be any
symbol.  The argument list must be valid as a functional argument list, and
must contain exactly 1 symbol whose `print-name'is \"L\".  By convention this
is the list argument recognized by the function defined by DEFLIST.</p>

<p>The DEFLIST recognizer will return T only if each element of L
satisfies (returns a non-NIL value) the given predicate, otherwise NIL.  If the
predicate is specified as a symbol, then this is assumed to be the function
symbol of a one argument function (or macro) with which to test the elements of
L.  If the predicate is specified as a single-argument LAMBDA function, then
the given LAMBDA function will be applied to test successive elements of L.</p>

<p>Any number of other arguments to the function may be supplied, but only the
L argument will change in the recursive structure of the recognizer.</p>

<p>Note that DEFLIST does not create any guards for L or any other argument.
Guards may be specified in the usual way since any number of DECLARE forms may
precede the predicate specification in the DEFLIST form.  DO NOT DECLARE GUARDS
FOR THE LIST ARGUMENT L, as this may cause DEFLIST to blindly generate
unprovable conjectures and unusable theorems.  Bear in mind that if you are
defining a function to be used as a guard, then you are advised to consider
what impact guarding the arguments of the function may have on its utility.  In
general the most useful guard functions are those that are guard-free.</p>

<p>Theory:</p>

<p>By default, DEFLIST creates an extensive theory for the recognized lists.
This theory contains appropriate lemmas for all of the list functions appearing
in the `list-functions' syntax description above.  This list of function
symbols is also available as the Acl2 constant *DEFLIST-THEORY-OPTIONS*.</p>

<p>One can select a subset of this theory to be generated by using the :THEORY
option (see below).  DEFLIST always creates a :FORWARD-CHAINING rule from the
recognizer to TRUE-LISTP.  DEFLIST also creates a DEFTHEORY event that lists
all of the lemmas created by the DEFLIST.  The name of the theory is formed by
concatenating the function name and the string \"-THEORY\", and interning the
resulting string in the package of the function name.</p>

<p>Options:</p>

<p>DEFLIST options are specified with a special :OPTIONS list systax.  If
present, the :OPTIONS list must appear as the last form in the body of the
DEFLIST.</p>

<dl>
<dt>:OMIT-DEFUN</dt>
<dd>If the :OMIT-DEFUN keyword is present then the definition will not be
    created.  Instead, only the list theory for the function is
    generated. Use this option to create a list theory for recognizers
    defined elsewhere.</dd>

<dt>:THEORY</dt>
<dd>This option is used to specify that only a subset of the list theory be
   created.  In the STRINGP-LISTP example above we specify that only lemmas
   about STRINGP-LISTP viz-a-viz NTH and PUT-NTH are to be generated.  By
   default the complete list theory for the recognizer is created.  If the
   option is given as (:THEORY) then the entire theory will be suppressed,
   except for the :FORWARD-CHAINING rule from the recognizer to TRUE-LISTP.</dd>

<dt>:THEORY-NAME</dt>
<dd>This option allows the user to define the name of the deftheory event
   that is automatically generated, and which includes the defthms that
   are generated.</dd>

<dt>:CAR-RULE-CLASSES</dt>
<dt>:NTH-RULE-CLASSES</dt>

<dd>These options specify a value for the :RULE-CLASSES keyword for the
   DEFTHM generated for the CAR and NTH element of a list recognized by the
   DEFLIST recognizer respectively.  The default is :REWRITE.</dd>
</dl>")

(defmacro deflist (name formals &rest body)
  (let*
    ((syntax-err (deflist-check-syntax name formals body))
     (last-form (car (last body)))
     (options? (and (>= (len body) 2)
                    (true-listp last-form)
                    (eq (car last-form) :OPTIONS)))
     (option-list (if options? (cdr last-form) nil))
     (predicate (if options?
                    (car (last (butlast body 1)))
                  last-form))
     ;;(l (nth (position-equal "L" (u::mapcar-string formals)) formals))
     (guard (u::get-guards-from-body body))
     (ctx 'DEFLIST)
     (option-err (u::get-option-check-syntax
                  ctx option-list *deflist-options* nil nil))
     (omit-defun (u::get-option-as-flag ctx :OMIT-DEFUN option-list))
     (theory (insert-dependencies
	      (u::get-option-subset
	       ctx :THEORY option-list
	       (strip-cars *deflist-theory-options*)
	       (strip-cars *deflist-theory-options*))
	      *deflist-theory-options*
	      nil))
     (theory-name (u::get-option-argument
		   ctx :THEORY-NAME option-list :FORM
		   (u::pack-intern name name "-THEORY") (u::pack-intern name name "-THEORY")))
     (car-rule-classes (u::get-option-argument
                        ctx :CAR-RULE-CLASSES option-list :FORM
			:REWRITE :REWRITE))
     (nth-rule-classes (u::get-option-argument
                        ctx :NTH-RULE-CLASSES option-list :FORM
			:REWRITE :REWRITE)))
    (or
     syntax-err				;Both better be NIL.
     option-err

     ;; We always generate the true-listp event.

     (let ((theory1 (union-equal '(true-listp) theory)))

       `(ENCAPSULATE ()

		     ;; We do the definition and proofs in a minimal theory for speed.
		     ;; The first label is for proofs that need the original theory.

		     (LOCAL (DEFLABEL DEFLIST-RESERVED-LABEL))
		     (LOCAL (IN-THEORY (THEORY 'MINIMAL-THEORY-FOR-DEFLIST)))

		     ,@(if omit-defun
			   nil
			 (list
			  `(DEFUN ,name ,formals
			     ,@(butlast body (if options? 2 1))
			     (COND
			      ((ATOM l) (eq l nil))
			      (T (AND (,predicate ,@(replace-equal 'l '(CAR l) formals))
				      (,name ,@(replace-equal 'l '(CDR l) formals))))))))

                     (LOCAL (IN-THEORY (ENABLE ,name)))

		     ,@(deflist-defthms
			 name formals predicate guard theory1
			 car-rule-classes nth-rule-classes)

		     (DEFTHEORY ,theory-name
		       ',(pack-intern-all-names name theory1))))

     )))

#|
Test Cases.

(trans1
 '(deflist integer-listp (l)
    "Recognizes true-lists of integers."
    integerp
    (:options (:car-rule-classes :type-prescription))))

(deflist integer-listp (l)
    "Recognizes true-lists of integers."
    integerp
    (:options :omit-defun
	      (:car-rule-classes :type-prescription)
	      (:nth-rule-classes :type-prescription)
	      (:theory append nthcdr)
	      ))

(deflist integer-listp (l)
    "Recognizes true-lists of integers."
    integerp
    (:options :omit-defun
	      (:car-rule-classes :type-prescription)
	      (:nth-rule-classes :type-prescription)
	      (:theory car nth)
	      (:theory-name integer-listp-theory2)))

(defmacro naturalp (n)
  `(and (integerp ,n) (<= 0 ,n)))

(trans1
 '(deflist natural-listp (l) naturalp
    (:options (:theory nth))))

(trans1
 '(deflist natural-listp (l) (lambda (x) (naturalp x))
    (:options (:theory nth))))

(deflist natural-listp (l) (lambda (x) (naturalp x))
  (:options (:theory nth)))

(trans1 '(deflist my-subset (l the-set)
  (declare (xargs :guard (eqlable-listp the-set)))
  (lambda (x) (member x the-set))))

(deflist my-subset (l the-set)
  (declare (xargs :guard (eqlable-listp the-set)))
  (lambda (x) (member x the-set)))

(defmacro bnaturalp (x lub)
  `(AND (naturalp ,x)
	(INTEGERP ,lub)
	(< ,x ,lub)))

(trans1
 '(deflist bnatural-listp (l lub) (lambda (x lub) (bnaturalp x lub))
    (:options (:theory nth))))

(trans1
 '(deflist bnatural-listp (l lub) bnaturalp
    (:options (:theory nth))))

(deflist bnatural-listp (l lub) bnaturalp
  (:options (:theory nth)))

(trans1
 '(deflist symbol-listp (l)
    "Define a list theory for this function which is already defined by
  Acl2."
    symbolp
    (:options :omit-defun (:nth-rule-classes :type-prescription))))

(deflist symbol-listp (l)
  "Define a list theory for this function which is already defined by
  Acl2."
  symbolp
  (:options :omit-defun (:theory put-nth) (:nth-rule-classes :type-prescription)))

(deflist stringp-listp (l)
  "Recognizes lists of strings ; produce a minimal theory, and store the NTH
  lemma as a :TYPE-PRESCRIPTION."
  stringp
  (:options (:theory nth put-nth) (:nth-rule-classes :type-prescription)))


; Errors:

(deflist l (u::l l)
  consp)

(deflist l (l cons)
  consp)

(deflist l (l)
  0)

(deflist l (l x)
  (lambda (x l) (cons x l)))

(deflist l (l x)
  (lambda (0) (cons x l)))

(deflist l (l)
  consp
  (:options (:theory foo)))

|#
