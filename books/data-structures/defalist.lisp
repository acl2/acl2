; defalist.lisp - defining typed alists
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bill Bevier (bevier@cli.com) and Bishop Brock
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    defalist.lisp
;;;
;;;    A package for defining a recognizer for a typed alist. Rewrite
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

(in-package "ACL2")

(include-book "alist-defuns")
(include-book "list-defuns")
(include-book "utilities")

(encapsulate ((domain-elem-type (x) boolean)
	      (domain-type (l) boolean)
	      (range-elem-type (x) boolean)
	      (range-type (l) boolean)
	      (alist-type (a) boolean))
  (local (in-theory '(ground-zero)))
  (local (defun domain-elem-type (x)
	   (symbolp x)))
  (local (defun domain-type (l)
	   (symbol-listp l)))
  (local (defun range-elem-type (x)
	   (integerp x)))
  (local (defun range-type (l)
	   (integer-listp l)))
  (local (defun alist-type (a)
	   (cond ((atom a) (eq a nil))
		 (t (and (consp (car a))
			 (domain-elem-type (caar a))
			 (range-elem-type (cdar a))
			 (alist-type (cdr a)))))))
  (defthm domain-type-domain-elem-type
    (and (domain-type nil)
	 (equal (domain-type (cons x l))
		(and (domain-elem-type x)
		     (domain-type l)))))
  (defthm range-type-range-elem-type
    (and (range-type nil)
	 (equal (range-type (cons x l))
		(and (range-elem-type x)
		     (range-type l)))))
  (defthm alist-type-defun
    (iff (alist-type l)
	 (cond ((atom l) (eq l nil))
	       (t (and (consp (car l))
		       (domain-elem-type (caar l))
		       (range-elem-type (cdar l))
		       (alist-type (cdr l))))))
    :rule-classes ((:rewrite :corollary
			     (implies (atom l)
				      (equal (alist-type l) (null l))))
		   (:rewrite :corollary
			     (equal (alist-type (cons x l))
				    (and (consp x)
					 (domain-elem-type (car x))
					 (range-elem-type (cdr x))
					 (alist-type l))))))
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
;
; alist-type-fn: a symbol that names a predicate which recognizes a typed alist
; dom-type-fn
; ran-type-fn
; dom-elem-type-fn
; ran-elem-type-fn
;
; formals:      the formal parameter list to alist-type-fn
;               We assume that the other type fns are unary predicates, either
;               symbols or lambda expressions.
;
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

(defmacro alist-type-alistp-lemma (alist-type-fn dom-type-fn
						 ran-type-fn
						 dom-elem-type-fn
						 ran-elem-type-fn
						 formals
						 &optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn
		   dom-elem-type-fn ran-elem-type-fn))
  `(implies ,(my-conjoin (my-conjuncts guard)
			 `((,alist-type-fn ,@formals)))
	    (alistp l)))

(defthm alist-type-alistp
  (alist-type-alistp-lemma alist-type domain-type range-type
			   domain-elem-type range-elem-type
			   (l))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct t)))

(in-theory (disable alist-type-alistp))

(defmacro alist-type-acons-lemma (alist-type-fn dom-type-fn
						ran-type-fn
						dom-elem-type-fn
						ran-elem-type-fn
						formals
						&optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn))
  (let* ((vars (u::unique-symbols 2 (intern-in-package-of-symbol "X" alist-type-fn) formals))
	 (var1 (car vars))
	 (var2 (cadr vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)
			     (,dom-elem-type-fn ,var1)
			     (,ran-elem-type-fn ,var2)))
	      (,alist-type-fn ,@(replace-equal 'l
					       `(acons ,var1 ,var2 l)
					       formals)))))

(defthm alist-type-acons
  (alist-type-acons-lemma alist-type domain-type range-type
			  domain-elem-type range-elem-type (l))
  :hints (("Goal" :do-not-induct t
	   :in-theory (enable alist-type-alistp acons))))

(defmacro alist-type-append-lemma  (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn dom-elem-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 2 (intern-in-package-of-symbol "L" alist-type-fn) formals))
	 (var1 (car vars))
	 (var2 (cadr vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@(replace-equal 'l var1 formals))
			     (,alist-type-fn ,@(replace-equal 'l var2 formals))))
	      (,alist-type-fn ,@(replace-equal 'l `(append ,var1 ,var2) formals)))))

(defthm alist-type-append
  (alist-type-append-lemma alist-type domain-type range-type
			   domain-elem-type range-elem-type (l))
  :hints (("Goal" :induct t)))

(defmacro alist-type-bind-equal-lemma (alist-type-fn dom-type-fn
					       ran-type-fn
					       dom-elem-type-fn
					       ran-elem-type-fn
					       formals
					       &optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn))
  (let* ((vars (u::unique-symbols 2 (intern-in-package-of-symbol "X" alist-type-fn) formals))
	 (var1 (car vars))
	 (var2 (cadr vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)
			     (,dom-elem-type-fn ,var1)
			     (,ran-elem-type-fn ,var2)))
	      (,alist-type-fn ,@(replace-equal 'l
					       `(bind-equal ,var1 ,var2 l)
					       formals)))))

(defthm alist-type-bind-equal
  (alist-type-bind-equal-lemma alist-type domain-type range-type
			 domain-elem-type range-elem-type (l))
  :hints (("Goal" :induct t)))

(defmacro alist-type-rembind-equal-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn dom-elem-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "X" alist-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)))
	      (,alist-type-fn ,@(replace-equal 'l `(rembind-equal ,var l) formals)))))

(defthm alist-type-rembind-equal
  (alist-type-rembind-equal-lemma alist-type domain-type range-type
			    domain-elem-type range-elem-type (l))
  :hints (("Goal" :induct t)))

(defmacro alist-type-pairlis$-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-elem-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 2 (intern-in-package-of-symbol "X" alist-type-fn) formals))
	 (var1 (car vars))
	 (var2 (cadr vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((true-listp ,var1)
			     (,dom-type-fn ,var1)
			     (,ran-type-fn ,var2)
			     (eql (len ,var1) (len ,var2))))
	      (,alist-type-fn ,@(replace-equal 'l
					       `(pairlis$ ,var1 ,var2)
					       formals)))))

(defthm alist-type-pairlis$
  (alist-type-pairlis$-lemma alist-type domain-type range-type
			     domain-elem-type range-elem-type (l))
  :hints (("Goal" :induct t)))

(defmacro alist-type-bind-all-equal-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-elem-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 3 (intern-in-package-of-symbol "L" alist-type-fn) formals))
	 (var1 (car vars))
	 (var2 (cadr vars))
	 (var3 (caddr vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,dom-type-fn ,@(replace-equal 'l var1 formals))
			     (,ran-type-fn ,@(replace-equal 'l var2 formals))
			     (,alist-type-fn ,@(replace-equal 'l var3 formals))))
	      (,alist-type-fn ,@(replace-equal 'l `(bind-all-equal ,var1 ,var2 ,var3) formals)))))

(defthm alist-type-bind-all-equal
  (alist-type-bind-all-equal-lemma alist-type domain-type range-type
			   domain-elem-type range-elem-type (l))
  :hints (("Goal" :induct t)))


(defmacro alist-type-domain-restrict-equal-lemma  (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn dom-elem-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "L" alist-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)))
	      (,alist-type-fn ,@(replace-equal 'l
					       `(domain-restrict-equal ,var l)
					       formals)))))

(defthm alist-type-domain-restrict-equal
  (alist-type-domain-restrict-equal-lemma alist-type domain-type range-type
				    domain-elem-type range-elem-type (l))
  :hints (("Goal" :induct t)))

(defmacro alist-type-rembind-all-equal-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn dom-elem-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "L" alist-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)))
	      (,alist-type-fn ,@(replace-equal 'l `(rembind-all-equal ,var l) formals)))))

(defthm alist-type-rembind-all-equal
  (alist-type-rembind-all-equal-lemma alist-type domain-type range-type
			    domain-elem-type range-elem-type (l))
  :hints (("Goal" :induct t)))

(defmacro alist-type-bind-pairs-equal-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn dom-elem-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "PAIRS" alist-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@(Replace-equal 'l var formals))
			     (,alist-type-fn ,@formals)))
	      (,alist-type-fn ,@(replace-equal 'l `(bind-pairs-equal ,var l) formals)))))

(defthm alist-type-bind-pairs-equal
  (alist-type-bind-pairs-equal-lemma alist-type domain-type range-type
			    domain-elem-type range-elem-type (l))
  :hints (("Goal" :induct t)))


(defmacro alist-type-assoc-equal-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "X" alist-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)
			     (not (,dom-elem-type-fn ,var))))
	      (not (assoc-equal ,var l)))))

(defthm alist-type-assoc-equal
  (alist-type-assoc-equal-lemma  alist-type domain-type range-type
		      domain-elem-type range-elem-type (l))
  :hints (("Goal" :in-theory (enable alist-type-alistp assoc-equal))))

(defmacro alist-type-bound?-equal-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "X" alist-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)
			     (not (,dom-elem-type-fn ,var))))
	      (not (bound?-equal ,var l)))))

(defthm alist-type-bound?-equal
  (alist-type-bound?-equal-lemma  alist-type domain-type range-type
		      domain-elem-type range-elem-type (l))
  :hints (("Goal" :in-theory (enable alist-type-alistp bound?-equal))))


(defmacro alist-type-all-bound?-equal-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore ran-type-fn dom-elem-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "X" alist-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)
			     (true-listp ,var)
			     (not (,dom-type-fn ,var))))
	      (not (all-bound?-equal ,var l)))))


(defthm alist-type-all-bound?-equal
  (alist-type-all-bound?-equal-lemma  alist-type domain-type range-type
		      domain-elem-type range-elem-type (l))
  :hints (("Goal" :in-theory (set-difference-theories (enable alist-type-alistp all-bound?-equal)
						      '(bound?-equal)))))

(defmacro alist-type-binding-equal-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn dom-elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "X" alist-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)
			     (bound?-equal ,var l)))
	      (,ran-elem-type-fn (binding-equal ,var l)))))

(defthm alist-type-binding-equal
  (alist-type-binding-equal-lemma alist-type domain-type range-type
			    domain-elem-type range-elem-type (l))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable alist-type-alistp binding-equal bound?-equal))))

(defmacro alist-type-cdr-assoc-equal-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-type-fn ran-type-fn dom-elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "X" alist-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)
			     (assoc-equal ,var l)))
	      (,ran-elem-type-fn (cdr (assoc-equal ,var l))))))

(defthm alist-type-cdr-assoc-equal
  (alist-type-cdr-assoc-equal-lemma alist-type domain-type range-type
			    domain-elem-type range-elem-type (l))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable alist-type-alistp assoc-equal bound?-equal))))

(defmacro alist-type-domain-lemma (alist-type-fn dom-type-fn
						 ran-type-fn
						 dom-elem-type-fn
						 ran-elem-type-fn
						 formals
						 &optional (guard 't))
  (declare (ignore ran-type-fn dom-elem-type-fn ran-elem-type-fn))
  `(implies ,(my-conjoin (my-conjuncts guard)
			 `((,alist-type-fn ,@formals)))
	    (,dom-type-fn (domain l))))

(defthm alist-type-domain
  (alist-type-domain-lemma  alist-type domain-type range-type
			    domain-elem-type range-elem-type (l))
  :hints (("Goal" :in-theory (enable alist-type-alistp domain))))

(defmacro alist-type-range-lemma (alist-type-fn dom-type-fn
						 ran-type-fn
						 dom-elem-type-fn
						 ran-elem-type-fn
						 formals
						 &optional (guard 't))
  (declare (ignore dom-type-fn dom-elem-type-fn ran-elem-type-fn))
  `(implies ,(my-conjoin (my-conjuncts guard)
			 `((,alist-type-fn ,@formals)))
	    (,ran-type-fn (range l))))

(defthm alist-type-range
  (alist-type-range-lemma   alist-type domain-type range-type
			    domain-elem-type range-elem-type (l))
  :hints (("Goal" :in-theory (enable alist-type-alistp range))))

(defmacro alist-type-collect-bound-equal-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore ran-type-fn dom-elem-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "X" alist-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)))
	      (,dom-type-fn ,@(replace-equal 'l `(collect-bound-equal ,var l) formals)))))

(defthm alist-type-collect-bound-equal
  (alist-type-collect-bound-equal-lemma  alist-type domain-type range-type
		      domain-elem-type range-elem-type (l))
  :hints (("Goal" :in-theory (set-difference-theories (enable alist-type-alistp collect-bound-equal)
						      '(bound?-equal)))))

(defmacro alist-type-all-bindings-equal-lemma (alist-type-fn dom-type-fn
						  ran-type-fn
						  dom-elem-type-fn
						  ran-elem-type-fn
						  formals
						  &optional (guard 't))
  (declare (ignore dom-type-fn dom-elem-type-fn ran-elem-type-fn))
  (let* ((vars (u::unique-symbols 1 (intern-in-package-of-symbol "X" alist-type-fn) formals))
	 (var (car vars)))
    `(implies ,(my-conjoin (my-conjuncts guard)
			   `((,alist-type-fn ,@formals)))
	      (,ran-type-fn ,@(replace-equal 'l `(all-bindings-equal ,var l) formals)))))

(defthm alist-type-all-bindings-equal
  (alist-type-all-bindings-equal-lemma  alist-type domain-type range-type
		      domain-elem-type range-elem-type (l))
  :hints (("Goal" :in-theory (set-difference-theories (enable alist-type-alistp all-bindings-equal)
						      '(bound?-equal binding-equal)))))

; ------------------------------------------------------------
; Typed ALists
; ------------------------------------------------------------

(defconst *defalist-true-fn* '(lambda (x) (declare (ignore x)) t)
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "The single-argument predicate that is always true."
|#)

(defconst *defalist-theory-options*
  '(acons alistp all-bindings-equal all-bound?-equal append assoc-equal
	  bind-all-equal bind-equal bind-pairs-equal binding-equal
	  bound?-equal collect-bound-equal domain domain-restrict-equal
	  pairlis$ range rembind-all-equal rembind-equal)
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "This list contains all of the symbols recognized as valid options for
   the DEFALIST :THEORY option."
|#)

(defun pack-intern-names (name1 name2)
  (u::pack-intern name1 name1 "-" name2))

(u::defloop pack-intern-all-names (name l)
	    (for ((x in l))
		 (collect (pack-intern-names name x))))

; DEFALIST-DEFTHMS.
; Generate a list of DEFTHM forms. These defthms explain
; the properties of standard list operations with
; respect to a typed list predicate.
; For arguments, see documentation for DEF-TYPED-LIST
; macro below.

(u::defloop defalist-defthms (alist-type-fn formals dom-elem-type-fn ran-elem-type-fn
					    dom-type-fn ran-type-fn guard theory binding-equal-rule-classes)
	    (declare (xargs :guard (and (symbolp alist-type-fn)
					(arglistp formals)
					(consp formals)
					(symbol-listp theory))
			    :mode :program))
	    (for ((fn in theory))
		 (append (let ((lemmaname (pack-intern-names alist-type-fn fn))
			       (lemma-macro-name (u::pack-intern alist-type-fn 'alist-type- fn '-lemma))
			       (rule-classes (case fn
					       (binding-equal binding-equal-rule-classes)
					       (alistp '(:forward-chaining))
					       (t '(:rewrite))))
			       (hints (if (or (consp (my-conjuncts guard))
					      (and (equal dom-type-fn *defalist-true-fn*)
						   (not (equal dom-elem-type-fn *defalist-true-fn*)))
					      (and (equal ran-type-fn *defalist-true-fn*)
						   (not (equal ran-elem-type-fn *defalist-true-fn*)))
					      (> (len formals) 1))
					  `(("Goal" :in-theory (enable ,fn ,@(if (eq fn 'binding-equal) '(bound?-equal) ()))))
					;; The functional instance of the domain and range element types are
					;; presented as lambda forms, since these may be defined as macros.
					(let ((domain-elem-type-instance (if (equal dom-elem-type-fn *defalist-true-fn*)
									     (remove-equal '(declare (ignore x)) dom-elem-type-fn)
									   (cond ((and (consp dom-elem-type-fn)
										       (eq (car dom-elem-type-fn) 'acl2::lambda))
										  dom-elem-type-fn)
										 (t `(lambda (x) (,dom-elem-type-fn x))))))
					      (domain-type-instance (if (equal dom-type-fn *defalist-true-fn*)
									(remove-equal '(declare (ignore x)) dom-type-fn)
								      dom-type-fn))
					      (range-elem-type-instance (if (equal ran-elem-type-fn *defalist-true-fn*)
									    (remove-equal '(declare (ignore x)) ran-elem-type-fn)
									  (cond ((and (consp ran-elem-type-fn)
										      (eq (car ran-elem-type-fn) 'acl2::lambda))
										 ran-elem-type-fn)
										(t `(lambda (x) (,ran-elem-type-fn x))))))
					      (range-type-instance (if (equal ran-type-fn *defalist-true-fn*)
								       (remove-equal '(declare (ignore x)) ran-type-fn)
								     ran-type-fn)))
					  `(("Goal" :do-not-induct t
					     :use  (:functional-instance
						    ,(u::pack-intern alist-type-fn 'alist-type- fn)
						    ;; In the case a type fn is (lambda (x) (declare (ignore x)) t)
						    ;; we have to remove the (declare (ignore x)) to make it a pseudo-lambda
						    ;; expression. See :doc lemma-instance.
						    (domain-elem-type ,domain-elem-type-instance)
						    (domain-type ,domain-type-instance)
						    (range-elem-type ,range-elem-type-instance)
						    (range-type ,range-type-instance)
						    (alist-type ,alist-type-fn))))))))
			   `((defthm ,lemmaname
			       (,lemma-macro-name ,alist-type-fn ,dom-type-fn ,ran-type-fn ,dom-elem-type-fn ,ran-elem-type-fn
						  ,formals ,guard)
			       :rule-classes ,rule-classes
			       :hints ,hints)
			     ;; When the fn is ASSOC-EQUAL, then we generate both the ASSOC-EQUAL and CDR-ASSOC-EQUAL lemmas.
			     ,@(if  (and (eq fn 'assoc-equal) (not (equal ran-elem-type-fn *defalist-true-fn*)))
				   `((defthm ,(pack-intern-names alist-type-fn (pack-intern-names 'cdr fn))
				      (,(u::pack-intern alist-type-fn 'alist-type-cdr-assoc-equal-lemma)
				       ,alist-type-fn ,dom-type-fn ,ran-type-fn ,dom-elem-type-fn ,ran-elem-type-fn ,formals ,guard)
				      :rule-classes ,binding-equal-rule-classes
				      :hints ,(subst (pack-intern-names 'alist-type (pack-intern-names 'cdr fn))
						     (u::pack-intern alist-type-fn 'alist-type- fn)
						     hints)))
				 nil))))))


(defconst *defalist-options* '(:BINDING-EQUAL-RULE-CLASSES :THEORY :OMIT-DEFUN :DOMAIN-TYPE :RANGE-TYPE :THEORY-NAME)
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "This list contains all of the  valid keyword options for DEFALIST."
|#)

(defconst *forward-chaining-elem-types*
  '(integerp rationalp complex-rationalp symbolp true-listp stringp characterp
	     alistp acl2-numberp
             #+:non-standard-analysis realp
             #+:non-standard-analysis complexp)
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "When a range element type recognizer is one of these, then BINDING-EQUAL-RULE-CLASSES
defaults to :forward-chaining, otherwise :rewrite."
|#)

(defun defalist-check-syntax (name formals body)
  "Return NIL if no errors, otherwise crash."
  (declare (xargs :mode :program))
  (cond
   ((not (symbolp name))
    (u::bomb 'DEFALIST "The function name must be a symbol, but ~p0 is not."
	     name))
   ((not (true-listp formals))
    (u::bomb 'DEFALIST "The argument list ~p0 is not a true list." formals))
   ((not (arglistp formals))
    (mv-let (elmt msg) (find-first-bad-arg formals)
      (u::bomb 'DEFALIST "The argument list ~p0 is not valid because the ~
                          element ~p1 ~@2." formals elmt msg)))
   ((let* ((formal-strings (u::mapcar-string formals))
	   (l-tail (member-equal "L" formal-strings))
	   (multiple-ls (member-equal "L" (cdr l-tail))))
      (or (not l-tail) multiple-ls))
    (u::bomb 'DEFALIST "The formal argument list to DEFALIST must be a valid ~
                       functional argument list that contains exactly 1 ~
                       symbol whose print-name is \"L\", but ~p0 is not."
	     formals))
   ((null body) (u::bomb 'DEFALIST "The function body is empty!"))
   (t (let* ((last-form (car (last body)))
	     (options? (and (>= (len body) 2)
			    (true-listp last-form)
			    (eq (car last-form) :OPTIONS)))
	     (predicate (if options?
			    (car (last (butlast body 1)))
			  last-form)))
	(cond
	 ((and (consp predicate)
	       (let ((d (car predicate))
		     (r (cdr predicate)))
		 (and (or (symbolp d)
			  (and (true-listp d)
			       (>= (len d) 3)
			       (eq (first d) 'ACL2::LAMBDA)
			       (arglistp (second d))
			       (equal (len (second d)) 1)))
		      (or (symbolp r)
			  (and (true-listp r)
			       (>= (len r) 3)
			       (eq (first r) 'ACL2::LAMBDA)
			       (arglistp (second r))
			       (equal (len (second r)) 1))))))
	  NIL)
	 (t (u::bomb 'DEFALIST "The DEFALIST predicate designator must be a ~
                             pair (d . r) where d is either a function symbol
                             or a 1-argument LAMBDA function, and r ~
                             is either a function symbol or a 1-argument
                             LAMBDA function. ~p0 does not satisfy this
                             requirement." predicate)))))))

(deftheory minimal-theory-for-defalist
  (union-theories
   (current-theory 'ground-zero)
   (current-theory 'alist-defuns)))

;; It is ok to avoid placing a type restriction on the domain or range of a defalist.
;; When a type is omitted, certain lemmas should be omitted from the generated theory.
;; This filter weeds out the theory elements that should be avoided in these cases.

(u::defloop filter-alist-theory (theory dom-elem-type-fn ran-elem-type-fn dom-type-fn ran-type-fn)
	    (for ((fn in theory))
		 (when (case fn
			 (binding-equal (not (equal ran-elem-type-fn *defalist-true-fn*)))
			 (bound?-equal (not (equal dom-elem-type-fn *defalist-true-fn*)))
			 (domain (not (equal dom-type-fn *defalist-true-fn*)))
			 (range (not (equal ran-type-fn *defalist-true-fn*)))
			 (pairlis$ (and (not (equal dom-type-fn *defalist-true-fn*))
					(not (equal ran-type-fn *defalist-true-fn*))))
			 (bind-all-equal (and (not (equal dom-type-fn *defalist-true-fn*))
					      (not (equal ran-type-fn *defalist-true-fn*))))
			 (all-bound?-equal (not (equal dom-type-fn *defalist-true-fn*)))
			 (collect-bound-equal (not (equal dom-type-fn *defalist-true-fn*)))
			 (all-bindings-equal (not (equal ran-type-fn *defalist-true-fn*)))
			 (t t))
		   (collect fn))))

(defsection defalist
  :parents (data-structures)
  :short "Define a new alist type, and a theory of the alist type."
  :long "Examples:

@({
  (defalist symbol-to-integer-alistp (l)
    \"Recognizes an alist mapping symbols to integers.\"
    (symbolp . integerp))

  (defalist symbol-to-bnatural-alistp (l lub)
    \"Recognizes an alists mapping symbols to  naturals bounded by lub.\"
    (symbolp . (lambda (x) (bnaturalp x lub))))

  (defalist symbol-alistp (l)
    \"Define an alist theory alists from an unspecified domain type to
     symbols.\"
    ((lambda (x) t) . symbolp)
    (:options :omit-defun (:range-type symbol-listp)))

  (defalist string-to-integer-alistp (l)
    \"Recognizes an alist mapping strings to integers. Produce a minimal
     theory, and store the BINDING-EQUAL lemma as a :TYPE-PRESCRIPTION.\"
    (stringp . integerp)
    (:options (:theory nth put) (:binding-equal-rule-classes :type-prescription)
              (:domain-type string-listp) (:range-type integer-listp)))
})

<p>Syntax:</p>

@({
   DEFALIST name arglist [documentation] {declaration}* type-pair [option-list]

   option-list ::= (:OPTIONS <<!options>>)

   options ::= !binding-equal-rule-classes-option |
               !omit-defun-option |
               !theory-option |
               !domain-type-option |
               !range-type-option |
               !theory-name-option

   theory-option ::= (:THEORY <<!alist-functions>>)

   theory-name-option ::= (:THEORY-NAME theory-name)

   alist-functions ::= acons | alistp | all-bindings-equal| all-bound?-equal | append |
                       assoc-equal | bind-all-equal | bind-equal | bind-pairs-equal |
                       binding-equal | bound?-equal | collect-bound-equal | domain |
                       domain-restrict-equal | pairlis$ | range | rembind-all-equal |
                       rembind-equal

   binding-equal-rule-classes-option ::= (:BINDING-EQUAL-RULE-CLASSES rule-classes)

   omit-defun-option ::= :OMIT-DEFUN
})

<p>Arguments and Values:</p>

@({
   arglist -- an argument list satisfying ACL2::ARGLISTP, and containing
     exactly one symbol whose `print-name' is \"L\".

   declaration -- any valid declaration.

   documentation -- a string; not evaluated.

   name -- a symbol.

   theory-name -- any symbol that is a legal name for a deftheory event.

   type-pair -- A pair (d . r) where d and r are either a function symbol
     or a one argument LAMBDA function or the constant T.
     d designates a predicate to be applied to each element of the domain
     of the alist, and r designates a predicate to be applied to each element
     of the range of the alist. T means no type restriction.

   rule-classes -- any form legal as an argument to the :RULE-CLASSES keyword
    of DEFTHM.

   Acl2-theory-expression -- Any legal Acl2 theory expression
})

<h3>Description:</h3>

<p>DEFALIST defines a recognizer for association lists whose pairs map
  keys of a given type to values of a given type, and by default creates
  an extensive theory for alists of the newly defined type.</p>

<p>To define an alist type with DEFALIST you must supply a name for the alist
  recognizer, an argument list for the recognizer, and predicate designator for
  elements of the alist's range. The name may be any symbol.  The argument list
  must be valid as a functional argument list, and must contain exactly one
  symbol whose `print-name'is \"L\".  By convention this is the alist argument
  recognized by the function defined by DEFALIST.</p>

<p>The type of the domain and range of the alist is given by a pair (d . r)
  where d identifies the type of an element of the alist's domain, and r
  specifies the type of an element of the alist's range. Either of these
  may be specified by a symbol which names a one-argument function (or macro)
  which tests the elements of the domain and range of L. Either of d and r may
  also be specified as a single-argument LAMBDA function. Finally, either of d
  and r may be specified as the constant t, indicating no type constraint.</p>

<p>Any number of other arguments to the alist functions may be supplied,
  but only the L argument will change in the recursive structure of the recognizer.</p>

<p>Note that DEFALIST does not create any guards for L or any other argument.
  Guards may be specified in the usual way since any number of DECLARE forms
  may preceed the predicate specification in the DEFALIST form.  Bear in mind
  that if you are defining a function to be used as a guard, then you are
  advised to consider what impact guarding the arguments of the function may
  have on its utility.  In general the most useful guard functions are those
  that are guard-free.</p>

<h3>Theory</h3>

<p>By default, DEFALIST creates an extensive theory for the recognized alists.
  This theory contains appropriate lemmas for all of the alist functions
  appearing in the `alist-functions' syntax description above.  One can select
  a subset of this theory to be generated by using the :THEORY option
  (see below).  DEFALIST always creates a :FORWARD-CHAINING rule from the
  recognizer to ALISTP.</p>

<p>DEFALIST also creates a DEFTHEORY event that lists all of the lemmas created
  by the DEFALIST.  The name of the theory is formed by concatenating the
  function name and the string \"-THEORY\", and INTERNing the resulting string
  in the package of the function name.</p>

<h3>Options</h3>

<p>DEFALIST options are specified with a special :OPTIONS list systax.  If
  present, the :OPTIONS list must appear as the last form in the body of the
  DEFALIST.</p>

<dl>
<dt>:OMIT-DEFUN</dt>
<dd>If the :OMIT-DEFUN keyword is present then the definition will not be
    created.  Instead, only the list theory for the function is
    generated. Use this option to create a list theory for recognizers
    defined elsewhere.</dd>

<dt>:THEORY</dt>
<dd>This option is used to specify that only a subset of the list theory be
   created.  In the STRINGP-LISTP example above we specify that only lemmas
   about STRINGP-LISTP viz-a-viz NTH and PUT are to be generated.  By default
   the complete list theory for the recognizer is created.  If the option is
   given as (:THEORY) then the entire theory will be suppressed,
   except for the :FORWARD-CHAINING rule from the recognizer to TRUE-LISTP.</dd>

<dt>:BINDING-EQUAL-RULE-CLASSES</dt>
<dd>This option specifies a value for the :RULE-CLASSES keyword for the
   DEFTHM generated for the BINDING-EQUAL function (and for CDRASSOC) applied to
   an alist recognized by the DEFALIST recognizer.  The default is :REWRITE.</dd>

<dt>:DOMAIN-TYPE</dt>
<dd>This option specifies a predicate that recognizes a list of domain elements.
   It may be either a symbol or LAMBDA form. If present, and when not prevented
   by a :THEORY specification, a rewrite rule for the type of the domain
   will be generated. A lemma will be generated to check the compatibility
   of the specified domain type and domain element type.</dd>

<dt>:RANGE-TYPE</dt>
<dd>This option specifies a predicate that recognizes a list of range elements.
   It may be either a symbol or LAMBDA form. If present, and when not prevented
   by a :THEORY specification, a rewrite rule for the type of the range
   will be generated.  A lemma will be generated to check the compatibility
   of the specified range type and domain element type.</dd>

<dt>:THEORY-NAME</dt>
<dd>This option allows the user to define the name of the deftheory event
   that is automatically generated, and which includes the defthms that
   are generated.</dd>
</dl>")

(defmacro defalist (name formals &rest body)
  (let*
    ((syntax-err (defalist-check-syntax name formals body))
     (last-form (car (last body)))
     (options? (and (>= (len body) 2)
                    (true-listp last-form)
                    (eq (car last-form) :OPTIONS)))
     (option-list (if options? (cdr last-form) nil))
     (type-pair (if options?
		    (car (last (butlast body 1)))
		  last-form))
     (dom-elemtype (if (eq (car type-pair) t)
		       *defalist-true-fn*
		     (car type-pair)))
     (ran-elemtype (if (eq (cdr type-pair) t)
		       *defalist-true-fn*
		     (cdr type-pair)))
     (l (nth (position-equal "L" (u::mapcar-string formals)) formals))
     (guard (u::get-guards-from-body body))
     (ctx 'DEFALIST)
     (option-err (u::get-option-check-syntax
                  ctx option-list *defalist-options* nil nil))
     (omit-defun (u::get-option-as-flag ctx :OMIT-DEFUN option-list))
     (theory (u::get-option-subset
              ctx :THEORY option-list
	      *defalist-theory-options* *defalist-theory-options*))
     (binding-equal-rule-classes (u::get-option-argument
			    ctx :BINDING-EQUAL-RULE-CLASSES option-list :FORM
			    :REWRITE :REWRITE))
     (domain-type (u::get-option-argument
		   ctx :DOMAIN-TYPE option-list :FORM
		   *defalist-true-fn*
		   *defalist-true-fn*))
     (range-type (u::get-option-argument
		  ctx :RANGE-TYPE option-list :FORM
		  *defalist-true-fn*
		  *defalist-true-fn*))
     (theory-name (u::get-option-argument
		   ctx :THEORY-NAME option-list :FORM
		   (u::pack-intern name name "-THEORY") (u::pack-intern name name "-THEORY")))
     )
    (or
     syntax-err				;Both better be NIL.
     option-err
     (and (equal dom-elemtype *defalist-true-fn*)
	  (not (equal domain-type *defalist-true-fn*)))
     (and (equal ran-elemtype *defalist-true-fn*)
	  (not (equal range-type *defalist-true-fn*)))

     ;; We always generate the alistp event.

     (let ((theory1
	    (union-equal '(alistp)
			 (filter-alist-theory theory dom-elemtype ran-elemtype domain-type range-type))))

       `(ENCAPSULATE ()

		     ;; We do the definition and proofs in a minimal theory for speed.
		     ;; The first label is for proofs that need the original theory.

		     (LOCAL (DEFLABEL DEFALIST-RESERVED-LABEL))

		     ,@(if omit-defun
			   nil
			 (list
			  `(DEFUN ,name ,formals
			     ,@(butlast body (if options? 2 1))
			     (COND ((ATOM ,l) (NULL ,l))
				   (T (AND (consp (CAR ,l))
					   (,dom-elemtype (caar ,l))
					   (,ran-elemtype (cdar ,l))
					   (,name ,@(replace-equal l `(CDR ,l) formals))))))
			  ))

		     ,@(defalist-defthms
			 name formals dom-elemtype ran-elemtype domain-type range-type
			 guard theory1 binding-equal-rule-classes)

		     (DEFTHEORY ,theory-name
		       ',(pack-intern-all-names name theory1))))
    )))

#|

Examples:

(defalist symbol-to-integer-alistp (l)
  "Recognizes an alist mapping symbols to integers."
  (symbolp . integerp)
  (:options (:domain-type symbol-listp)
	    (:range-type integer-listp)))

(defmacro naturalp (n)
  `(and (integerp ,n) (<= 0 ,n)))

(defun natural-listp (l)
  (if (atom l) t
    (and (naturalp (car l)) (natural-listp (cdr l)))))

(defalist symbol-to-natural-alistp (l)
  "Recognizes an alists mapping symbols to  naturals bounded by lub."
  (symbolp . naturalp)
  (:options (:domain-type symbol-listp)
	    (:range-type natural-listp)
	    (:theory binding-equal)
	    (:theory-name sym->nat-theory)))

(defalist string-to-integer-alistp (l)
  "Recognizes an alist mapping strings to integers. Produce a minimal
  theory, and store the BINDING-EQUAL lemma as a :TYPE-PRESCRIPTION."
  (stringp . integerp)
  (:options (:theory bind binding-equal bound?-equal)
	    (:binding-equal-rule-classes :type-prescription)
	    (:domain-type string-listp)
	    (:range-type integer-listp)))

(defalist symbol-alistp (l)
  "Define an alist theory for alists mapping symbols to an arbitrary range type."
  (symbolp . t)
  (:options :omit-defun (:domain-type symbol-listp)))

(defalist anything-to-integer-alistp (l)
  (t . integerp)
  (:options (:range-type integer-listp)
	    (:theory binding-equal)))

|#
