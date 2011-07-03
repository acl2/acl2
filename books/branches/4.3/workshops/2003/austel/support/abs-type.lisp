(in-package "ACL2")

#|
Events accompanying "Implementing abstract types in ACL2",
by Vernon Austel
|#

;; Events for the simple example concerning lists.
(defun listfix (x)
  (if (endp x)
     nil
    (cons (car x) (listfix (cdr x)))))

(defun list= (x y)
  (equal (listfix x) (listfix y)))

(defequiv list=)

(defthm listfix-listfix
  (equal (listfix (listfix x))
	 (listfix x)))

(defthm list=-listfix
  (list= (listfix x) x))

(defcong list= list= (cons x y) 2)
(defcong list= equal (car x) 1)

(defthm not-consp-list=-nil
 (implies (not (consp l))
	  (list= l nil))
 :rule-classes :forward-chaining)

(defthm listfix-append
  (equal (listfix (append x y))
	 (append (listfix x) (listfix y))))

(defcong list= list= (append x y) 1)
(defcong list= list= (append x y) 2)

(in-theory (disable list=))


(defthm list=-append-nil
  (list= (append l nil) l))




;; Events concerning the expression evaluation example.

;; the defcong-fix macro
(progn
  ;; don't use:  (defstub-equiv defcong-equiv2)
  ;; because this expands into a formula using x, y and z,
  ;; and this causes problems with variable capture in functional instantiation
  (encapsulate
   (((defcong-equiv2 * *) => *))

   (local (defun defcong-equiv2 (x y) (equal x y)))

   (defthm defcong-equiv2-is-an-equivalence
     (and (booleanp (defcong-equiv2 xxx yyy))
	  (defcong-equiv2 xxx xxx)
	  (implies (defcong-equiv2 xxx yyy)
		   (defcong-equiv2 yyy xxx))
	  (implies (and (defcong-equiv2 xxx yyy)
			(defcong-equiv2 yyy zzz))
		   (defcong-equiv2 xxx zzz)))
     :rule-classes (:equivalence))
   )


  (encapsulate
   (((defcong-equiv1-norm *) => *))

   (local (defun defcong-equiv1-norm (dummy-arg) (declare (ignore dummy-arg)) t))

   (defthm defcong-equiv1-norm-prop
     (equal (defcong-equiv1-norm (defcong-equiv1-norm xxx))
	    (defcong-equiv1-norm xxx)))
   )

  (defun defcong-equiv1 (the-value1 the-value2)
    (equal (defcong-equiv1-norm the-value1) (defcong-equiv1-norm the-value2)))
  (defequiv defcong-equiv1)


  (encapsulate
   (((defcong-norm-fn *) => *))

   (local (defun defcong-norm-fn (dummy-arg) (declare (ignore dummy-arg)) t))

   (defthm defcong-norm-fn-prop
     (defcong-equiv2
       (defcong-norm-fn (defcong-equiv1-norm xxx))
       (defcong-norm-fn xxx)))
   )


  (defcong defcong-equiv1 defcong-equiv2 (defcong-norm-fn xxx) 1
    :hints (("Goal" :in-theory (e/d (defcong-equiv1) (defcong-norm-fn-prop))
	     :use ((:instance defcong-norm-fn-prop)
		   (:instance defcong-norm-fn-prop (xxx xxx-equiv))))))


  (defmacro if-stable (&rest rest)
    `(if STABLE-UNDER-SIMPLIFICATIONP
	 ',rest
       nil))

  (progn
    (defthm character-listp-first-n-ac
      (implies (and (character-listp l) (character-listp ac)
		    (<= n (len l)))
	       (character-listp (first-n-ac n l ac)))
      :hints (("Goal" :expand (first-n-ac n nil ac))))

    (defthm character-listp-take
      (implies (and (character-listp l) (<= n (len l)))
	       (character-listp (take n l))))

    (in-theory (disable take))

    (defun symchop (sym)
      (declare (xargs :guard (symbolp sym)))
      (intern-in-package-of-symbol
       (coerce (butlast (coerce (symbol-name sym) 'LIST) 1) 'STRING)
       sym))
    )
  (defun symcat (sym suffix)
    (declare (xargs :guard (and (symbolp sym)
				(or (symbolp suffix)
				    (stringp suffix)))))
    (intern-in-package-of-symbol
     (concatenate 'STRING
		  (symbol-name sym)
		  (if (symbolp suffix)
		      (symbol-name suffix)
		    suffix))
     sym))

  (defun symchop (sym)
    (declare (xargs :guard (symbolp sym)))
    (intern-in-package-of-symbol
     (coerce (butlast (coerce (symbol-name sym) 'list)
		      1)
	     'string)
     sym))

  (defmacro defcong-fix (equiv1 equiv2 tm n &key (hints 'nil))
    (let ((defcong-equiv1-norm (symcat (symchop equiv1) 'fix))
	  (xxx (nth n tm)))
      `(defcong ,equiv1 ,equiv2 ,tm ,n
	 :hints (("Goal"
		  :use (:instance
			(:functional-instance
			 defcong-equiv1-implies-defcong-equiv2-defcong-norm-fn-1
			 (defcong-equiv2
			   ,equiv2)
			 (defcong-equiv1-norm
			   ,defcong-equiv1-norm)
			 (defcong-equiv1
			   (lambda (x y)
			     (equal (,defcong-equiv1-norm x) (,defcong-equiv1-norm y))))
			 (defcong-norm-fn
			   (lambda (,xxx)
			     ,tm)))
			(xxx ,xxx)
			(xxx-equiv ,(symcat xxx '-equiv)))
		  :expand (,equiv1 ,xxx ,(symcat xxx '-equiv)))
		 ,@hints


		 ;; left to itself, the prover will try induction on the
		 ;; original goal.
		 ;; that strategy fails.
		 ;; we have to make it pick just the one subgoal
		 ;; that needs induction.
		 ;; The particular subgoal varies, so we can't use
		 ;; a literal goalspec.
		 (if-stable :induct t)))))
  )


(defun expr-kind (expr)
  (cond ((symbolp expr) 'SYMBOL)
	((consp expr) 'BINOP)
	(t 'LIT)))

;; destructors
(defun binop-op (x)
  (if (equal (expr-kind x) 'BINOP)
      (cadr x)
    nil))

(defun binop-left (expr)
  (if (equal (expr-kind expr) 'BINOP)
      (caddr expr)
    nil))

(defun binop-right (expr)
  (if (equal (expr-kind expr) 'BINOP)
      (cadddr expr)
    nil))


;; constructors
(defun mk-binop (op left right)
  (list 'BINOP op left right))

(defun litfix (x)
  (ifix x))

;; fixer
(defun exprfix (expr)
  (let ((kind (expr-kind expr)))
      (case kind
	    (SYMBOL expr)

	    (LIT    (litfix expr))

	    (otherwise
	     (mk-binop (binop-op expr)
		       (exprfix (binop-left expr))
		       (exprfix (binop-right expr)))))))

(defun expr= (x y)
  (equal (exprfix x) (exprfix y)))

(defequiv expr=)


;; congruence rule for the "kind" function.
(defcong expr= equal (expr-kind expr) 1
  :hints (("Goal" :expand ((exprfix expr)
			   (exprfix expr-equiv)))))

;; distinguishing between different kinds can be a pain.
(defthm expr-kind-otherwise
  (implies (and (not (equal (expr-kind expr) 'lit))
		(not (equal (expr-kind expr) 'symbol)))
	   (iff (equal (expr-kind expr) 'binop)
		t)))
  
(defthm expr-kind-symbol
  (implies (equal (expr-kind expr) 'SYMBOL)
	   (symbolp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (expr-kind)))))

(defthm expr-kind-lit
  (implies (equal (expr-kind expr) 'LIT)
	   (not (consp expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (expr-kind)))))

(defthm expr-kind-otherwise-2
  (implies (and (not (equal (expr-kind expr) 'lit))
		(not (equal (expr-kind expr) 'symbol)))
	   (consp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (expr-kind)))))

(defthm expand-expr-kind
  (equal (expr-kind (mk-binop binop left right))
	 'BINOP)
  :hints (("Goal" :in-theory (e/d (expr-kind mk-binop)))))



;; congruences for destructors
(defcong expr= equal (binop-op expr) 1
  :hints (("Goal" :expand ((exprfix expr)
			   (exprfix expr-equiv)))))
  
(defcong expr= expr= (binop-left expr) 1)
(defcong expr= expr= (binop-right expr) 1)

(defcong expr= expr= (mk-binop bop left right) 2)
(defcong expr= expr= (mk-binop bop left right) 3)

(defthm exprfix-exprfix
  (equal (exprfix (exprfix expr))
	 (exprfix expr)))

(defthm expr=-exprfix
  (expr= (exprfix expr) expr))


;; measure lemmas for destructors
(defthm acl2-count-binop-left
  (implies (equal (expr-kind expr) 'BINOP)
	   (< (acl2-count (binop-left expr))
	      (acl2-count expr)))
  :rule-classes (:rewrite :linear))

(defthm acl2-count-binop-right
  (implies (equal (expr-kind expr) 'BINOP)
	   (< (acl2-count (binop-right expr))
	      (acl2-count expr)))
  :rule-classes (:rewrite :linear))

;; elimination rules for constructors
(defthm elim-binop
  (implies (equal (expr-kind expr) 'BINOP)
	   (expr= (mk-binop (binop-op expr)
			    (binop-left expr)
			    (binop-right expr))
		  expr))
  :rule-classes (:rewrite :elim))

;; These kinds of expansions are also handy
(defthm expand-binop-destructors
  (and (equal (binop-op    (mk-binop op left right)) op)
       (equal (binop-left  (mk-binop op left right)) left)
       (equal (binop-right (mk-binop op left right)) right)))

(defthm integerp-exprfix
  (equal (integerp (exprfix expr))
	 (and (not (symbolp expr))
	      (not (consp expr)))))


(deftheory expr-destructors
  '(binop-op binop-left binop-right))

(deftheory expr-constructors
  '(litfix mk-binop))

(in-theory (disable expr-kind))
(in-theory (disable expr=))
(in-theory (disable expr-destructors expr-constructors))





;; The first example function.
(defun free-vars (expr)
  (let ((kind (expr-kind expr)))
      (case kind
         (SYMBOL  (list expr))
         (LIT  nil)
         (t    (append (free-vars (binop-left expr))
                        (free-vars (binop-right expr)))))))

;; its associated expansion rule
(defthm expand-free-vars
  (and (implies (equal (expr-kind expr) 'SYMBOL)
		(equal (free-vars expr) (list expr)))
       
       (implies (equal (expr-kind expr) 'LIT)
		(equal (free-vars expr) nil))

       (equal (free-vars (litfix expr)) nil)
       
       (equal (free-vars (mk-binop op left right))
	      (append (free-vars left)
		      (free-vars right))))
  :hints (("Goal" :in-theory (e/d (expr-kind
				   expr-destructors expr-constructors)))))
  
;; Its congruence theorem
;; type:
;;	:trans1 (defcong-fix expr= equal (free-vars expr) 1)
;; at the ACL2 command prompt to see what it turns into
(defcong-fix expr= equal (free-vars expr) 1)


;; We shouldn't need this anymore, although we enable
;; it for the example inductive proof.
(in-theory (disable free-vars))


#| 
This shows what the congruence proof will look like
if fixing functions are not used to define the equivalence relation.

(defun expr=-2 (expr y)
  (let ((kind (expr-kind expr)))
    (and (equal (expr-kind y) kind)
	 (case kind
	       (SYMBOL (equal y expr)) 

	       (LIT    (equal (litfix expr) (litfix y)))

	       (otherwise
		(and (equal (binop-op expr)
			    (binop-op y))
		     (expr=-2 (binop-left expr)
			    (binop-left y))
		     (expr=-2 (binop-right expr)
			      (binop-right y))))))))


(defthm expr=-2-thm
 (iff (expr=-2 x y)
      (expr= x y))
  :hints (("Goal"
	   :expand ((exprfix x) (exprfix y))
	   :induct (expr=-2 x y)
	   :in-theory (e/d (expr= expr-kind
				   expr-destructors expr-constructors)))))

(defthm expr=-ind-pat T
  :rule-classes
  ((:induction
    :pattern (expr= x y)
    :condition t 
    :scheme (expr=-2 x y))))

(defcong expr= equal (free-vars expr) 1
  :hints (("Goal" :in-theory (e/d (free-vars)))
	  ("Subgoal *1/1" :expand (expr= expr expr-equiv))))
  
|#

;; The second example function
(defun eval-expr (expr env)
  (let ((kind (expr-kind expr)))
    (case kind
	  (SYMBOL  (cdr (assoc expr env)))
	  (LIT     (litfix expr))
	  (t       (+ (eval-expr (binop-left expr) env)
		      (eval-expr (binop-right expr) env))))))

(defthm expand-eval-expr
  (and (implies (equal (expr-kind expr) 'SYMBOL)
		(equal (eval-expr expr env) (cdr (assoc expr env))))

       (implies (equal (expr-kind expr) 'LIT)
		(equal (eval-expr expr env) (litfix expr)))

       (equal (eval-expr (litfix expr) env) (litfix expr))
       
       (equal (eval-expr (mk-binop op left right) env)
	      (+ (eval-expr left env)
		 (eval-expr right env))))
  :hints (("Goal" :in-theory (e/d (expr-destructors expr-constructors)))))

(defthm not-integerp-litfix
  (implies (not (integerp x))
	   (equal (litfix x) 0))
  :hints (("Goal" :in-theory (e/d (litfix)))))
  
(defcong-fix expr= equal (eval-expr expr env) 1)

(in-theory (disable eval-expr))

(defthm true-listp-free-vars
  (true-listp (free-vars expr))
  :hints (("Goal" :in-theory (e/d ((:induction free-vars))))))

(defthm consp-append
  (equal (consp (append x y))
	 (or (consp x) (consp y))))

(defthm env-irrelevant-using-induction
  (implies (not (consp (free-vars expr)))
	   (equal (eval-expr expr env)
		  (eval-expr expr nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (eval-expr free-vars)))))
 
 
;; The constraints for a simple induction on expr=
(encapsulate
 ((expr-induct (expr) t))

 (local (defun expr-induct (x) (declare (ignore x)) t))

 (defthm expr-induct-symbol
   (implies (equal (expr-kind expr) 'SYMBOL)
	    (expr-induct expr)))

 (defthm expr-induct-lit
   (expr-induct (litfix expr)))

 (defthm expr-induct-binop
   (implies (and (expr-induct left)
		 (expr-induct right))
	    (expr-induct (mk-binop binop left right))))

 (defcong expr= iff (expr-induct expr) 1)
 )



;; the proof that expr-induct is always true.
(encapsulate
 nil

 ;; basecases need extra help
 (local
  (defthm symbolp-expr-induct
    (implies (symbolp expr)
	     (expr-induct expr))
    :hints (("Goal" :in-theory (e/d (expr-kind) (expr-induct-symbol))
	     :use expr-induct-symbol))))

 (local
  (defthm integerp-expr-induct
    (implies (integerp expr)
	     (expr-induct expr))
    :hints (("Goal" :in-theory (e/d (litfix) (expr-induct-lit))
	     :use expr-induct-lit))))
 
 (local
  (defthmd expr-induct-thm-exprfix
    (expr-induct (exprfix expr))
    :hints (("Goal" :in-theory (e/d () (expr=-implies-iff-expr-induct-1))))))
  

 ;; Then we just allow the congruence rule to fire.
 (defthm expr-induct-thm
   (expr-induct expr)
   :hints (("Goal" :use expr-induct-thm-exprfix)))
 )

;; prove the same theorem as above using functional instantiation.
(defthm env-irrelevant
  (implies (not (consp (free-vars expr)))
	   (equal (eval-expr expr env)
		  (eval-expr expr nil)))
  :hints (("Goal" :use (:functional-instance
			expr-induct-thm
			(expr-induct
			 (lambda (expr)
			   (implies (not (consp (free-vars expr)))
				    (equal (eval-expr expr env)
					   (eval-expr expr nil)))))))))


(defmacro defexprthm (name tm)
  `(defthm ,name
     ,tm
     :hints (("Goal"
	      :do-not-induct t
	      :use (:instance
		    (:functional-instance
		     expr-induct-thm
		     (expr-induct (lambda (expr) ,tm))))))))

;; an easier way to do the same thing
;; (this event will be redundant)
(defexprthm env-irrelevant
  (implies (not (consp (free-vars expr)))
	   (equal (eval-expr expr env)
		  (eval-expr expr nil))))



;; all we know about this function is that it is an
;; equivalence relation.
(encapsulate
 ((expr-fn= (x y) t))

 (local (defun expr-fn= (x y) (equal x y)))

 (defequiv expr-fn=)
 )

;; these functions serve as placeholders for what
;; a particular function may do.
(encapsulate
 ((expr-symbol-fn (expr) t)
  (expr-lit-fn (expr) t)
  (expr-binop-fn (op left $left right $right) t))

 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)

 (local (defun expr-symbol-fn (expr) t))
 (local (defun expr-lit-fn (expr) t))
 (local (defun expr-binop-fn (op left $left right $right) t))
 
 (defcong expr=    expr-fn= (expr-lit-fn expr) 1)

 (defcong expr=    expr-fn= (expr-binop-fn op left $left right $right) 2)
 (defcong expr-fn= expr-fn= (expr-binop-fn op left $left right $right) 3)
 (defcong expr=    expr-fn= (expr-binop-fn op left $left right $right) 4)
 (defcong expr-fn= expr-fn= (expr-binop-fn op left $left right $right) 5)
 )

;; now define a "typical" function on expressions.
(defun expr-fn (expr)
    (let ((kind (expr-kind expr)))
      (case kind
         (SYMBOL  (expr-symbol-fn expr))
         (LIT  (expr-lit-fn expr))
         (t    (expr-binop-fn (binop-op expr)
			      (binop-left expr)
                              (expr-fn (binop-left expr))
			      (binop-right expr)
                              (expr-fn (binop-right expr)))))))

  
;; its corresponding expansion
(defthm expand-expr-fn
  (and (implies (equal (expr-kind expr) 'SYMBOL)
		(expr-fn= (expr-fn expr)
			  (expr-symbol-fn expr)))
       
       (implies (equal (expr-kind expr) 'LIT)
		(expr-fn= (expr-fn expr)
			  (expr-lit-fn expr)))

       (expr-fn= (expr-fn (litfix expr))
		 (expr-lit-fn (litfix expr)))
       
       (expr-fn= (expr-fn (mk-binop op left right))
		 (expr-binop-fn op
				left (expr-fn left)
				right (expr-fn right))))
  :hints (("Goal" :in-theory (e/d (expr-kind
				   expr-destructors expr-constructors)))))

;; and its congruence theorem
;; (similar to the proofs for free-vars and eval-expr)
(encapsulate
 nil
 (local
  (defthm expr-lit-lemma
    (implies (and (equal (expr-kind expr) 'LIT)
		  (not (integerp expr)))
	     (expr= expr 0))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (e/d (expr= expr-kind))))))

 (defcong-fix expr= expr-fn= (expr-fn expr) 1
   :hints ((if-stable
	    :in-theory (e/d (litfix) ((expr-fn)))
	    :expand (expr-fn (mk-binop bop (exprfix blt)
				       (exprfix brt))))))
 )

;; Writing macros like this gets old pretty fast.
(defun defexpr-fn (expr-fn args expr-fn=
			expr-symbol-fn
			expr-lit-fn
			expr-binop-fn)
  (declare (xargs :mode :program))
  `(progn
     ;; many variables in the BINOP case are unused.
     ;; ACL2 complains about this.
     ;; just kludge it for our example.
     (set-ignore-ok t)

     (defun ,expr-fn ,args
       (let ((kind (expr-kind expr)))
	 (case kind
	       (SYMBOL  ,expr-symbol-fn)
	       (LIT     ,expr-lit-fn)
	       (t    (let ((op (binop-op expr))
			   (left (binop-left expr))
			   ($left (,expr-fn (binop-left expr)
					    ,@(cdr args)))
			   (right (binop-right expr))
			   ($right (,expr-fn (binop-right expr)
					     ,@(cdr args))))
		       ,expr-binop-fn)))))

     (defthm ,(packn (list 'expand- expr-fn))
       (and (implies (equal (expr-kind expr) 'SYMBOL)
		     (,expr-fn= (,expr-fn ,@args)
			    ,expr-symbol-fn))
       
	    (implies (equal (expr-kind expr) 'LIT)
		     (,expr-fn= (,expr-fn ,@args)
			    ,expr-lit-fn))

	    (,expr-fn= (,expr-fn (litfix expr) ,@(cdr args))
		       (let ((expr (litfix expr)))
			 ,expr-lit-fn))
       
	    (,expr-fn= (,expr-fn (mk-binop op left right) ,@(cdr args))
		   (let (($left (,expr-fn left ,@(cdr args)))
			 ($right (,expr-fn right ,@(cdr args))))
		     ,expr-binop-fn)))
       :hints (("Goal"
	 :do-not-induct t
	 :use
	 (:functional-instance expand-expr-fn
			       (expr-fn
				;; because expr-fn may take more than one arg
				(lambda (expr)
				  (,expr-fn ,@args)))
			       (expr-fn= ,expr-fn=)
			       (expr-symbol-fn
				(lambda (expr)
				  ,expr-symbol-fn))
			       (expr-lit-fn
				(lambda (expr)
				  ,expr-lit-fn))
			       (expr-binop-fn
				(lambda (op left $left right $right)
				  ,expr-binop-fn))))))
  

     (defthm ,(packn (list 'expr=-implies- expr-fn= '- expr-fn '-1))
       (implies (expr= expr expr-equiv)
		(,expr-fn= (,expr-fn expr ,@(cdr args))
			   (,expr-fn expr-equiv ,@(cdr args))))
       :hints
       (("Goal"
	 :do-not-induct t
	 :use
	 ;; except for the theorem name,
	 ;; this functional instance is the same as the above
	 (:functional-instance expr=-implies-expr-fn=-expr-fn-1
			       (expr-fn
				;; because expr-fn may take more than one arg
				(lambda (expr)
				  (,expr-fn ,@args)))
			       (expr-fn= ,expr-fn=)
			       (expr-symbol-fn
				(lambda (expr)
				  ,expr-symbol-fn))
			       (expr-lit-fn
				(lambda (expr)
				  ,expr-lit-fn))
			       (expr-binop-fn
				(lambda (op left $left right $right)
				  ,expr-binop-fn)))))
       :rule-classes ((:congruence)))
     ))

;; This macro can be made much fancier,
;; with default arguments and so forth,
;; but this gives the general idea.
(defmacro defexpr (expr-fn args expr-fn=
			   &key symbol lit binop)
  (defexpr-fn expr-fn args expr-fn=
    symbol lit binop))




;; use the new macro to
;;   define the function
;;   generate its expansion theorem
;;   generate its congruence theorem
(defexpr variable-free (expr) equal
  :SYMBOL	nil
  :LIT		t
  :BINOP	(and $left $right))
  
;; not much we can say about this, actually...
(defexprthm variable-free-lemma
  (iff (variable-free expr)
       (not (consp (free-vars expr)))))

;; This would have problems if we constrained expr-symbol-fn above.
(defexpr expr-subst (expr sbst) expr=
  :SYMBOL	(if (assoc expr sbst)
		    (cdr (assoc expr sbst))
		  expr)
  :LIT		expr 
  :BINOP	(mk-binop op $left $right))

(defexprthm eval-expr-expr-subst-nil
  (equal (eval-expr (expr-subst expr nil) env)
	 (eval-expr expr env)))




;; This is curious, but probably not useful.
(defthm litfix-elim
  (implies (equal (expr-kind expr) 'LIT)
	   (expr= (litfix expr) expr))
  :rule-classes :elim
  :hints (("Goal" :in-theory (e/d (litfix expr= expr-kind)))))
 


