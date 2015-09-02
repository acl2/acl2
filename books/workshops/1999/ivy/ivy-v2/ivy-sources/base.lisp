(in-package "ACL2")

;; This book contains the core definitions of our first-order logic.
;; The main definitions are wff (well-formed formula) and feval
;; (evaluation in finite interpretations).  Look elsewhere for
;; comments on infinite interpretations.
;;
;; At the end is a simple example of a soundness proof.

(include-book "sets")
(include-book "../../../../../ordinals/e0-ordinal")
(set-well-founded-relation ACL2::e0-ord-<)

;(defmacro natp (n)
;    (list 'and (list 'integerp n) (list '<= 0 n)))

(defun fringe (x)
  (declare (xargs :guard t))
  (if (atom x)
      (list x)
      (append (fringe (car x)) (fringe (cdr x)))))

(defthm fringe-is-true-listp
  (true-listp (fringe x)))

(defun fassoc (x a)  ;; an unguarded version of assoc-equal
  (declare (xargs :guard t))
  (cond ((atom a) nil)
	((and (consp (car a))
	      (equal x (caar a))) (car a))
	(t (fassoc x (cdr a)))))

;; A variable is a symbolp.

(defun variable-term (x)
  (declare (xargs :guard t))
  (symbolp x))

;; A function symbol is a symbolp.

(defun function-symbol (x)
  (declare (xargs :guard t))
  (symbolp x))

;; Reserved logic symbols.  A relation symbol cannot be one of these.
;; This is mostly to keep users from writing confusing formulas.  For
;; example, 'and is binary; if a user writes a ternary 'and in a formula
;; context, it will be non-well-formed rather than an atomic formula.
;; (Note that one of these CAN be a function symbol.)

(defun logic-symbolp (x)
  (declare (xargs :guard t))
  (or (equal x 'true)
      (equal x 'false)
      (equal x 'and)
      (equal x 'or)
      (equal x 'not)
      (equal x 'imp)
      (equal x 'iff)
      (equal x 'all)
      (equal x 'exists)))

;; A relation symbol is a symbolp that is not a logic-symbolp.
;; This means that a relation symbol is also a function symbol.
;; Atomic formulas are distinguished from terms by context.

(defun relation-symbol (x)
  (declare (xargs :guard t))
  (and (symbolp x) (not (logic-symbolp x))))

;; Note: Arity-overloading is acceptable for function symbols
;; and relation symbols, and a symbol can serve as both a function
;; symbol and a relation symbol.
;;
;; We might have to be careful in a few places, because
;; (and (variable-term nil) (function-symbol nil) (relation-symbol nil)).

;; Macros a1 and a2 get the first and second arguments of a formula
;; (that is, the second and third members of a list).

(defmacro a1 (p)  ;; argument 1
  (list 'cadr p))

(defmacro a2 (p)  ;; argument 2
  (list 'caddr p))

;; These functions check for true lists of length 2 and 3.
;; I don't know if it would be better to use true-listp and len.

(defun list2p (l)
  (declare (xargs :guard t))
  (and (consp l) (consp (cdr l)) (null (cddr l))))

(defun list3p (l)
  (declare (xargs :guard t))
  (and (consp l) (list2p (cdr l))))

;;------------------------------------------------------
;; The following functions check if a formula has a particular type
;; and is well-formed at the top level.  Note that subformulas are
;; not checked for well-formedness here.  These are the official
;; functions, but they are slow.  For recursion through formulas,
;; it is usually much faster to use wfbinary, wfquant, below.

(defun wfnot (f)
  (declare (xargs :guard t))
  (and (list2p f) (equal (car f) 'not)))

(defun wfand (p)
  (declare (xargs :guard t))
  (and (list3p p) (equal (car p) 'and)))

(defun wfor  (p)
  (declare (xargs :guard t))
  (and (list3p p) (equal (car p) 'or)))

(defun wfimp (p)
  (declare (xargs :guard t))
  (and (list3p p) (equal (car p) 'imp)))

(defun wfiff (p)
  (declare (xargs :guard t))
  (and (list3p p) (equal (car p) 'iff)))

(defun wfall (p)
  (declare (xargs :guard t))
  (and (list3p p) (equal (car p) 'all) (variable-term (a1 p))))

(defun wfexists (p)
  (declare (xargs :guard t))
  (and (list3p p) (equal (car p) 'exists) (variable-term (a1 p))))

(defun wfatomtop (p)  ;; note different from wfatom below
  (declare (xargs :guard t))
  (and (consp p)
       (relation-symbol (car p))
       (true-listp (cdr p))))

;;--------------------------------------------
;; Using these instead of the preceding functions can really
;; speed up proofs, I think because list3p gets expanded a lot less.

(defun wfbinary (f)
  (declare (xargs :guard t))
  (and (list3p f)
       (or (equal (car f) 'and)
	   (equal (car f) 'or)
	   (equal (car f) 'imp)
	   (equal (car f) 'iff))))

(defun wfquant (f)
  (declare (xargs :guard t))
  (and (list3p f)
       (or (equal (car f) 'all)
	   (equal (car f) 'exists))
       (variable-term (a1 f))))

;; Wfeq recognizes a true-listp of len 3, with = as the first member.

(defun wfeq (a)
  (declare (xargs :guard t))
  (and (true-listp a) (equal (len a) 3) (equal (car a) '=)))

;; A wf-ap-term-top (well-formed application term top) is just
;; a true-listp with a function-symbol as the first member.

(defun wf-ap-term-top (tm)
  (declare (xargs :guard t))
  (and (consp tm)
       (function-symbol (car tm))
       (true-listp (cdr tm))))

;;=================================================================
;; In the general version, the encapsulation starts here.
;;=================================================================

;; A domain-term is a member of the domain of some interpretation.
;; Below, when we define well-formed term, we will allow domain-term
;; to be a well-formed term, because when we evaluate formulas in an
;; interpretation, we substitute domain-terms for free variables,
;; and we wish to retain well-formedness.
;;
;; A Side Note.  When we evaluate quantified formulas, we  immediately
;; substitute domain-terms for variables, then continue evaluating.
;; An alternative is to delay the substitution (by carrying an alist)
;; until we get down to variables.  We now think the alternative would
;; simplify things in several ways, for example, (1) there wouldn't be
;; any reason to make domain-terms be well-formed terms, and (2)
;; inductions on the evaluation functions would be simpler.
;; Big exercise: try it!
;;
;; A domain-term is a natural number.  (Function symbols, in particular
;; constant symbols, cannot be natural numbers, so they won't get
;; mixed up with domain-terms.)

(defun domain-term (e)
  (declare (xargs :guard t))
  (natp e))

(in-theory (disable domain-term))

;; -------------------------------------------------
;; Well-formed terms.  Note that a domain-term is a well-formed term.

(defun wft-list (l)
  (declare (xargs :guard t))
  (if (atom l)
      (null l)
    (and (or (variable-term (car l))
	     (domain-term (car l))
	     (and (consp (car l))
		  (function-symbol (caar l))
		  (wft-list (cdar l))))
	 (wft-list (cdr l)))))

(defmacro wft (x) ;; well-formed term
  (list 'wft-list (list 'list x)))

;;-------------------------------------------------
;; Formulas

;; Well-Formed Atomic Formula

(defun wfatom (a)
  (declare (xargs :guard t))
  (and (consp a)
       (relation-symbol (car a))
       (wft-list (cdr a))))

;; Well-Formed Formula

(defun wff (f)
  (declare (xargs :guard t))
  (cond ((equal f 'true) t)
	((equal f 'false) t)
	((wfatom f) t)
	((wfnot f) (wff (a1 f)))
	((wfbinary f) (and (wff (a1 f)) (wff (a2 f))))
	((wfquant f) (wff (a2 f)))
	(t nil)))

;;--------------------------------------------------------
;; Back to domain-terms.

(defun domain-term-list (l)
  (declare (xargs :guard t))
  (cond ((atom l) (null l))
	(t (and (domain-term (car l))
		(domain-term-list (cdr l))))))

(defthm domain-term-list-true-listp
  (implies (domain-term-list l)
	   (true-listp l)))

;; A domainp is the domain of some interpretation.
;; It is a binary tree whose fringe consists of domain-terms,
;; contains 0, and has no duplicates.
;; (Why not make it a list of domain-terms?  I think a binary
;; tree is more convenient, because domains are nonempty.)
;; (Why not make it a natp, say n, with domain elements 0, ..., n-1?)

(defun domainp (dom)
  (declare (xargs :guard t))
  (and (domain-term-list (fringe dom))
       (setp (fringe dom))
       (member-equal 0 (fringe dom))))

;; There are no recognizers for function, function-list, relation,
;; relation-list, or interpretation.  If something goes wrong
;; when evaluating a formula or term in an interpretation
;; (the interpretation is not well-formed or inadequate, the formula
;; is not well-formed or contains free variables)
;; default values are returned (nil for formulas, and 0 for terms).
;;
;; Apply a function to a tuple of domain-terms.

(defun fapply (f tuple)
  (declare (xargs :guard (domain-term-list tuple)))
  (if (and (fassoc tuple f)
	   (domain-term (cdr (fassoc tuple f))))
      (cdr (fassoc tuple f))
    0))

(defthm fapply-returns-domain-term
  (domain-term (fapply f tuple)))

;; Apply a relation to a tuple of domain-terms.

(defun rapply (r tuple)
  (declare (xargs :guard (domain-term-list tuple)))
  (and (fassoc tuple r)
       (equal (cdr (fassoc tuple r)) t)))  ;; note true iff t

(in-theory (disable fapply rapply))

;;------------------------------------------------------
;; Interpretation.  There is no recognizer.
;;
;; A "nice" interpretation (an undefined notion) will consist of
;; (domainp . (relation-list . function-list)).

;; Access functions for the 3 components of an interpretation.

(defun domain (i)
  (declare (xargs :guard t))
  (cond ((and (consp i) (domainp (car i))) (car i))
	(t 0)))

(defun relations (i)
  (declare (xargs :guard t))
  (cond ((and (consp i) (consp (cdr i))) (cadr i))
	(t nil)))

(defun functions (i)
  (declare (xargs :guard t))
  (cond ((and (consp i) (consp (cdr i))) (cddr i))
	(t nil)))

(defthm domain-is-domainp
  (domainp (domain i)))

(defthm fringe-of-domain-is-domain-term-list
  (domain-term-list (fringe (domain i))))

(defthm fringe-of-domain-contains-0
  (member-equal 0 (fringe (domain i))))

(in-theory (disable domain relations functions))

;;-------------------------------------------------
;; This section leads to the evaluation function.

;; Flookup takes a function-symbol, a tuple of domain-terms,
;; and an interpretation, and looks up the value of the function
;; for that tuple.  If anything goes wrong at the top level,
;; the default value 0 is returned.

(defun flookup (fsym tuple i)
  (declare (xargs :guard (and (function-symbol fsym)
			      (domain-term-list tuple))))
  (if (or (not (function-symbol fsym))
	  (not (domain-term-list tuple)))
      0  ;; default value
    (let ((sym-func (fassoc (cons fsym (len tuple)) (functions i))))
      (if (not (consp sym-func))
	  0  ;; function is not in function list
	(let ((val (fapply (cdr sym-func) tuple)))
	  (if (member-equal val (fringe (domain i)))
	      val
	    0  ;; function value is not in the domain
	    ))))))

(defthm flookup-returns-domain-term
  (domain-term (flookup func-sym tuple i)))

;; Eval-term-list takes a list of terms and an interpretation,
;; evaluates the terms, and returns a list of domain-terms.
;; If vars-in-term-list were defined at this point, it should
;; be in the guard.

(defun eval-term-list (l i)
  (declare (xargs :guard (wft-list l)
		  :verify-guards nil))
  (if (atom l)
      nil
    (cons (cond ((domain-term (car l))
		 (if (member-equal (car l) (fringe (domain i)))
		     (car l)
		   0)) ;; default value
		((variable-term (car l)) 0) ;; default value
		((wf-ap-term-top (car l))
		 (flookup (caar l) (eval-term-list (cdar l) i) i))
		(t 0))  ;; default value for non-term
	  (eval-term-list (cdr l) i))))

(defmacro eval-term (tm i)
  (list 'car (list 'eval-term-list (list 'list tm) i)))

(defthm eval-term-list-gives-domain-term-list
  (domain-term-list (eval-term-list l i)))

(verify-guards eval-term-list)

;; Rlookup takes a relation-symbol, a tuple of domain-terms, and an
;; interpretation, and looks up the value of the relation for that
;; tuple.  If anything goes wrong (at the top level), the default
;; value nil is returned.

(defun rlookup (rsym tuple i)
  (declare (xargs :guard (and (relation-symbol rsym)
			      (domain-term-list tuple))))
  (cond ((not (relation-symbol rsym)) nil)
	((not (domain-term-list tuple)) nil)
	((consp (fassoc (cons rsym (len tuple))
			(relations i)))
	 (rapply (cdr (fassoc (cons rsym (len tuple))
			      (relations i))) tuple))
	(t nil)))

(defthm wft-list-1  ;; for eval-atomic guard
  (implies (and (wft-list l)
		(consp l))
	   (wft-list (list (car l)))))

(defthm wft-list-2  ;; for eval-atomic guard
  (implies (wft-list (cons x y))
	   (wft-list (list x)))
  :hints (("Goal"
	   :use ((:instance wft-list-1 (l (cons x y)))))))

;; Eval-atomic evaluates an atomic formula in an interpretation.
;; Note that an equality atom is true iff the two arguments
;; evaluate to the same thing.  If free-vars were defined
;; at this point, it should be in the guard.

(defun eval-atomic (a i)
  (declare (xargs :guard (wfatom a)))
  (cond ((or (not (consp a))
	     (not (relation-symbol (car a)))
	     (not (true-listp (cdr a))))
	 nil)  ;; default value
	((wfeq a) (equal (eval-term (a1 a) i)
			 (eval-term (a2 a) i)))
	(t (rlookup (car a) (eval-term-list (cdr a) i) i))))

(in-theory (disable eval-atomic))  ;; Most soundness proofs don't need it.

;; Function subst-term-list substitutes a term for a variable
;; in a list of terms.

(defun subst-term-list (l v tm)
  (declare (xargs :guard (and (wft-list l) (variable-term v) (wft tm))))
  (if (atom l)
      l
    (cons (cond ((variable-term (car l)) (if (equal (car l) v)
					     tm
					   (car l)))
		((domain-term (car l)) (car l))
		((wf-ap-term-top (car l))
		 (cons (caar l) (subst-term-list (cdar l) v tm)))
		(t (car l)))  ;; leave non-term unchanged
	  (subst-term-list (cdr l) v tm))))

(defmacro subst-term (t1 x t2)
  (list 'car (list 'subst-term-list (list 'list t1) x t2)))

;; subst-term-list preserves true-listp and well-formedness.

(defthm subst-term-list-preserves-true-listp
  (equal (true-listp (subst-term-list l x tm))
	 (true-listp l)))

(defthm subst-term-list-wf
  (implies (and (wft-list l)
		(wft tm))
	   (wft-list (subst-term-list l v tm))))

;; Function subst-free substitutes a term for free
;; occurrences of a variable in a formula.

(defun subst-free (f v tm)
  (declare (xargs :guard (and (wff f)
			      (variable-term v)
			      (wft tm))))
  (cond ((wfnot f) (list 'not (subst-free (a1 f) v tm)))
	((wfbinary f) (list (car f)
			    (subst-free (a1 f) v tm)
			    (subst-free (a2 f) v tm)))
	((wfquant f) (if (equal (a1 f) v)
			 f
		       (list (car f)
			     (a1 f)
			     (subst-free (a2 f) v tm))))
	((wfatomtop f) (cons (car f) (subst-term-list (cdr f) v tm)))
	(t f)))

;; subst-free preserves well-formedness.

(defthm subst-free-wf
  (implies (and (wff f)
		(wft tm))
	   (wff (subst-free f v tm))))

;; Function wff-count counts the number of formula nodes in a formula.
;; It is useful for proving termination of functions (on formulas)
;; that change atomic formulas.

(defun wff-count (f)
  (declare (xargs :guard (wff f)))
  (cond ((wfnot f)    (+ 1 (wff-count (a1 f))))
	((wfbinary f) (+ 1 (wff-count (a1 f)) (wff-count (a2 f))))
	((wfquant f)  (+ 1 (wff-count (a2 f))))
	(t 1)))

;; subst-free preserves the wff-count of a formula.

(defthm subst-free-preserves-wff-count
  (equal (wff-count (subst-free f v e))
	 (wff-count f)))

(defthm domain-append-right  ;; for feval guard
  (implies (and (not (domain-term-list a))
		(true-listp a))
	   (not (domain-term-list (append a b)))))

(defthm domain-append-left  ;; for feval guard
  (implies (and (not (domain-term-list b))
		(true-listp b))
	   (not (domain-term-list (append a b)))))

(defthm domain-term-list-subset
  (implies (and (domain-term-list a)
		(true-listp b)
		(not (domain-term-list b)))
	   (not (subsetp-equal b a))))

(defthm domain-term-list-member
  (implies (and (domain-term-list a)
		(not (domain-term e)))
	   (not (member-equal e a))))

;; The Evaluation Function

;; There are 2 mutually recursive functions: (feval f i) evaluates
;; a formula in an interpretation, and when it gets to a quantified
;; subformula, it calls (feval-d f dom i), which recurses through the
;; domain of the interpretation, substituting elements and calling feval.
;;
;; It would be nice to have a guard (not (free-vars f)) on both of
;; these functions, but free-vars hasn't been defined yet.
;;
;; The termination measure has 3 components: the size of the formula,
;; the function (feval-d is smaller than feval), and the size of the
;; domain.  The second component is there because nothing gets smaller
;; when feval calls feval-d.

(mutual-recursion
 (defun feval (f i)  ;; recurse through formula
   (declare (xargs :measure (cons (cons (wff-count f) 2) 0)
                   :guard (wff f)))
   (cond ((equal f 'true) t)
         ((equal f 'false) nil)
         ((wfnot f) (not     (feval (a1 f) i)))
         ((wfand f) (and     (feval (a1 f) i) (feval (a2 f) i)))
         ((wfor  f) (or      (feval (a1 f) i) (feval (a2 f) i)))
         ((wfimp f) (implies (feval (a1 f) i) (feval (a2 f) i)))
         ((wfiff f) (iff     (feval (a1 f) i) (feval (a2 f) i)))
         ((wfquant f) (feval-d f (domain i) i))
         (t (eval-atomic f i))))

 (defun feval-d (f dom i)  ;; recurse through domain
   (declare (xargs :measure (cons (cons (wff-count f) 1)
                                  (acl2-count dom))
                   :guard (and (wff f)
                               (wfquant f)
			       ;; (domain-term-list (fringe dom))
                               (subsetp-equal (fringe dom)
                                              (fringe (domain i))))))
   (cond ((not (wfquant f)) nil) ;; default value
         ((atom dom) (feval (subst-free (a2 f) (a1 f) dom) i))
         ((wfall f)    (and (feval-d f (car dom) i)
                            (feval-d f (cdr dom) i)))
         ((wfexists f) (or  (feval-d f (car dom) i)
                            (feval-d f (cdr dom) i)))
         (t nil))) ;; default value
)

;; Notes about feval.  Because of the default values, some unexpected
;; things can happen if the formula being evaluated has free variables,
;; is not well formed, or is not fully interpreted.  For example,
;;
;; 1.  (FEVAL '(= X Y) i) for any i, will evaluate to T, because
;; all free variables evaluate to the default value 0.
;;
;; 2.  (FEVAL '(NOT (OR (P))) i), for any i, will evaluate to T,
;; because the '(OR (P)) is not a wff.
;;
;; Also, we must make sure that domain-terms are not thought of as
;; ordinary constants, because
;;
;; 3.  (FEVAL '(= 1 2) (cons '(0 1 . 2) anything)) is NIL.
;;
;; If the domain-terms are uninterpreted, they act like uninterpreted
;; constants:
;;
;; 4.  (FEVAL '(= 3 4) (cons '(0 1 . 2) anything)) is T.
;; 5.  (FEVAL '(= 3 4) nil) is T.
;; 6.  (FEVAL '(= (a) (b)) nil) is T.

;; A Side Note.  As a check of our handling of default
;; values, we could define a recognizer
;; (adequate-interpretation formula interp), which checks
;; if an interpretation is well-formed and interprets all
;; of the symbols in a formula, and also a function
;; (fix-interpretation formula interp) which makes an
;; interpretaion adequate for a formula.  Then, we should
;; be able to prove some theorems like
;;   (adequate-interpretation f (fix-interpretation f i)).
;; and
;;   (feval f i) = (feval f (fix-interpretation f i))
;; Big Exercise: try it.

;;=================================================================
;; In the general version, the encapsulation ends here.
;;=================================================================

;; A useful induction scheme for feval.  Note that this is not a direct
;; translation of feval/feval-d --- it has been simplified by using
;; wfbinary and wfquant, and by CONSing the recursive calls.

(defun feval-i (flg f dom i)
  (declare (xargs :measure (cons (cons (wff-count f) (if flg 2 1))
				 (acl2-count dom))
		  :guard (and (wff f)
			      (implies (not flg)
				       (domain-term-list (fringe dom))))
		  ))
  (if flg
      (cond ((wfnot f) (feval-i t (a1 f) 'junk i))
	    ((wfbinary f) (cons (feval-i t (a1 f) 'junk i)
				(feval-i t (a2 f) 'junk i)))
	    ((wfquant f) (feval-i nil f (domain i) i))
	    (t nil))
    (cond ((not (wfquant f)) nil)
	  ((atom dom) (feval-i t (subst-free (a2 f) (a1 f) dom) 'junk i))
	  (t (cons (feval-i nil f (car dom) i)
		   (feval-i nil f (cdr dom) i))))))

;; A scheme for inducting on domains.  This is useful for proving
;; feval properties about a quantifier at the top of a formula.

(defun dom-i (d)
  (declare (xargs :guard t))
  (if (atom d)
      nil
    (cons (dom-i (car d)) (dom-i (cdr d)))))

;;=================================================================
;; Here is a (useless) example of a transformation on formulas
;; and a soundness theorem for it.  This can serve as a template
;; for induction on the mutually rerecursive evaluation functions.

(defun simpt (f)  ;; this does a trivial simplification
  (declare (xargs :guard (wff f)))
  (cond ((wfand f) (if (equal (a1 f) 'true)
		       (simpt (a2 f))
		     (list 'and (simpt (a1 f)) (simpt (a2 f)))))
	((wfbinary f) (list (car f) (simpt (a1 f)) (simpt (a2 f))))
	((wfquant f) (list (car f) (a1 f) (simpt (a2 f))))
	((wfnot f) (list 'not (simpt (a1 f))))
	(t f)))

(defthm subst-free-true
  (implies (not (equal f 'true))
	   (not (equal (subst-free f x tm) 'true))))

(defthm simpt-subst
  (equal (simpt (subst-free f x tm))
	 (subst-free (simpt f) x tm)))

(defthm simpt-fsound-flg
  (if flg
      (equal (feval (simpt f) i)
	     (feval f i))
      (implies (wfquant f)
	       (equal (feval-d (simpt f) dom i)
		      (feval-d f dom i))))
  :hints (("Goal"
	   :induct (feval-i flg f dom i)
	   ))
  :rule-classes nil)

(defthm simpt-fsound
  (equal (feval (simpt f) i)
	 (feval f i))
  :hints (("Goal"
	   :by (:instance simpt-fsound-flg (flg t)))))
