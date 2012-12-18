#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;;
;; A generic generalization routine
;;

(include-book "coi/symbol-fns/symbol-fns" :dir :system)
(include-book "coi/util/mv-nth" :dir :system)
(include-book "coi/gensym/gensym" :dir :system)

(local (include-book "coi/bags/top" :dir :system))
(local (include-book "coi/lists/set" :dir :system))

;; You may wrap terms that you wish to generalize with the
;; function (gensym::generalize term)

(defun gensym::generalize (x) x)

(defevaluator gensym::eval gensym::eval-list
  (
   (if a b c)
   (gensym::generalize x)
   )
  )

(in-theory (disable GENSYM::EVAL-CONSTRAINT-6))
(in-theory (disable GENSYM::EVAL-CONSTRAINT-7))

(defun pattern-match-rec (args terms alist)
  (declare (type (satisfies alistp) alist)
	   (xargs :verify-guards nil))
  (if (and (consp args)
	   (consp terms))
      (met ((hit alist)
	    (let ((pattern (car args))
		  (term    (car terms)))
	      (cond
	       ((symbolp pattern)
		(let ((hit (assoc pattern alist)))
		  (if (consp hit)
		      (if (equal (cdr hit) term)
			  (mv t alist)
			(mv nil nil))
		    (mv t (cons (cons pattern term) alist)))))
	       ((consp pattern)
		(cond
		 ((and (consp term) (not (equal (car term) 'quote)))
		  (let ((pfn   (car pattern))
			(pargs (cdr pattern))
			(tfn   (car term))
			(targs (cdr term)))
		    (if (equal pfn tfn)
			(pattern-match-rec pargs targs alist)
		      (mv nil nil))))
		 (t (mv nil nil))))
	       (t
		(mv nil nil)))))
	(if hit (pattern-match-rec (cdr args) (cdr terms) alist)
	  (mv nil nil)))
    (if (and (null args) (null terms))
	(mv t alist)
      (mv nil nil))))

(defthm alistp-pattern-match-rec
  (implies
   (alistp alist)
   (alistp (v1 (pattern-match-rec args terms alist)))))

(verify-guards pattern-match-rec)

(defun clause-keys (clauses)
  (declare (type t clauses)
	   (xargs :Verify-guards nil))
  (if (consp clauses)
      (let ((clause (car clauses)))
	(cond
	 ((symbolp clause)
	  (cons clause (clause-keys (cdr clauses))))
	 ((atom clause)
	  (clause-keys (cdr clauses)))
	 ((eq (car clause) 'quote)
	  (clause-keys (cdr clauses)))
	 ((consp (car clause))
	  (append (clause-keys (cdr clause))
		  (clause-keys (cdr clauses))))
	 (t
	  (append (clause-keys (cdr clause))
		  (clause-keys (cdr clauses))))))
    nil))

(defthm true-listp-clause-keys
  (true-listp (clause-keys clauses)))

(verify-guards clause-keys)

(defthm not-member-key-clause-keys-reduction
  (implies
   (and
    (consp a)
    (pseudo-term-listp clauses)
    (not (bag::memberp (caar a) (clause-keys clauses))))
   (equal (gensym::eval-list clauses a)
	  (gensym::eval-list clauses (cdr a))))
  :hints (("Goal" :in-theory (enable PSEUDO-TERMP pseudo-term-listp)
	   :induct (clause-keys clauses))
	  (and stable-under-simplificationp
	       '(:in-theory (enable GENSYM::EVAL-CONSTRAINT-0)))))

(defun term-keys (term)
  (declare (type t term))
  (cond
   ((symbolp term)
    (list term))
   ((atom term)
    nil)
   ((eq (car term) 'quote)
    nil)
   ((consp (car term))
    (clause-keys (cdr term)))
   (t
    (clause-keys (cdr term)))))

(defthm not-member-key-term-keys-reduction
  (implies
   (and
    (consp a)
    (pseudo-termp term)
    (not (bag::memberp (caar a) (term-keys term))))
   (equal (gensym::eval term a)
	  (gensym::eval term (cdr a))))
  :hints (("Goal" :in-theory (enable GENSYM::EVAL-CONSTRAINT-0 pseudo-termp))))

(in-theory (disable term-keys))

(defun pattern-match-list (list terms)
  (declare (type t list terms))
  (if (and (consp list) (consp (car list)))
      (let ((pattern (caar list))
	    (type-p  (cdar list)))
	(met ((hit alist) (pattern-match-rec pattern terms nil))
	     (declare (ignore alist))
	     (if hit (mv terms type-p)
	       (pattern-match-list (cdr list) terms))))
    (mv nil nil)))

(defun pattern-match-args (fn args terms)
  (declare (type t fn args terms))
  (if (consp terms)
      (let ((term (car terms)))
	(cond
	 ((atom term)
	  (pattern-match-args fn args (cdr terms)))
	 ((eq (car term) 'quote)
	  (pattern-match-args fn args (cdr terms)))
	 ((consp (car term))
	  (or
	   (pattern-match-args fn args (cdr term))
	   (pattern-match-args fn args (cdr terms))))
	 (t
	  (or (and (equal fn (car term))
		   (met ((subterm type-p) (pattern-match-list args (cdr term)))
			(and subterm (cons (cons fn subterm) type-p))))
	      (pattern-match-args fn args (cdr term))
	      (pattern-match-args fn args (cdr terms))))))
    nil))

#+joe
(defthm pseudo-termp-pattern-match
  (implies
   (pseudo-term-listp terms)
   (pseudo-termp (pattern-match-args fn args terms))))

(defun replace-common-subterm (subterm var terms)
  (declare (type t subterm var terms))
  (if (consp terms)
      (let ((term (car terms)))
	(if (equal term subterm)
	    (cons var (replace-common-subterm subterm var (cdr terms)))
	  (cond
	   ((atom term)
	    (cons term (replace-common-subterm subterm var (cdr terms))))
	   ((eq (car term) 'quote)
	    (cons term (replace-common-subterm subterm var (cdr terms))))
	   ((consp (car term))
	    (cons (cons (car term) (replace-common-subterm subterm var (cdr term)))
		  (replace-common-subterm subterm var (cdr terms))))
	   (t
	    (cons (cons (car term) (replace-common-subterm subterm var (cdr term)))
		  (replace-common-subterm subterm var (cdr terms)))))))
    nil))

(defthm len-replace-common-subterm
  (equal (len (replace-common-subterm suterm var list))
	 (len list)))

(defthm pseudo-termp-listp-replace-common-subterm
  (implies 
   (and
    (pseudo-termp var)
    (pseudo-term-listp clauses))
   (pseudo-term-listp (replace-common-subterm subterm var clauses)))
  :hints (("Goal" :in-theory (enable pseudo-termp
				     pseudo-term-listp))))

(defthm generic-replace-common-subterm-reduction
  (implies
   (and
    var
    (symbolp var)
    (equal (cdr (assoc-eq var a)) (gensym::eval subterm a)))
   (equal (gensym::eval-list (replace-common-subterm subterm var terms) a)
	  (gensym::eval-list terms a)))
  :hints ((and stable-under-simplificationp
	       '(:in-theory (enable GENSYM::EVAL-CONSTRAINT-0)))
	  ("Goal" :induct (replace-common-subterm subterm var terms))))

(local
 (defthm non-membership-from-non-memberp-superset-free
   (implies
    (and
     (not (list::memberp a x))
     (list::subsetp y x))
    (not (list::memberp a y))))
 )

(local
 (defthm subsetp-term-append-term
   (list::subsetp term (append term x)))
 )

(local
 (defthm subsetp-x-append-term-x
   (list::subsetp x (append term x)))
 )

(defun generalization-symbol-base (subterm)
  (declare (type t subterm))
  (if (and (consp subterm)
	   (consp (cdr subterm))
	   (consp (cadr subterm)))
      (let ((symbol (caadr subterm)))
	(if (symbolp symbol) symbol `gensym::||))
    `gensym::||))

(defun generalize-clause-processor (clause subterm)
  (declare (type t clause subterm))
  (if (consp subterm)
      (let ((fn (generalization-symbol-base subterm)))
	(let ((avoid (append (term-keys subterm) (clause-keys clause))))
	  (let ((var (gensym::gensym fn avoid)))
	    (if (not var) (mv nil nil)
	      (mv var (replace-common-subterm subterm var clause))))))
    (mv nil nil)))

(defun generalize-clause-alist (clause a subterm)
  (declare (type t clause subterm))
  (if (consp subterm)
      (let ((fn (generalization-symbol-base subterm)))
	(let ((avoid (append (term-keys subterm) (clause-keys clause))))
	  (let ((var (gensym::gensym fn avoid)))
	    (if (not var) a
	      (cons (cons var (gensym::eval subterm a)) a)))))
    a))

(defthm eval-v0-generalize-clause-processor
  (implies
   (and
    (v0 (generalize-clause-processor clause subterm))
    (pseudo-termp subterm))
   (equal (gensym::eval (v0 (generalize-clause-processor clause subterm)) (GENERALIZE-CLAUSE-ALIST clause A subterm))
	  (gensym::eval subterm a))))

(defthm eval-subterm-GENERALIZE-CLAUSE-ALIST
  (implies
   (and
    (v0 (generalize-clause-processor clause subterm))
    (pseudo-termp subterm)
    (pseudo-termp term)
    (list::subsetp (term-keys term) (append (term-keys subterm) (clause-keys clause))))
   (equal (gensym::eval term (GENERALIZE-CLAUSE-ALIST clause A subterm))
	  (gensym::eval term a)))
  :hints (("Goal" :in-theory (disable LIST::SUBSETP-APPEND-2))))


(defthm generalize-clause-processor-reduction
  (implies
   (and
    (pseudo-term-listp clause)
    (pseudo-termp subterm)
    (v0 (generalize-clause-processor clause subterm)))
   (equal (gensym::eval-list (v1 (generalize-clause-processor clause subterm))
			     (generalize-clause-alist clause a subterm))
	  (gensym::eval-list clause a))))
  
(defthm generalize-clause-alist-reduction
  (implies
   (and
    (pseudo-term-listp clause)
    (pseudo-termp subterm))
   (equal (gensym::eval-list clause (generalize-clause-alist clause a subterm))
	  (gensym::eval-list clause a))))
  
(in-theory (disable generalize-clause-processor generalize-clause-alist))

(in-theory (enable GENSYM::EVAL-CONSTRAINT-6))
(in-theory (enable GENSYM::EVAL-CONSTRAINT-7))

(include-book "coi/util/clause-processor" :dir :system)

;;(conjoin-disjoin gensym::eval gensym::eval-list)
(clause-eval-facts gensym::eval gensym::eval-list)

(defthmd disjoin-congruence
  (implies
   (equal (gensym::eval-list args1 a1) 
	  (gensym::eval-list args2 a2))
   (iff (iff (gensym::eval (disjoin args1) a1)
	     (gensym::eval (disjoin args2) a2)) t))
  :hints (("Goal" :expand ((disjoin args2)
			   (disjoin args1))
	   :induct (list::len-len-induction args1 args2))))

;;
;; This may be generally useful .. push back into clause-processor?
;;

(defthm disjoin-implication
  (implies
   (and
    (equal (gensym::eval-list args1 a1)
	   (gensym::eval-list args2 a2))
    (gensym::eval (disjoin args1) a1))
   (gensym::eval (disjoin args2) a2))
  :hints (("Goal" :use disjoin-congruence)))

#|
(defthm disjoin2-congruence-1
  (implies
   (and
    (gensym::eval (disjoin2 w x) a1)
    (iff (gensym::eval w a1) (gensym::eval y a2))
    (iff (gensym::eval x a1) (gensym::eval z a2)))
   (gensym::eval (disjoin2 y z) a2)))

(defthm disjoin2-congruence-2
  (implies
   (and
    (not (gensym::eval (disjoin2 w x) a1))
    (iff (gensym::eval w a1) (gensym::eval y a2))
    (iff (gensym::eval x a1) (gensym::eval z a2)))
   (not (gensym::eval (disjoin2 y z) a2))))

(local (in-theory (disable disjoin2)))

(defthm disjoin2-ite-reduction
  (implies
   (and
    (consp ite)
    (equal (car ite) 'if))
   (iff (gensym::eval (disjoin2 ite x) a)
	(if (gensym::eval (cadr ite) a)
	    (gensym::eval (disjoin2 (caddr ite) x) a)
	  (gensym::eval (disjoin2 (cadddr ite) x) a))))
  :hints (("Goal" :in-theory (enable disjoin2))))

(in-theory (disable conjoin2))

(defthm eval-conjoin2
  (iff (gensym::eval (conjoin2 x y) a)
       (and (gensym::eval x a)
	    (gensym::eval y a)))
  :hints (("Goal" :in-theory (enable conjoin2))))

(defthm eval-disjoin2
  (iff (gensym::eval (disjoin2 x y) a)
       (or (gensym::eval x a)
	   (gensym::eval y a)))
  :hints (("Goal" :in-theory (enable disjoin2))))
|#

(defun generalize-termp (term)
  (declare (type t term))
  (and (pseudo-termp term)
       (consp term)
       (consp (cdr term))
       (null (cddr term))
       (equal (car term) 'gensym::generalize)))

(defun generalize-clause-processor-wrapper (clause hint)
  (declare (type t clause hint))
  (if (consp hint)
      (let ((subterm (car hint))
	    (type-p  (cdr hint)))
	(met ((var new) (generalize-clause-processor clause subterm))
	     (if (and (generalize-termp subterm) (symbolp type-p) (not (equal type-p 'quote)) var)
		 (if type-p
		     (list
		      (cons `(if (,type-p ,(cadr subterm)) ,*t* ,*nil*) new)
		      (cons `(if (,type-p ,var) ,*nil* ,*t*) new)
		      )
		   (list new))
	       (list clause))))
    (list clause)))

(defun generalize-clause-alist-wrapper (clause a hint)
  (declare (type t clause hint))
  (if (consp hint)
      (let ((subterm (car hint))
	    (type-p  (cdr hint)))
	(met ((var new) (generalize-clause-processor clause subterm))
	     (declare (ignore new))
	     (if (and (generalize-termp subterm) (symbolp type-p) (not (equal type-p 'quote)) var) 
		 (generalize-clause-alist clause a subterm)
	       a)))
    a))

(defthm term-keys-generalize-termp
  (implies
   (generalize-termp subterm)
   (equal (term-keys subterm)
	  (clause-keys (cdr subterm))))
  :hints (("Goal" :in-theory (enable CLAUSE-KEYS term-keys))))

(defthm open-clause-keys
  (implies
   (and
    (syntaxp (not (symbolp terms)))
    (consp terms))
   (equal (clause-keys terms)
	  (append (term-keys (car terms))
		  (clause-keys (cdr terms)))))
  :hints (("Goal" :in-theory (enable term-keys clause-keys))))

(defthm clause-keys-null
  (implies
   (not (consp terms))
   (equal (clause-keys terms) nil))
  :hints (("Goal" :in-theory (enable term-keys clause-keys))))


(defthm generalize-clause-processor-works
  (implies
   (and
    (pseudo-term-listp cl)
    (alistp a)
    (gensym::eval (conjoin-clauses (generalize-clause-processor-wrapper cl hint))
	      (generalize-clause-alist-wrapper cl a hint)))
   (gensym::eval (disjoin cl) a))
  :hints (("Goal" :do-not-induct t
	   :do-not '(eliminate-destructors generalize)
	   :in-theory (e/d (pseudo-termp pseudo-term-listp GENSYM::EVAL-CONSTRAINT-0)
			   (LIST::SUBSETP-APPEND-2))
	   :use ((:instance disjoin-implication
			    (args1 cl)
			    (a1    (generalize-clause-alist cl a (car hint)))
			    (args2 cl)
			    (a2    a))
		 (:instance disjoin-implication
			    (args1 (val 1 (generalize-clause-processor cl (car hint))))
			    (a1    (generalize-clause-alist cl a (car hint)))
			    (args2 cl)
			    (a2    a)))))
  :rule-classes :clause-processor)

(defun get-generalization-patterns (world)
  (declare (xargs :guard (and (plist-worldp world)
                              (alistp (table-alist 'generalization world)))))
  (cdr (assoc-eq :patterns (table-alist 'generalization world))))

(defun generalize-pattern-hint (patterns clause)
  (declare (xargs :mode :program))
  (let ((hint (pattern-match-args 'gensym::generalize patterns clause)))
    (and hint
	 (let ((hints `(:clause-processor (generalize-clause-processor-wrapper clause ',hint))))
	   `(:computed-hint-replacement 
	     ((generalize-clause-hint id clause world))
	     ,@hints)))))

(defun generalize-clause-hint (id clause world)
  (declare (xargs :mode :program)
	   (ignore id))
  (or (generalize-pattern-hint (get-generalization-patterns world) clause)
      nil))

(add-default-hints!
 '((generalize-clause-hint id clause world)))

(defmacro add-generalization-pattern (pattern &key (type 'nil))
  `(table generalization :patterns
	  (cons ',(cons `(,pattern) type)
		(cdr (assoc :patterns (table-alist 'generalization world))))))

;; Can we add a fixing function to the mix?  Create a new symbol and apply the
;; fixing function?
;;
;;(add-generalization-pattern (foo x y z) :type fix)

(in-theory (disable gensym::generalize))

(encapsulate
 ()
(local
(encapsulate
 ()

 (defun foo (x) x)
 (defun goo (x)
   (declare (ignore x))
   t)

 (defthm open-goo
   (implies
    (and
     (syntaxp (symbolp x))
     (integerp x))
    (goo x)))

 (in-theory (disable goo (:type-prescription goo)))

 (defthm integerp-foo
   (implies
    (integerp x)
    (integerp (foo x))))

 (in-theory (disable foo (:type-prescription foo)))

 (add-generalization-pattern (foo x) :type integerp)

 ;; This works only because of the generalization of (foo x)
 (defthm pred-foo
   (implies
    (integerp x)
    (goo (gensym::generalize (foo x)))))

 )))
