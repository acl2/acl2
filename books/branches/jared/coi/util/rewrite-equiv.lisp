#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "good-rewrite-order")
(include-book "clause-processor")

(defthm not-hide-forward
  (implies
   (not (hide x))
   (not x))
  :hints (("Goal" :expand (hide x)))
  :rule-classes (:forward-chaining))

(defthm not-rewrite-equiv-forward
  (implies
   (not (rewrite-equiv term))
   (not term))
  :rule-classes (:forward-chaining))

(defun member? (x list)
  (declare (type t x list))
  (if (consp list)
      (or (equal x (car list))
	  (member? x (cdr list)))
    nil))

(defun equiv-var-term (equivs term)
  (declare (xargs :mode :program))
  (and (consp term)
       (equal (car term) 'not)
       (consp (cdr term))
       (consp (cadr term))
       (let ((term (cadr term)))
	 (and (member? (car term) equivs)
	      (consp (cdr term))
	      (consp (cddr term))
	      (let ((lhs (cadr term))
		    (rhs (caddr term)))
		(or (and (good-rewrite-order lhs rhs) `(not (hide (rewrite-equiv ,term))))
		    (and (good-rewrite-order rhs lhs) `(not (hide (rewrite-equiv (,(car term) ,rhs ,lhs)))))
		    nil))))))

(defun find-equiv (equivs clause)
  (declare (xargs :mode :program))
  (if (consp clause)
      (let ((term (car clause)))
	(let ((nterm (equiv-var-term equivs term)))
	  (or (and nterm (cons term nterm))
	      (find-equiv equivs (cdr clause)))))
    nil))

(defun clause-contains (term1 clause)
  (declare (type t clause))
  (if (consp clause)
      (or (equal (car clause) term1)
	  (clause-contains term1 (cdr clause)))
    nil))

(defun replace-1 (term1 term2 clause)
  (declare (type t term1 term2 clause))
  (if (consp clause)
      (if (equal (car clause) term1)
	  (cons term2 (cdr clause))
	(cons (car clause)
	      (replace-1 term1 term2 (cdr clause))))
    nil))

(defun rewrite-equiv-clause-processor (clause hints)
  (if (consp hints)
      (let ((term1 (car hints))
	    (term2 (cdr hints)))
	(let ((clause (replace-1 term1 term2 clause)))
	  (list 
	   clause
	   (list (clause-implies term2 term1)))))
    (list clause)))

(defevaluator rewrite-equiv-eval rewrite-equiv-list
  (
   (if a b c)
   ))

(clause-eval-facts rewrite-equiv-eval rewrite-equiv-list)

(local (in-theory (disable alistp)))

(defthm rewrite-equiv-clause-processor-works
  (implies
   (and
    (pseudo-term-listp cl)
    (alistp a)
    (rewrite-equiv-eval (conjoin-clauses 
			 (rewrite-equiv-clause-processor cl hints)) a))
   (rewrite-equiv-eval (disjoin cl) a))
  :rule-classes :clause-processor
  :otf-flg t)

;;
;; This would probably work better as a clause processor.
;;
;; What we would need to do is to create two subgoals: one 
;; containing the new rewrite-equiv in place of the equivalence
;; and the other with an assertion that the old equivalence
;; justified the replacment.
;;
(defun slow-rewrite-equiv-hint (stbl old equivs clause)
  (declare (xargs :mode :program))
  (if (and old (clause-contains old clause)) nil
    (let ((default (and old `(:COMPUTED-HINT-REPLACEMENT
			      ((slow-rewrite-equiv-hint stable-under-simplificationp nil ',equivs clause))
			      :cases (t)
			      ))))
      (or (and (or old stbl)
	       (let ((hint (find-equiv equivs (reverse clause))))
		 (or (and hint
			  (let ((old (car hint)))
			    (let ((hint `(:clause-processor (rewrite-equiv-clause-processor clause ',hint))))
			      `(:COMPUTED-HINT-REPLACEMENT
				((slow-rewrite-equiv-hint stable-under-simplificationp ',old ',equivs clause))
				,@hint
				))))
		     default)))
	  default))))

;;
;; OK .. again without clause processors.
;;
#+joe
(defun slow-rewrite-equiv-hint (stbl old equivs clause)
  (declare (xargs :mode :program))
  (if (and old (clause-contains old clause)) nil
    (let ((default (and old `(:COMPUTED-HINT-REPLACEMENT
			      ((slow-rewrite-equiv-hint stable-under-simplificationp nil ',equivs clause))
			      ))))
      (or (and (or stbl old)
	       (let ((hint (find-equiv equivs clause)))
		 (or (and hint
			  (let ((old (car hint))
				(new (cdr hint)))
			    `(:COMPUTED-HINT-REPLACEMENT
			      ((slow-rewrite-equiv-hint stable-under-simplificationp ',old ',equivs clause))
			      :cases (,new))))
		     default)))
	  default))))

(defmacro rewrite-equiv-hint (&rest args)
  (if (consp args)
      `(slow-rewrite-equiv-hint stable-under-simplificationp nil '(,@args) clause)
    `(slow-rewrite-equiv-hint stable-under-simplificationp nil '(equal) clause)))

(local
 (encapsulate 
  ()

(defstub foo (x) nil)
(defstub goo (x) nil)
(defstub hoo (x) nil)

(encapsulate
 (
  ((fred *) => *)
  )

 (local
  (defun fred (x)
    (declare (ignore x))
    t))

 (defthm fred-goo
   (fred (+ 3 (goo x))))

 )
 
;;
;; This theorem does not prove without the rewrite-with-equality hint ..
;;
(defthm simple-example
  (implies
   (and
    (integerp x)
    (equal (foo x) (goo x))
    (equal (hoo x) (+ 3 (foo x))))
   (fred (hoo x)))
  :hints (("Goal" :do-not '(fertilize))
	  (rewrite-equiv-hint)))

(defun cnt (list)
  (if (consp list)
      (1+ (cnt (cdr list)))
    0))

;;
;; Here we use it to help apply an induction hypothesis.
;;
(defthm cnt-reduction
  (equal (cnt list)
	 (len list))
  :hints ((rewrite-equiv-hint)))

))

(local
 (encapsulate
  ()

  (defun equiv (x y) (equal x y))
  
  (defequiv equiv)

  (defcong equiv equal (fred x) 1)

  (defcong equiv equal (binary-+ x y) 1)

  (defcong equiv equal (binary-+ x y) 2)

  (in-theory (disable equiv))

  (defthm simple-equiv-example-1
    (implies
     (and
      (integerp x)
      (equiv (foo x) (goo x))
      (equiv (hoo x) (+ 3 (foo x))))
     (fred (hoo x)))
    :rule-classes nil
    :hints ((rewrite-equiv-hint equiv)))

  ))