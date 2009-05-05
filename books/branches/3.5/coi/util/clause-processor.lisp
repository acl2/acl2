#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(defevaluator clause-eval clause-eval-list
  (
   (if a b c)
   )
  )

(defun clause-eval-clique (x) 
  (declare (ignore x))
  t)

(defthm clause-eval-clique-theorem
  (clause-eval-clique (clause-eval x a)))

(defthm clause-eval-disjoin2
  (iff (clause-eval (disjoin2 x y) a)
       (or (clause-eval x a)
	   (clause-eval y a))))

(defthm clause-eval-conjoin2
  (iff (clause-eval (conjoin2 x y) a)
       (and (clause-eval x a)
	    (clause-eval y a))))

(in-theory (disable disjoin2 conjoin2))

(defthm open-disjoin
  (equal (disjoin (cons a list))
	 (if (consp list)
	     (disjoin2 a (disjoin list))
	   a)))

(defthm clause-eval-disjoin
  (and
   (implies
    (not (consp list))
    (iff (clause-eval (disjoin list) a) nil))
   (implies
    (consp list)
    (iff (clause-eval (disjoin list) a) 
	 (or (clause-eval (car list) a)
	     (clause-eval (disjoin (cdr list)) a))))))

(in-theory (disable disjoin))

(defthm open-conjoin
  (equal (conjoin (cons a list))
	 (if (consp list)
	     (conjoin2 a (conjoin list))
	   a)))

(defthm clause-eval-conjoin
  (and
   (implies
    (not (consp list))
    (iff (clause-eval (conjoin list) a) t))
   (implies
    (consp list)
    (iff (clause-eval (conjoin list) a)
	 (and (clause-eval (car list) a)
	      (clause-eval (conjoin (cdr list)) a))))))

(in-theory (disable conjoin))

(defun clause-not (x)
  `(if ,x (quote nil) (quote t)))

(defun clause-implies (x y)
  `(if ,x ,y (quote t)))

;; We use clause-cons to add a "true fact" to a list of clauses.
;; To do this, we must negate the term.

(defun clause-cons (a clause)
  (cons (clause-not a) clause))

(defthm clause-eval-clause-not
  (iff (clause-eval (clause-not x) a)
       (not (clause-eval x a))))

(defthm clause-eval-clause-implies
  (iff (clause-eval (clause-implies x y) a)
       (implies (clause-eval x a)
		(clause-eval y a))))

(in-theory (disable clause-not))
(in-theory (disable clause-implies))

(defmacro clause-eval-facts (eval eval-list)

  (let ((eval-clique-proof   (packn-pos (list eval "-CLIQUE-PROOF") eval))
	(eval-disjoin2       (packn-pos (list eval "-DISJOIN2") eval))
	(eval-conjoin2       (packn-pos (list eval "-CONJOIN2") eval))
	(eval-disjoin        (packn-pos (list eval "-DISJOIN") eval))
	(eval-conjoin        (packn-pos (list eval "-CONJOIN") eval))
	(eval-clause-not     (packn-pos (list eval "-CLAUSE-NOT") eval))
	(eval-clause-implies (packn-pos (list eval "-CLAUSE-IMPLIES") eval))
	(eval-constraint-0   (packn-pos (list eval "-CONSTRAINT-0") eval))
	)

    `(encapsulate
	 ()
       
       (defthm ,eval-clique-proof
	 (clause-eval-clique (,eval x a))
	 :rule-classes nil
	 :hints (("Goal" :use (:functional-instance
			clause-eval-clique-theorem
			(clause-eval ,eval)
			(clause-eval-list ,eval-list)))
		 (and stable-under-simplificationp
		      '(:in-theory (enable ,eval-constraint-0)))))
		  
       
       (defthm ,eval-disjoin2
	 (iff (,eval (disjoin2 x y) a)
	      (or (,eval x a)
		  (,eval y a)))
	 :hints (("Goal" :use (:functional-instance
			       clause-eval-disjoin2
			       (clause-eval ,eval)
			       (clause-eval-list ,eval-list)))))
       
       (defthm ,eval-conjoin2
	 (iff (,eval (conjoin2 x y) a)
	      (and (,eval x a)
		   (,eval y a)))
	 :hints (("Goal" :use (:functional-instance
			       clause-eval-conjoin2
			       (clause-eval ,eval)
			       (clause-eval-list ,eval-list)))))

       (defthm ,eval-clause-not
	 (iff (,eval (clause-not x) a)
	      (not (,eval x a)))
	 :hints (("Goal" :use (:functional-instance
			       clause-eval-clause-not
			       (clause-eval ,eval)
			       (clause-eval-list ,eval-list)))))

       (defthm ,eval-clause-implies
	 (iff (,eval (clause-implies x y) a)
	      (implies (,eval x a)
		       (,eval y a)))
	 :hints (("Goal" :use (:functional-instance
			       clause-eval-clause-implies
			       (clause-eval ,eval)
			       (clause-eval-list ,eval-list)))))

       (defthm ,eval-conjoin
	 (and
	  (implies
	   (not (consp list))
	   (iff (,eval (conjoin list) a) t))
	  (implies
	   (consp list)
	   (iff (,eval (conjoin list) a)
		(and (,eval (car list) a)
		     (,eval (conjoin (cdr list)) a)))))
	 :hints (("Goal" :use (:functional-instance
			       clause-eval-conjoin
			       (clause-eval ,eval)
			       (clause-eval-list ,eval-list)))))

       (defthm ,eval-disjoin
	 (and
	  (implies
	   (not (consp list))
	   (iff (,eval (disjoin list) a) nil))
	  (implies
	   (consp list)
	   (iff (,eval (disjoin list) a)
		(or (,eval (car list) a)
		    (,eval (disjoin (cdr list)) a)))))
	 :hints (("Goal" :use (:functional-instance
			       clause-eval-disjoin
			       (clause-eval ,eval)
			       (clause-eval-list ,eval-list)))))

       )))


(local
 (encapsulate
     ()

   (defevaluator test-eval test-eval-list
     (
      (if a b c)
      )
     )

   (clause-eval-facts test-eval test-eval-list)

   ))
