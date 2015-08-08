(in-package "ACL2")

;; Soundness of the skolem step functions step-sk/step-ex,
;; which operate on the leftmost existential quantifier.
;; Recall that step-sk does a skolemization, and step-ex
;; does the corresponding extension of an interpretation.

(include-book "sk-useless")
(include-book "sk-step")

;;-------------------------

(defthm not-validator-not-feval-d
  (implies (and (domain-term-list (fringe dom))
		(not (validator f x dom i)))
	   (not (feval-d (list 'exists x f) dom i))))

(defthm not-validator-not-feval
  (implies (and (not (validator f x dom i))
		(subsetp-equal (fringe dom) (fringe (domain i)))
		(member-equal e (fringe dom)))
	   (not (feval (subst-free f x e) i))))

(defthm not-validator-not-feval-2
  (implies (and (not (validator f x (domain i) i))
		(member-equal e (fringe (domain i))))
	   (not (feval (subst-free f x e) i))))

(defthm validator-feval
  (implies (validator f x dom i)
	   (feval (subst-free f x (validator f x dom i)) i)))

(defthm validator-feval-exists
  (implies (and (variable-term x)
		(validator f x dom i))
	   (feval-d (list 'exists x f) dom i)))

;;------------------------------------
;; not validator case

(encapsulate
 nil
 (local (include-book "instance"))

 (defthm ground-term-eval  ;; redundant event from instance book
  (implies (and (variable-term x)
		(domain-term-list (fringe dom))
		(not (vars-in-term-list (list tm))))
	   (equal (xeval (subst-free f x (eval-term tm i)) dom i)
		  (xeval (subst-free f x tm) dom i))))
 )

(defthm ground-term-feval
  (implies (and (variable-term x)
		(not (vars-in-term-list (list tm))))
	   (equal (feval (subst-free f x (eval-term tm i)) i)
		  (feval (subst-free f x tm) i)))
  :hints (("Goal"
           :in-theory (enable xeval-feval))))

(defthm not-validator-case
  (implies (and (variable-term x)
		(domain-term-list vals)
		(not (validator f x (domain i) i))
		(not (member-equal fsym (funcs-in-formula f))))
	   (not (feval (subst-free f x (cons fsym vals))
		       (list* (domain i)
			      (relations i)
			      (list (cons fsym (len vals))
				    (cons vals 0))
			      (functions i)))))
  :hints (("Goal"
	   :do-not generalize
	   :in-theory (disable eval-term-list ground-term-feval)
	   :use ((:instance ground-term-feval
			    (tm (cons fsym vals))
			    (i (list* (domain i)
				      (relations i)
				      (list (cons fsym (len vals))
					    (cons vals 0))
				      (functions i)))
			    ))))
  :otf-flg t)

;;------------------------------------
;; validator case

(defthm validator-in-domain
  (implies (validator f x dom i)
	   (member-equal (validator f x dom i) (fringe dom))))

(defthm validator-is-domain-term
  (implies (and (validator f x dom i)
		(domain-term-list (fringe dom)))
	   (domain-term (validator f x dom i))))

(defthm eval-term-with-inserted-tuple
  (implies (and (domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(function-symbol fsym)
		(member-equal val (fringe (domain i))))
	   (equal (car (eval-term-list
			(list (cons fsym vals))
			(list* (domain i)
			       (relations i)
			       (list (cons fsym (len vals))
				     (cons vals val))
			       (functions i))))
		  val))
  :hints (("Goal"
           :in-theory (enable fapply domain))))

(defthm validator-case
  (implies (and (variable-term x)
		(function-symbol fsym)
		(not (member-equal x (quantified-vars f)))
		(setp (quantified-vars f))
		(domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		(validator f x (domain i) i))
	   (equal (feval (subst-free f x (cons fsym vals))
			 (list* (domain i)
				(relations i)
				(list (cons fsym (len vals))
				      (cons vals
					    (validator f x
						       (domain i)
						       i)))
				(functions i)))
		  (feval-d (list 'exists x f)
			   (domain i)
			   i)))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (disable eval-term-list ground-term-feval)
	   :use ((:instance ground-term-feval
			    (tm (cons fsym vals))
			    (i (list* (domain i)
				      (relations i)
				      (list (cons fsym (len vals))
					    (cons vals (validator f x
						       (domain i)
						       i)))
				      (functions i)))
			    )))))

;;---------------------------------
;; append case

(include-book "sk-xbuild")

(defthm xeval-append-a-x
  (implies
   (and (variable-term f3)
	(function-symbol fsym)
	(step-sk-arity f5 (+ 1 (len vals)))
	(not (member-equal f3 (quantified-vars f5)))
	(setp (quantified-vars f5))
	(domain-term-list vals)
	(subsetp-equal vals (fringe (domain i)))
	(not (member-equal fsym (funcs-in-formula f5)))
	(domain-term-list (append (fringe dom1) (fringe dom2)))
	(setp (append (fringe dom1) (fringe dom2)))
	(subsetp-equal (append (fringe dom1) (fringe dom2))
		       (fringe (domain i))))
   (equal (feval-d (list 'all f3 (step-sk f5 (append vals (list f3)) fsym))
		   dom2
		   (list* (domain i)
			  (relations i)
			  (cons (cons fsym
				      (step-sk-arity f5 (+ 1 (len vals))))
				(append (build-sk-d (list 'all f3 f5)
						    vals dom1 i)
					(build-sk-d (list 'all f3 f5)
						    vals dom2 i)))
			  (functions i)))
	  (feval-d (list 'all f3 (step-sk f5 (append vals (list f3)) fsym))
		   dom2
		   (list* (domain i)
			  (relations i)
			  (cons (cons fsym
				      (step-sk-arity f5 (+ 1 (len vals))))
				(build-sk-d (list 'all f3 f5)
					    vals dom2 i))
			  (functions i)))))
  :hints (("Goal"
	   :use ((:instance xeval-append-a
			    (y f3) (f f5) (dm dom1) (dom dom2)
			    (func2 (build-sk-d (list 'all f3 f5)
					       vals dom2 i))))
           :in-theory (disable XEVAL-APPEND-A)
	   :do-not-induct t
	   )))

(defthm xeval-append-b-x1
  (implies
   (and (variable-term f3)
	(function-symbol fsym)
	(step-sk-arity f5 (+ 1 (len vals)))
	(not (member-equal f3 (quantified-vars f5)))
	(setp (quantified-vars f5))
	(domain-term-list vals)
	(subsetp-equal vals (fringe (domain i)))
	(not (member-equal fsym (funcs-in-formula f5)))
	(domain-term-list (append (fringe dom1) (fringe dom2)))
	(setp (append (fringe dom1) (fringe dom2)))
	(subsetp-equal (append (fringe dom1) (fringe dom2))
		       (fringe (domain i)))
	(feval-d (list 'all f3 f5) dom1 i)
	)
   (equal (feval-d (list 'all f3 (step-sk f5 (append vals (list f3)) fsym))
		   dom1
		   (list* (domain i)
			  (relations i)
			  (cons (cons fsym (step-sk-arity f5 (+ 1 (len vals))))
				(append (build-sk-d (list 'all f3 f5)
						    vals dom1 i)
					(build-sk-d (list 'all f3 f5)
						    vals dom2 i)))
			  (functions i)))
	  (feval-d (list 'all f3 (step-sk f5 (append vals (list f3)) fsym))
		   dom1
		   (list* (domain i)
			  (relations i)
			  (cons (cons fsym (step-sk-arity f5 (+ 1 (len vals))))
				(build-sk-d (list 'all f3 f5)
					    vals dom1 i))
			  (functions i)))))
  :hints (("Goal"
	   :use ((:instance xeval-append-b
			    (y f3) (f f5) (dm dom2) (dom dom1)
			    (func1 (build-sk-d (list 'all f3 f5)
					       vals dom1 i))))
           :in-theory (disable XEVAL-APPEND-B)
	   :do-not-induct t
	   )))

(defthm xeval-append-b-x2
  (implies
   (and (variable-term f3)
	(function-symbol fsym)
	(step-sk-arity f5 (+ 1 (len vals)))
	(not (feval-d (list 'all f3 (step-sk f5 (append vals (list f3)) fsym))
		      dom1
		      (list* (domain i)
			     (relations i)
			     (cons (cons fsym
					 (step-sk-arity f5 (+ 1 (len vals))))
				   (build-sk-d (list 'all f3 f5)
					       vals dom1 i))
			     (functions i))))
	(not (member-equal f3 (quantified-vars f5)))
	(setp (quantified-vars f5))
	(domain-term-list vals)
	(subsetp-equal vals (fringe (domain i)))
	(not (member-equal fsym (funcs-in-formula f5)))
	(domain-term-list (append (fringe dom1) (fringe dom2)))
	(setp (append (fringe dom1) (fringe dom2)))
	(subsetp-equal (append (fringe dom1) (fringe dom2))
		       (fringe (domain i)))
	(not (feval-d (list 'all f3 f5) dom1 i))
	)
   (not (feval-d (list 'all f3 (step-sk f5 (append vals (list f3)) fsym))
		 dom1
		 (list* (domain i)
			(relations i)
			(cons (cons fsym (step-sk-arity f5 (+ 1 (len vals))))
			      (append (build-sk-d (list 'all f3 f5)
						  vals dom1 i)
				      (build-sk-d (list 'all f3 f5)
						  vals dom2 i)))
			(functions i)))))
  :hints (("Goal"
	   :use ((:instance xeval-append-b
			    (y f3) (f f5) (dm dom2) (dom dom1)
			    (func1 (build-sk-d (list 'all f3 f5)
					       vals dom1 i))))
           :in-theory (disable XEVAL-APPEND-B)
	   :do-not-induct t
	   )))

;;----------------------------------------------
;; Here it is, the heart of the soundness of Skolemization.
;; We split it into 2 cases: with and without a skolemizable existential quant.

(defthm step-sk-e-fsound-flg
  (implies (and (setp (quantified-vars f))
		(step-sk-arity f (len vals))  ;; there is a skolemizable exists
		(function-symbol fsym)
		(domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f))))
	   (if flg
	       (equal (feval (step-sk f vals fsym) (step-ex f fsym vals i))
		      (feval f i))

	       (implies (and (wfall f)
			     (domain-term-list (fringe dom))
			     (setp (fringe dom))
			     (subsetp-equal (fringe dom) (fringe (domain i))))
			(equal (feval-d (step-sk f vals fsym ) dom
					(step-ex-d f fsym vals dom i))
			       (feval-d f dom i)))))
  :hints (("Goal"
	   :do-not generalize
	   :induct (build-sk-i flg f vals dom i))
	  )
  :rule-classes nil)

(in-theory (disable step-ex))

(defthm step-sk-e-fsound-vals
  (implies (and (setp (quantified-vars f))
		(step-sk-arity f (len vals))  ;; there is a skolemizable exists
		(function-symbol fsym)
		(domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		)
	   (equal (feval (step-sk f vals fsym) (step-ex f fsym vals i))
		  (feval f i)))
  :hints (("Goal"
	   :by (:instance step-sk-e-fsound-flg (flg t)))))

(defthm step-sk-without-exists-2
  (implies (and (natp n)
		(not (step-sk-arity f n)))
	   (equal (step-sk f vars fsym) f))
  :hints (("goal"
	   :induct (step-sk-sym-i2 f vars n))))

(defthm step-sk-x-fsound-vals
  (implies (and (setp (quantified-vars f))
		(not (step-sk-arity f (len vals)))  ;; no skolemizable exists
		(function-symbol fsym)
		(domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		)
	   (equal (feval (step-sk f vals fsym) (step-ex f fsym vals i))
		  (feval f i)))
  :hints (("Goal"
	   :in-theory (enable step-ex)
	   :use ((:instance step-sk-without-exists-2
			    (n (len vals))
			    (vars vals))))))

(defthm step-sk-fsound-vals
  (implies (and (setp (quantified-vars f))
		(function-symbol fsym)
		(domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		)
	   (equal (feval (step-sk f vals fsym) (step-ex f fsym vals i))
		  (feval f i)))
  :hints (("Goal"
	   :use ((:instance step-sk-e-fsound-vals)
		 (:instance step-sk-x-fsound-vals)))))

(defthm step-sk-fsound
  (implies (and (setp (quantified-vars f))
		(function-symbol fsym)
		(not (member-equal fsym (funcs-in-formula f))))
	   (equal (feval (step-sk f nil fsym) (step-ex f fsym nil i))
		  (feval f i))))

