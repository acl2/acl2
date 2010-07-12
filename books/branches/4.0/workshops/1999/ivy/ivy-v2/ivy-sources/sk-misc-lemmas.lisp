(in-package "ACL2")

;; This book contains lemmas, not about Skolemization, that
;; arose during the Skolemization work.

(include-book "stage")

(defthm eval-term-list-preserves-len
  (equal (len (eval-term-list l i))
	 (len l)))

(defthm subst-term-list-preserves-len
  (equal (len (subst-term-list l x tm))
	 (len l)))

(defthm domain-list-domain
  (equal (domain (list* (domain i) x))
	 (domain i))
  :hints (("Goal"
           :in-theory (enable domain))))

(defthm relations-1
  (equal (relations (list* x y z)) y)
  :hints (("Goal"
           :in-theory (enable relations))))

(defthm functions-1
  (equal (functions (list* x y z)) z)
  :hints (("Goal"
           :in-theory (enable functions))))

(defthm var-list-append-one
  (implies (and (variable-term v)
		(var-list vars))
	   (var-list (append vars (list v)))))

(defthm var-list-props
  (implies (var-list vars)
	   (and (wft-list vars)
		(true-listp vars)))
  :rule-classes :forward-chaining)

(defthm domain-term-list-append
  (implies (and (domain-term dom)
		(domain-term-list vals))
	   (domain-term-list (append vals (list dom)))))

(defthm eval-term-list-on-domain-term-list
  (implies (and (domain-term-list vals)
		(subsetp-equal vals (fringe (domain i))))
	   (equal (eval-term-list vals i) vals)))

(defthm not-domain-term-not-domain-term-list
  (implies (and (not (domain-term x))
		(domain-term-list l))
	   (not (member-equal x l))))

(defthm eval-term-list-parts
  (equal (eval-term-list l (list* (domain i) (relations i) (functions i)))
	 (eval-term-list l i)))

(defthm xeval-interp-parts
  (equal (xeval f dom (list* (domain i) (relations i) (functions i)))
	 (xeval f dom i))
  :hints (("Goal"
	   :induct (xeval-i f dom i)
           :in-theory (enable eval-atomic))))

(defthm len-append-list
  (equal (len (append a (list x)))
	 (+ 1 (len a))))

(defthm subset-member-append-list
  (implies (and (subsetp-equal a b)
		(member-equal x b))
	   (subsetp-equal (append a (list x)) b)))

(defthm subst-free-preserves-exists-count
  (equal (exists-count (subst-free f x tm))
	 (exists-count f)))

(defthm subst-free-preserves-funcs-in-formula
  (implies (domain-term e)
	   (equal (funcs-in-formula (subst-free f x e))
		  (funcs-in-formula f))))

(defthm not-member-equal-append-list
  (implies (and (not (equal y x))
		(not (member-equal x vars)))
	   (not (member-equal x (append vars (list y))))))

(defthm var-occurrence-term-list-list-cons
  (implies (and (var-list vars)
		(not (member-equal x vars)))
	   (not (var-occurrence-term-list x (list (cons s vars))))))

(defthm disjoint-append-5
  (implies (and (disjoint a (cons x b))
		(not (member-equal x b)))
	   (disjoint (append a (list x)) b))
  :hints (("Goal"
	   :do-not generalize)))

(defthm subst-append-vals-list
  (implies (and (domain-term-list vals)
		(variable-term x))
	   (equal (subst-term-list (append vals (list x)) x e)
		  (append vals (list e)))))

(defthm nil-not-in-domain-term-list
  (implies (domain-term-list vals)
	   (not (member-equal nil vals))))

(defthm not-member-append  ;; move to sets?
  (implies (and (not (member-equal x a))
		(not (member-equal x b)))
	   (not (member-equal x (append a b)))))

(defthm domain-term-list-has-no-vars
  (implies (domain-term-list vals)
	   (not (vars-in-term-list vals)))
  :hints (("Goal"
           :in-theory (enable domain-term))))

(defthm not-vars-in-term-list-2
  (implies (and (domain-term-list vals)
		(function-symbol sym))
	   (not (vars-in-term-list (list (cons sym vals))))))

(defthm car-of-eval-term-list-is-domain-term
  (implies (consp l)
	   (domain-term (car (eval-term-list l i)))))

(defthm subset-eval-term-list-domain
  (subsetp-equal (eval-term-list l i)
		 (fringe (domain i))))

(defthm car-of-eval-term-list-is-in-domain
  (implies (consp l)
	   (member-equal (car (eval-term-list l (cons (domain i) tail)))
			 (fringe (domain i)))))

(defthm car-of-eval-term-list-is-in-domain-2
  (member-equal (car (eval-term-list (list tm) i))
		(fringe (domain i)))
  :hints (("Goal"
         :use ((:instance car-of-eval-term-list-is-in-domain
			  (l (list tm))
			  (tail (cons (relations i) (functions i))))))))

(defthm feval-interp-parts
  (equal (feval f (list* (domain i) (relations i) (functions i)))
	 (feval f i))
  :hints (("Goal"
           :in-theory (enable xeval-feval))))

(defthm setp-append-disjoint
  (implies (setp (append a b))
	   (disjoint a b)))

(defthm disjoint-member-append-cons
  (implies (and (disjoint a b2)
		(not (member-equal b1 (append b2 a))))
	   (disjoint a (cons b1 b2))))

(defthm setp-append-disjoint-2
  (implies (setp (append b a))
	   (disjoint a b))
  :hints (("Goal"
	   :do-not generalize)))

(defthm setp-fringe-domain
  (setp (fringe (domain i)))
  :hints (("Goal"
           :in-theory (enable domain))))

(defthm not-funcs-in-var-list
  (implies (var-list vars)
	   (not (funcs-in-term-list vars))))

(defthm disjoint-member-forward
  (implies (and (disjoint a b)
		(member-equal x a))
	   (not (member-equal x b)))
  :rule-classes :forward-chaining)

