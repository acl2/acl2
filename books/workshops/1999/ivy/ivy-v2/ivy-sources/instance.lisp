(in-package "ACL2")

;; In this book we show that a ground term can be
;; substituted for a universally quantified variable.

(include-book "stage")

;; Substituting a member of the domain.

(defthm instance-domain-term-sound
  (implies (and (variable-term x)
                (xeval (list 'all x f) dom i)
		(member-equal e (fringe dom)))
           (xeval (subst-free f x e) (domain i) i))
  :hints (("Goal"
	   :induct (dom-i dom))))

;;--------------------------------------------------

(defthm len-subst-term-list
  (equal (len (subst-term-list l x tm)) (len l)))

(defthm eval-term-list-idemp
  (equal (eval-term-list (eval-term-list l i) i)
	 (eval-term-list l i)))

(defthm eval-term-idemp-helper
  (implies (consp l)
	   (equal (car (eval-term-list (list (car (eval-term-list l i))) i))
		  (car (eval-term-list l i)))))

(defthm eval-term-idemp
  (equal (eval-term (eval-term tm i) i)
	 (eval-term tm i)))

;;--------------------------------------------------
;; The following 3 lemmas are for the base case of ground-term-eval

(defthm eval-subst-eval-equal-eval-subst
  (equal (eval-term-list (subst-term-list l x (eval-term tm i)) i)
         (eval-term-list (subst-term-list l x tm) i)))

(defthm eval-subst-eval-equal-eval-subst-car
  (equal (eval-term (car (subst-term-list l x (eval-term tm i))) i)
         (eval-term (car (subst-term-list l x tm)) i)))

(defthm eval-subst-eval-equal-eval-subst-cadr
  (equal (eval-term (cadr (subst-term-list l x (eval-term tm i))) i)
         (eval-term (cadr (subst-term-list l x tm)) i)))

;;--------------------------------------------------

(defthm not-vars-in-term-list-not-var-occurrence-term-list
  (implies (not (vars-in-term-list l))
           (not (var-occurrence-term-list x l))))

(defthm not-var-occurrence-term-list-list-car-eval-term-list
  (implies
   (consp l)
   (not (var-occurrence-term-list y (list (car (eval-term-list l i)))))))

;;--------------------------------------------------

(defthm ground-term-eval
  (implies (and (variable-term x)
		(domain-term-list (fringe dom))
		(not (vars-in-term-list (list tm))))
	   (equal (xeval (subst-free f x (eval-term tm i)) dom i)
		  (xeval (subst-free f x tm) dom i)))
  :hints (("Goal"
	   :do-not generalize
	   :induct (xeval-i f dom i))
	  ("Subgoal *1/7"
	   :in-theory (enable eval-atomic))))

(defthm eval-term-list-gives-domain-tuple
  (subsetp-equal (eval-term-list l i) (fringe (domain i)))
  :hints (("Goal"
	   :in-theory (enable domain-term))))

(defthm consp-eval-term-list
  (implies (consp x)
	   (consp (eval-term-list x i))))

;;--------------------------------------------------

(encapsulate
 nil
 (local (defthm lkj
	  (implies (and (subsetp-equal a b) (consp a))
		   (member-equal (car a) b))))

 (defthm eval-term-gives-domain-member
   (member-equal (eval-term tm i) (fringe (domain i))))
)  ;; end encapsulate

(defthm instance-term-sound
  (implies (and (variable-term x)
		(not (vars-in-term-list (list tm)))
		(xeval (list 'all x f) (domain i) i))
	   (xeval (subst-free f x tm) (domain i) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance instance-domain-term-sound
			    (dom (domain i))
			    (e (eval-term tm i))
			    )))))
