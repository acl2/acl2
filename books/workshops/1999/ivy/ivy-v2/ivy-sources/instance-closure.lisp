(in-package "ACL2")

;; The main event of this book is the last event,
;; instance-xsound-for-1-substitution, which says that
;; if the universal closure of a quantifier-free formula f
;; is true in some intepretation, and we substitute a
;; (not necessarily ground) term for a variable, then
;; the universal closure of the result is true in the
;; interpretation.

(include-book "instance")
(include-book "../../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

;;-------------
;; If the formula is quantifier-free, the domain argument is irrelevant.

(defthm quant-free-xeval
  (implies (quantifier-free f)
           (equal (xeval f dom1 i)
                  (xeval f dom2 i)))
  :hints (("Goal"
	   :induct (quantifier-free f)))
  :rule-classes nil)

(defthm not-free-xeval-same
  (implies (and (variable-term x)
		(not (member-equal x (free-vars f))))
           (equal (xeval (list 'all x f) dom i)
                  (xeval f (domain i) i)))
  :hints (("Goal"
           :induct (dom-i dom))
	  ("Subgoal *1/1"
	   :in-theory (enable not-free-not-change-2)))
  :rule-classes nil)

;;------------------

(defthm subst-flip-fix-quant-free
  (implies (and (quantifier-free f)
		(not (equal x y))
		(domain-term e))
	   (equal (subst-free (subst-free f x e) y (subst-term tm x e))
		  (subst-free (subst-free f y tm) x e))))

;;------------- for case 1.5 (base instance-ground)

(defthm union-15
  (implies (union-equal a nil)
	   (union-equal a b)))

(defthm member-vars-subst
  (implies (and (member-equal x (vars-in-term-list l))
		(vars-in-term-list (list tm)))
	   (vars-in-term-list (subst-term-list l x tm))))

(defthm member-vars-subst-free
  (implies (and (vars-in-term-list (list tm))
		(quantifier-free f)
		(member-equal x (free-vars f)))
	   (free-vars (subst-free f x tm))))

;;-----------------------  Part 1
;;
;; Now get theorem instance-xsound-ground into a slightly different form.
;; Note the (quantifier-free f) constraint (see note on thm
;; instance-gxsound-alls-1 below).
;; This is for the base case of theorem instance-xsound-alls-1 below.

(in-theory (enable not-free-not-change-2))

(local (defthm case-1-5
  (implies (and (domain-term-list (fringe dom))
		(quantifier-free f)
		(variable-term x)
		(not (remove-equal x (free-vars f)))
		(not (free-vars (subst-free f x tm)))
		(xeval (list 'all x f) (domain i) i))
	   (xeval (subst-free f x tm) dom i))
  :hints (("goal"
	   :do-not-induct t
	   :in-theory (disable instance-term-sound member-vars-subst-free)
	   :use ((:instance instance-term-sound)
		 (:instance member-vars-subst-free)
		 (:instance quant-free-xeval
			    (f (subst-free f x tm))
			    (dom1 dom)
			    (dom2 (domain i)))
		 (:instance not-free-xeval-same
			    (dom (domain i))))
	   ))))

(in-theory (disable not-free-not-change-2))

;;------------------  for case 1.3 and 1.1

(defthm x-diff-y-x-only-member-not-member-y
  (implies (and (not (equal x y))
		(not (remove-equal x a)))
	   (not (member-equal y a)))
  :rule-classes nil)

;;------------------ for case 1.4

(defthm subst-alls-commute-backward
  (implies (and (not (member-equal x vars))
                (var-list vars))
           (equal (alls vars (subst-free f x e))
		  (subst-free (alls vars f) x e)))
  :rule-classes nil)

(defthm not-free-vars-alls-subst-free
  (implies (and (var-set v2)
		(variable-term v1)
		(not (member-equal v1 v2))
		(not (remove-equal v1 (free-vars (alls v2 g))))
		(domain-term e))
	   (not (free-vars (alls v2 (subst-free g v1 e)))))
  :hints (("Goal"
	   :in-theory (disable subst-alls-commute vars-alls-free)
	   :use ((:instance subst-alls-commute-backward
			    (x v1) (vars v2) (f g))
		 (:instance vars-alls-free
			    (x v1) (f (alls v2 g))))
	   :do-not-induct t)))

;;------------------------ for a case

(in-theory (enable not-free-not-change-2))

(defthm flip-only-diff
  (implies (and (quantifier-free f)
		(domain-term e)
		(not (remove-equal y (free-vars f)))
		(not (equal x y))
		)
	   (equal (subst-free f y (subst-term tm x e))
		  (subst-free (subst-free f y tm) x e)))
  :hints (("Goal"
         :do-not-induct t
	 :in-theory (disable subst-flip-fix-quant-free)
	 :use ((:instance subst-flip-fix-quant-free)
	       (:instance x-diff-y-x-only-member-not-member-y
			  (x y) (y x) (a (free-vars f))))))
  :rule-classes nil)

(in-theory (disable not-free-not-change-2))

(defthm flip-same-term-list
  (implies (domain-term e)
	   (equal (subst-term-list f2 x (car (subst-term-list (list tm) x e)))
		  (subst-term-list (subst-term-list f2 x tm) x e))))

(defthm flip-only-same
  (implies (and (quantifier-free f)
		(domain-term e))
	   (equal (subst-free f x (subst-term tm x e))
		  (subst-free (subst-free f x tm) x e)))
  :rule-classes nil)

(defthm flip-only
  (implies (and (quantifier-free f)
		(domain-term e)
		(not (remove-equal y (free-vars f))))
	   (equal (subst-free f y (subst-term tm x e))
		  (subst-free (subst-free f y tm) x e)))
  :hints (("Goal"
         :do-not-induct t
	 :use ((:instance flip-only-diff)
	       (:instance flip-only-same)))))

;;------------------------
;; This is the induction scheme for instance-xsound-alls-1b below.
;; The difference from var-induct is that there is an extra argument tm
;; that is instantiated along with the formula f.

(defthm wft-list-subst-term-list  ;; for var-induct-tm guards
  (implies (and (wft-list l)
		(consp l)
		(domain-term e))
	   (wft-list (list (car (subst-term-list l x e))))))

(defthm consp-subst-term-list  ;; for var-induct-tm guards
  (implies (and (wft-list l)
		(consp l))
	   (consp (subst-term-list l x e))))

(defun var-induct-tm (vars f tm dom i)
  (declare (xargs :measure (cons (+ 1 (acl2-count vars)) (acl2-count dom))
                  :guard (and (var-list vars) (wff f) (wft tm)
                              (domain-term-list (fringe dom)))))
  (if (atom vars)
      nil
      (if (atom dom)
          (var-induct-tm (cdr vars)
		      (subst-free f (car vars) dom)
		      (car (subst-term-list (list tm) (car vars) dom))
		      (domain i) i)
          (cons (var-induct-tm vars f tm (car dom) i)
                (var-induct-tm vars f tm (cdr dom) i)))))

;; The following theorem has that hypothesis (quantifier-free f).  The
;; two reasons (both due to the base case) are:
;;   (1) The old (car i)/dom problem, which might be fixable by using feval.
;;   (2) The proof fails because (vars-in-term tm) and (quantified-vars f)
;;       are not disjoint.

(defthm instance-xsound-alls-1b
  (implies (and (domain-term-list (fringe dom))
		(subsetp-equal (fringe dom) (fringe (domain i)))
                (variable-term x)
		(quantifier-free f)  ;; NOTE QUANTIFIER-FREE!
		(not (free-vars (list 'all x f)))
                (xeval (list 'all x f) (domain i) i)
		(var-set v)
		(equal (subst-free f x tm) g)
                (not (free-vars (alls v g))))
           (xeval (alls v g) dom i))
  :hints (("Goal"
	   :induct (var-induct-tm v g tm dom i))
	  ("Subgoal *1/3"
	   :expand ((ALLS V (SUBST-FREE F X TM))))
	  )
  :rule-classes nil)

;;----------------------  Part 2
;; Now, extend the preceding theorem by tacking sequences of universally
;; quantified variables onto the fronts of the the formulas with "alls".

;;------------------------  for a case of instance-xsound-alls-2 below

(defthm unexpand-subst-free-all
  (implies (and (variable-term y)
                (not (equal x y)))
           (equal (list 'all y (subst-free f x tm))
                  (subst-free (list 'all y f) x tm)))
  :rule-classes nil)

(defthm var-alls-subst-2
  (implies (and (domain-term e)
                (variable-term x)
                (variable-term y)
                (not (equal x y))
                (var-set v)
                (not (member-equal x v))
                (not (remove-equal x (free-vars (alls v (list 'all y f))))))
           (not (free-vars (alls v (list 'all y (subst-free f x e))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable subst-free)
           :use ((:instance unexpand-subst-free-all (tm e))))
          ("Goal'4'"
           :use ((:instance not-free-vars-alls-subst-free
			    (g (list 'all y f))
			    (v1 x) (v2 v))))))

;;------------------------ For a case of instance-xsound-alls-2:

(defthm not-member-append
  (implies (and (not (member-equal x a))
		(not (member-equal x b)))
	   (not (member-equal x (append a b)))))

(defthm xeval-alls-all-subst
  (implies
   (and (domain-term-list (fringe dom))
        (domain-term e)
        (member-equal e (fringe dom))
        (variable-term x)
        (variable-term w)
        (not (equal x w))
        (not (member-equal x w2))
        (not (member-equal w w2))
        (var-set w2)
        (xeval (list 'all w (alls w2 (list 'all x f))) dom i))
   (xeval (alls w2 (list 'all x (subst-free f w e))) (domain i) i))
  :hints (("Goal"
           :induct (dom-i dom))))

;;------------------------

;; This is the induction scheme for instance-xsound-alls-2b below.
;; The difference from var-induct-tm is that there is an extra argument g
;; that is instantiated along with the formula f and term tm.

(defun var-induct-2-tm (vars f g tm dom i)
  (declare (xargs :measure (cons (+ 1 (acl2-count vars)) (acl2-count dom))
                  :guard (and (var-list vars) (wff f) (wff g) (wft tm)
                              (domain-term-list (fringe dom)))))
  (if (atom vars)
      nil
      (if (atom dom)
          (var-induct-2-tm (cdr vars)
		      (subst-free f (car vars) dom)
		      (subst-free g (car vars) dom)
		      (car (subst-term-list (list tm) (car vars) dom))
		      (domain i) i)
          (cons (var-induct-2-tm vars f g tm (car dom) i)
                (var-induct-2-tm vars f g tm (cdr dom) i)))))

(defthm instance-xsound-alls-2b
  (implies (and (domain-term-list (fringe dom))
                (subsetp-equal (fringe dom) (fringe (domain i)))
                (variable-term x)
                (quantifier-free f)   ;; ********* quantifier-free *******
                (var-set w)
		(not (member-equal x w))
                (not (free-vars (alls w (list 'all x f))))
                (xeval (alls w (list 'all x f)) (domain i) i)
                (var-set (append w v))
		(equal (subst-free f x tm) g)
                (not (free-vars (alls (append w v) g))))
           (xeval (alls (append w v) g) dom i))
  :hints (("Goal"
	   :induct (var-induct-2-tm w f g tm dom i))
	  ("Subgoal *1/3"
	   :expand ((append w v)))
	  ("Subgoal *1/2.1''"
	   :use ((:instance xeval-alls-all-subst
			    (e dom)
			    (dom (domain i))
			    (w w1))))
	  ("Subgoal *1/1'''"
	   :use ((:instance instance-xsound-alls-1b
			    (g (subst-free f x tm)))))
	  )
  :rule-classes nil)

;;-------------------------- Part 3
;; Get this thing in terms of universal closure.  This requires some
;; set operations and the theorem xeval-alls-subset to get the
;; leading universal quantifiers in right order (given by free-vars).

(defthm var-set-append-remove-list
  (implies (and (variable-term x)
                (var-set vf))
           (var-set (append (remove-equal x vf) (list x)))))

(defthm alls-append
  (equal (alls (append v (list x)) f)
         (alls v (list 'all x f))))

;;------------

(defthm not-member-not-equal
  (implies (and (not (member-equal x a))
                (member-equal v1 a))
           (not (equal x v1)))
  :rule-classes nil)

(defthm member-remove-free-vars-alls
  (implies (and (member-equal x (free-vars (alls v2 f)))
                (member-equal v1 w)
                (member-equal x (free-vars (alls w f))))
           (member-equal x (remove-equal v1 (free-vars (alls v2 f)))))
 :hints (("goal"
          :do-not-induct t
          :in-theory (disable alls-eliminates-free-vars)
          :use ((:instance alls-eliminates-free-vars (vars w))
                (:instance not-member-not-equal (a w))))))

(defthm subset-member-free-vars-alls
  (implies (and (subsetp-equal v w)
                (member-equal x (free-vars (alls w f))))
           (member-equal x (free-vars (alls v f))))
 :hints (("Goal"
          :do-not generalize))
 :rule-classes nil)

(defthm subset-vars-not-member-closure
  (implies (subsetp-equal (free-vars f) w)
           (not (member-equal x (free-vars (alls w f)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance subset-member-free-vars-alls
                            (v (free-vars f)))))))

(defthm subset-vars-closed
  (implies (subsetp-equal (free-vars f) w)
           (not (free-vars (alls w f))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance consp-has-member-equal
                            (x (free-vars (alls w f))))))))

(defthm not-vars-alls-remove-vars-all
  (not (free-vars (alls (remove-equal x (free-vars f)) (list 'all x f))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable alls-append)
           :use ((:instance alls-append
                            (v (remove-equal x (free-vars f))))))))

;;---------------
;; This section is just to prove something about set operations,
;; theorem member-append-difference below.

(defthm member-difference-cons
  (implies (and (member-equal x (set-difference-equal b a2))
                (not (equal x a1)))
           (member-equal x (set-difference-equal b (cons a1 a2))))
  :rule-classes nil)

(defthm member-append-or
  (implies (member-equal x (append a b))
           (or (member-equal x a) (member-equal x b)))
  :rule-classes nil)

(defthm member-append-difference-cons-helper
  (implies (and (member-equal x (set-difference-equal b a2))
                (not (equal x a1)))
           (member-equal x (append a2 (set-difference-equal b (cons a1 a2)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance member-difference-cons))))
  :rule-classes nil)

(defthm member-append-difference-cons
  (implies (and (member-equal x (append a2 (set-difference-equal b a2)))
                (not (equal x a1)))
           (member-equal x (append a2 (set-difference-equal b (cons a1 a2)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable member-append-left)
           :use ((:instance member-append-difference-cons-helper)
                 (:instance member-append-left
			    (a a2)
                            (b (set-difference-equal b (cons a1 a2))))
                 (:instance member-append-or
			    (a a2)
                            (b (set-difference-equal b (cons a1 a2))))))))

(defthm member-append-difference
  (implies (member-equal x (append a b))
           (member-equal x (append a (set-difference-equal b a)))))

;; Now get this in terms of subset.

;; It might have been simpler to do this in terms of subset in the
;; first place.  In  particular, the following is proved automatically.
;;   (defthm lkj7
;;     (subsetp-equal (append b a)
;;                    (append (set-difference-equal b a) a)))
;; but both appends have to be flipped, which is nontrivial (for me).

;;------------------------------------

(defthm member-append-difference-subset
  (subsetp-equal (append a b) (append a (set-difference-equal b a)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance subset-skolem-lemma
                            (a (append a b))
                            (b (append a (set-difference-equal b a))))))))

;;------------------------------------

(defthm vars-in-subst-term-list
  (subsetp-equal (vars-in-term-list (subst-term-list l x tm))
                 (union-equal (remove-equal x (vars-in-term-list l))
                              (vars-in-term-list (list tm))))
  :hints (("Goal"
           :do-not generalize)))

(defthm member-union-remove
  (implies (and (member-equal f (union-equal r v))
                (not (equal x f)))
           (member-equal f (union-equal (remove-equal x r) v))))

(defthm subset-remove-union-remove
  (implies (subsetp-equal f (union-equal r v))
           (subsetp-equal (remove-equal x f)
                          (union-equal (remove-equal x r) v)))
  :hints (("Goal"
           :induct (remove-equal x f))))

(defthm free-vars-in-subst
  (subsetp-equal (free-vars (subst-free f x tm))
                 (union-equal (remove-equal x (free-vars f))
                              (vars-in-term tm))))

;; Now, get this in terms of append instead of union-equal

(defthm subset-union-append
  (subsetp-equal (union-equal b c)
                 (append b c)))

(defthm subset-union-subset-append
  (implies (subsetp-equal a (union-equal b c))
           (subsetp-equal a (append b c))))

(defthm free-vars-in-subst-append
  (subsetp-equal (free-vars (subst-free f x tm))
                 (append (remove-equal x (free-vars f))
                         (vars-in-term tm))))

;;---------------------------

(defthm subset-free-subst-append-remove-etc
  (subsetp-equal (free-vars (subst-free f x tm))
                 (append (remove-equal x (free-vars f))
                         (set-difference-equal
                          (vars-in-term tm)
                          (remove-equal x (free-vars f)))))
  :hints (("Goal"
           :use ((:instance subsetp-equal-transitive
                            (x (free-vars (subst-free f x tm)))
                            (y (append (remove-equal x (free-vars f))
                                       (vars-in-term tm)))
                            (z (append (remove-equal x (free-vars f))
                                       (set-difference-equal
                                        (vars-in-term tm)
                                        (remove-equal x (free-vars f)))))
                            ))
           :do-not-induct t)))

;;---------------

(defthm not-vars-append-difference-subst
  (not (free-vars
        (alls (append (remove-equal x (free-vars f))
                      (set-difference-equal (vars-in-term tm)
                                            (remove-equal x (free-vars f))))
              (subst-free f x tm))))
  :hints (("Goal"
           :do-not-induct t)))

(defthm var-list-remove-free-vars
  (var-list (remove-equal x (free-vars f))))

(defthm var-list-append-difference
  (implies (and (var-list a)
		(var-list b))
	   (var-list (append a (set-difference-equal b a)))))

(defthm setp-append-difference-helper
  (implies (and (setp (append a (set-difference-equal b a)))
		(not (member-equal x a))
		(not (member-equal x b)))
	   (setp (append a (cons x (set-difference-equal b a))))))

(defthm setp-append-difference
  (implies (and (setp a)
		(setp b))
	   (setp (append a (set-difference-equal b a))))
  :hints (("Goal"
           :do-not generalize)))

;;------------------- The main event

(local (include-book "close"))  ;; for xeval-alls-subset

(defthm instance-xsound-for-1-substitution
  (implies (and (quantifier-free f)   ;; ********* quantifier-free *******
                (xeval (universal-closure f) (domain i) i)
                (variable-term x))
	   (xeval (universal-closure (subst-free f x tm)) (domain i) i))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable quantifier-free free-vars subst-free xeval)
           :use ((:instance instance-xsound-alls-2b
			    (g (subst-free f x tm))
			    (dom (domain i))
                            (w (remove-equal x (free-vars f)))
                            (v (set-difference-equal
                                (vars-in-term tm)
                                (remove-equal x (free-vars f)))))
                 (:instance xeval-alls-subset
                            (b (append (remove-equal x (free-vars f))
                                       (list x)))
                            (a (free-vars f)))
                 (:instance xeval-alls-subset
                            (b (append (remove-equal x (free-vars f))
                                       (set-difference-equal
                                        (vars-in-term tm)
                                        (remove-equal x (free-vars f)))))
                            (a (free-vars (subst-free f x tm)))
                            (f (subst-free f x tm)))
                 )))
  :rule-classes nil)
