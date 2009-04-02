(in-package "ACL2")

;; This book is about paramodulation (without unification).
;;
;; We define a function paramod that tries to make one
;; paramodulation inference (on identical terms) at specified
;; positions of two parent clauses.  Then we prove that if
;; the universal closures of the two parents are true in some
;; interpretation, then the universal closure of the paramoudulant
;; is true in that interpretation.

(include-book "stage")

(defun term-at-pos-term-list (a l pos)
  (declare (xargs :guard (and (wft a) (wft-list l) (integer-listp pos))))
  (cond
   ((atom pos) nil)
   ((atom l) nil)
   ((equal (car pos) 1)
    (cond ((variable-term (car l)) (and (atom (cdr pos)) (equal a (car l))))
	  ((domain-term   (car l)) (and (atom (cdr pos)) (equal a (car l))))
	  ((wf-ap-term-top (car l))
	   (if (atom (cdr pos))
	       (equal a (car l))
	     (term-at-pos-term-list a (cdar l) (cdr pos))))
	  (t nil))) ;; non-term
   (t (term-at-pos-term-list a (cdr l) (cons (- (car pos) 1)
					     (cdr pos))))))

;;  (term-at-pos-term-list 'x '(y (f x) z) '(2 1))

(defun term-at-pos (a f pos)
  (declare (xargs :guard (and (wft a) (wff f) (integer-listp pos))))
  (cond ((atom pos) nil)
	((wfnot f) (if (equal (car pos) 1)
		       (term-at-pos a (a1 f) (cdr pos))
		     nil))
	((wfbinary f) (cond ((equal (car pos) 1)
			     (term-at-pos a (a1 f) (cdr pos)))
			    ((equal (car pos) 2)
			     (term-at-pos a (a2 f) (cdr pos)))
			    (t nil)))
	((wfatomtop f) (term-at-pos-term-list a (cdr f) pos))
	(t nil)))

;;  (term-at-pos 'x '(or (p) (q y (f x) z)) '(2 2 1))

(defun replace-at-pos-term-list (a b l pos)
  (declare (xargs :guard (and (wft a) (wft b) (wft-list l) (integer-listp pos))))
  (cond
   ((atom pos) l)
   ((atom l) l)
   ((equal (car pos) 1)
    (cons (cond ((variable-term (car l))
		 (if (and (atom (cdr pos)) (equal a (car l)))
		     b
		     (car l)))
		((domain-term (car l))
		 (if (and (atom (cdr pos)) (equal a (car l)))
		     b
		     (car l)))
		((wf-ap-term-top (car l))
		 (if (atom (cdr pos))
		     (if (equal a (car l))
			 b
		         (car l))
		     (cons (caar l)
			   (replace-at-pos-term-list a b (cdar l) (cdr pos)))))
		(t (car l))) ;; variable term, domain-term, non-term
	  (cdr l)))
   (t (cons (car l)
	    (replace-at-pos-term-list a b (cdr l) (cons (- (car pos) 1)
							(cdr pos)))))))

(defthm replace-at-pos-term-list-preserves-true-listp
  (implies (true-listp l)
	   (true-listp (replace-at-pos-term-list a b l pos))))

(defthm replace-at-pos-term-list-wf
  (implies (and (wft-list l)
		(wft b))
	   (wft-list (replace-at-pos-term-list a b l pos))))

(defthm replace-at-pos-term-list-preserves-len
  (equal (len (replace-at-pos-term-list a b l po))
	 (len l)))

;;------------------------------------------------------
;; replace-at-pos
;; No replacements are made below quantified formulas.
;; If the position doesn't exist, or if a is not at the position,
;; the formula is not changed.

(defun replace-at-pos (a b f pos)
  (declare (xargs :guard (and (wft a) (wft b) (wff f) (integer-listp pos))))
  (cond ((atom pos) f)
	((wfnot f) (if (equal (car pos) 1)
		       (list 'not (replace-at-pos a b (a1 f) (cdr pos)))
		     f))
	((wfbinary f) (cond ((equal (car pos) 1)
			     (list (car f)
				   (replace-at-pos a b (a1 f) (cdr pos))
				   (a2 f)))
			    ((equal (car pos) 2)
			     (list (car f)
				   (a1 f)
				   (replace-at-pos a b (a2 f) (cdr pos))))
			    (t f)))
	((wfatomtop f) (cons (car f)
			     (replace-at-pos-term-list a b (cdr f) pos)))
	(t f)))

;; (replace-at-pos '(a) 'x '(or (p (f (a)) c) (d)) '(1 1 1))

(defthm replace-at-pos-wf
  (implies (and (wff f)
		(wft b))
	   (wff (replace-at-pos a b f pos))))

;-------------------------

(defthm eval-term-list-replace
  (implies (equal (car (eval-term-list (list a) i))
		  (car (eval-term-list (list b) i)))
	   (equal (eval-term-list (replace-at-pos-term-list a b l pos) i)
		  (eval-term-list l i))))

;; These next two lemmas help when paramodulating into an equality
;; (because eval-atomic does that awkward eval-term thing for equalities).

(defthm eval-term-list-replace-car
  (implies
   (and (equal (car (eval-term-list (list a) i))
	       (car (eval-term-list (list b) i)))
	(consp l))
   (equal
    (car (eval-term-list (list (car (replace-at-pos-term-list a b l pos))) i))
    (car (eval-term-list (list (car l)) i)))))

(defthm eval-term-list-replace-cadr
  (implies
   (and (equal (car (eval-term-list (list a) i))
	       (car (eval-term-list (list b) i)))
	(consp l)
	(consp (cdr l)))
   (equal
    (car (eval-term-list (list (cadr (replace-at-pos-term-list a b l pos))) i))
    (car (eval-term-list (list (cadr l)) i)))))

(defthm replace-at-pos-not-true-listp
  (implies (not (true-listp x))
	   (not (true-listp (replace-at-pos-term-list a b x pos)))))

(defthm replace-at-pos-xsound
  (implies (xeval (list '= a b) (domain i) i)
	   (equal (xeval (replace-at-pos a b f pos) dom i)
		  (xeval f dom i)))
  :hints (("Goal"
	   :do-not generalize
	   :in-theory (enable eval-atomic)
	   :induct (replace-at-pos a b f pos))))

;;-----------------------

(defun simp-t-or (f g)
  (declare (xargs :guard (and (wff f) (wff g))))
  (if (or (equal f 'true) (equal g 'true))
      'true
    (list 'or f g)))

(defun paramod (f1 p1 f2 p2)
  (declare (xargs :guard (and (wff f1) (integer-listp p1)
			      (wff f2) (integer-listp p2))))
  (cond ((atom p1) 'true)
	((atom (cdr p1))
	 (cond ((not (wfeq f1)) 'true)
	       ((and (equal (car p1) 1)
		     (term-at-pos (a1 f1) f2 p2))
		(replace-at-pos (a1 f1) (a2 f1) f2 p2))
	       ((and (equal (car p1) 2)
		     (term-at-pos (a2 f1) f2 p2))
		(replace-at-pos (a2 f1) (a1 f1) f2 p2))
	       (t 'true)))
	((wfor f1)
	 (cond ((equal (car p1) 1)
		(simp-t-or (paramod (a1 f1) (cdr p1) f2 p2) (a2 f1)))
	       ((equal (car p1) 2)
		(simp-t-or (a1 f1) (paramod (a2 f1) (cdr p1) f2 p2)))
	       (t 'true)))
	(t 'true)))

;; (paramod '(or (p) (= (a) (b))) '(2 1) '(or (q x (a)) (r)) '(1 2))

(defthm paramod-xsound-ground
  (implies (and (xeval f1 dom i)
		(xeval f2 dom i))
	   (xeval (paramod f1 p1 f2 p2) dom i))
  :hints (("Goal"
	   :in-theory (enable eval-atomic)
	   :induct (paramod f1 p1 f2 p2))))

;;----------------------

(defthm subst-term-list-preserves-len
  (equal (len (subst-term-list l x tm))
	 (len l)))

;;----------------------------
;; (eoft f g): "equal-or-first-true".  This is similar to sub-conj
;; in resolve book, except that it is nonrecursive and simpler.
;; The purpose is the same as for resolve: to get around the problem
;; that subst-free and paramod don't commute.  (See thm
;; paramod-xsound-case2-helper below to see how it fits in.)
;; This messy, and there must be a simpler way to do it.

(defun eoft (f g)
  (declare (xargs :guard (and (wff f) (wff g))))
  (or (equal f g)
      (equal f 'true)))

;-----------------

(defthm subst-term-list-preserves-wf-ap-term-top
  (implies (wf-ap-term-top (cons f args))
	   (wf-ap-term-top (cons f (subst-term-list args x tm)))))

(defthm replace-at-pos-term-list-preserves-wf-ap-term-top
  (implies (wf-ap-term-top (cons f args))
	   (wf-ap-term-top (cons f (replace-at-pos-term-list a b args pos)))))

(defthm wf-ap-term-top-consp
  (implies (not (consp x))
	   (not (wf-ap-term-top x))))

(defthm wf-ap-term-top-is-true-listp
  (implies (wf-ap-term-top tm)
	   (true-listp (cdr tm)))
  :rule-classes :forward-chaining)

(local (in-theory (disable wf-ap-term-top)))

(defthm subst-replace-term-list
  (implies
   (and (term-at-pos-term-list a f2 pos)
	(domain-term e))
   (equal (subst-term-list (replace-at-pos-term-list a b f2 pos) x e)
	  (replace-at-pos-term-list (subst-term a x e)
				    (subst-term b x e)
				    (subst-term-list f2 x e)
				    pos))))

(defthm subst-replace
  (implies (and (term-at-pos a f pos)
		(domain-term e))
	   (equal (subst-free (replace-at-pos a b f pos) x e)
		  (replace-at-pos (subst-term a x e)
				  (subst-term b x e)
				  (subst-free f x e)
				  pos))))

;;----------------------

(defthm subst-true
  (equal (equal (subst-free f x tm) 'true)
	 (equal f 'true)))

(defthm term-at-pos-subst-1
  (implies (and (domain-term e)
		(term-at-pos a f pos))
	   (term-at-pos (subst-term a x e) (subst-free f x e) pos)))

(defthm term-at-pos-subst-2
  (implies (and (domain-term e)
		(variable-term x)
		(term-at-pos x f pos))
	   (term-at-pos e (subst-free f x e) pos)))

(defthm term-at-pos-subst-3
  (implies (and (domain-term e)
		(variable-term y)
		(not (equal y x))
		(term-at-pos y f pos))
	   (term-at-pos y (subst-free f x e) pos)))

(defthm term-at-pos-subst-4
  (implies (and (domain-term e)
		(wf-ap-term-top tm)
		(term-at-pos tm f pos))
	   (term-at-pos (cons (car tm) (subst-term-list (cdr tm) x e))
			(subst-free f x e)
			pos))
  :hints (("goal"
           :in-theory (enable wf-ap-term-top))))

(defthm term-at-pos-subst-5
  (implies (and (domain-term e)
		(not (variable-term y))
		(not (wf-ap-term-top y))
		(term-at-pos y f pos))
	   (term-at-pos y (subst-free f x e) pos)))

(defthm term-at-pos-subst-6
  (implies (and (domain-term e)
		(domain-term ee)
		(term-at-pos ee f pos))
	   (term-at-pos ee (subst-free f x e) pos)))

(local (include-book "arithmetic"))

; The following was modified by Matt Kaufmann, June 2001, in order to
; accommodate the new rewrite rule equal-constant-+-left in the
; arithmetic/equalities book.

#|
(defthm len-0-list-forward
  (implies (and (true-listp l)
		(equal (+ n (len l)) n))
	   (equal l nil))
  :rule-classes :forward-chaining)
|#

(defthm len-0-list-forward
  (implies (and (true-listp l)
		(equal (len l) 0))
	   (equal l nil))
  :rule-classes :forward-chaining)

;----------------------------

(defthm eoft-paramod
  (implies (domain-term e)
	   (eoft (subst-free (paramod f1 p1 f2 p2) x e)
		 (paramod (subst-free f1 x e) p1
			  (subst-free f2 x e) p2)))
  :hints (("Goal"
	   :induct (paramod f1 p1 f2 p2)
	   :do-not generalize)))

(defthm eoft-subst
  (implies (eoft q p)
	   (eoft (subst-free q x tm) (subst-free p x tm))))

(defthm eoft-xeval
  (implies (and (eoft q p)
		(xeval p dom i))
	   (xeval q dom i))
  :hints (("Goal"
	   :do-not generalize
	   :induct (xeval-i p dom i))))

(defthm eoft-xeval-vars
  (implies (and (var-set vars)
		(eoft q p)
		(xeval (alls vars p) dom i))
	   (xeval (alls vars q) dom i))
  :hints (("Goal"
	   :do-not generalize
	   :in-theory (disable eoft)
	   :expand ((alls vars p) (alls vars q))
	   :induct (var-induct-2 vars p q dom i))))

(defthm paramod-xsound-case2-helper
  (implies
   (and (variable-term x)
	(var-set vars)
	(not (member-equal x vars))
	(domain-term e)
	(xeval (alls vars (paramod (subst-free f1 x e) p1
				   (subst-free f2 x e) p2)) (domain i) i) )
   (xeval (alls vars (subst-free (paramod f1 p1 f2 p2) x e)) (domain i) i))
  :hints (("Goal"
         :use ((:instance eoft-xeval-vars
			  (dom (domain i))
			  (q (subst-free (paramod f1 p1 f2 p2) x e))
			  (p (paramod (subst-free f1 x e) p1
				      (subst-free f2 x e) p2)))))))

(defthm paramod-xsound-alls
  (implies (and (var-set vars)
		(domain-term-list (fringe dom))
		(xeval (alls vars f1) dom i)
		(xeval (alls vars f2) dom i))
	   (xeval (alls vars (paramod f1 p1 f2 p2)) dom i))
  :hints (("Goal"
	   :induct (var-induct-2 vars f1 f2 dom i)
	   :do-not generalize
	   :in-theory (disable paramod))
	  ("Subgoal *1/3"
	   :expand ((alls vars f1) (alls vars f2)))))
		
;;-----------------------------
;; Now, get it in terms of universal-closure.

(encapsulate
 nil
 (local (include-book "close"))
 (defthm xeval-alls-subset
   (implies (and (var-set a)
		 (var-set b)
		 (subsetp-equal a b)
		 (not (free-vars (alls a f))))
	    (equal (xeval (alls a f) (domain i) i)
		   (xeval (alls b f) (domain i) i)))
   :rule-classes nil)
 )

(defthm paramod-xsound-closure
  (implies (and (xeval (universal-closure f) (domain i) i)
		(xeval (universal-closure g) (domain i) i))
           (xeval (universal-closure (paramod f fp g gp)) (domain i) i))
  :hints
  (("Goal"
    :do-not-induct t
    :use ((:instance xeval-alls-subset
		     (f f)
		     (a (free-vars f))
		     (b (union-equal
			 (free-vars f)
			 (union-equal (free-vars g)
				      (free-vars (paramod f fp g gp))))))
	  (:instance xeval-alls-subset
		     (f g)
		     (a (free-vars g))
		     (b (union-equal
			 (free-vars f)
			 (union-equal (free-vars g)
				      (free-vars (paramod f fp g gp))))))
	  (:instance xeval-alls-subset
		     (f (paramod f fp g gp))
		     (a (free-vars (paramod f fp g gp)))
		     (b (union-equal
			 (free-vars f)
			 (union-equal (free-vars g)
				      (free-vars (paramod f fp g gp))))))
	  ))))
