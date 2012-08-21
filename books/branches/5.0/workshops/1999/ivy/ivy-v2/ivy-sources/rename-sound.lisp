(in-package "ACL2")

;; This book contains the soundess proof for (rename-all f),
;; which is defined in the book "rename".

(include-book "rename")
(include-book "xeval")

;----------------------------

(defthm rename-bound-xsound-top-quant-equal
  (implies (and (wfquant f)
		(variable-term y)
	        (not (bound-occurrence y f))
		(not (free-occurrence y f)))
	   (equal (xeval (rename-bound f (a1 f) y) dom i)
		  (xeval f dom i)))
  :hints (("Goal"
	   :induct (dom-i dom)
	   )))

(defthm subst-rename-commute
  (implies (and (domain-term e)
		(variable-term z)
		(variable-term y)
	        (not (equal y z)))
	   (equal (subst-free (rename-bound f x y) z e)
		  (rename-bound (subst-free f z e) x y))))

(defthm rename-bound-xsound
  (implies (and (variable-term y)
	        (not (bound-occurrence y f))
		(not (free-occurrence y f))
		(domain-term-list (fringe dom))
		)
	   (equal (xeval (rename-bound f x y) dom i)
		  (xeval f dom i)))
  :hints (("Goal"
	   :induct (xeval-i f dom i))))

;-------

(defthm not-bound-occurrence-rename-bound
  (implies (and (not (bound-occurrence v f))
		(not (equal y v)))
	   (not (bound-occurrence v (rename-bound f x y)))))

(defthm not-free-occurrence-rename-bound
  (implies (and (not (free-occurrence v f))
		(not (equal y v)))
	   (not (free-occurrence v (rename-bound f x y)))))

(defthm all-safe-rename-bound
  (implies (and (not (member-equal y vars))
		(var-set vars)
		(not (bound-occurrence y f))
		(not (free-occurrence y f))
		(all-safe vars f))
	   (all-safe vars (rename-bound f x y)))
  :hints (("Goal"
	   :do-not generalize)))

(defthm rename-bunch-xsound
  (implies (and (var-set newvars)
		(all-safe newvars f))
	   (equal (xeval (rename-bunch f oldvars newvars) (domain i) i)
		  (xeval f (domain i) i)))
  :hints (("Goal"
	   :do-not generalize
	   :induct (rename-bunch f oldvars newvars))))

(defthm rename-all-xsound
  (equal (xeval (rename-all f) (domain i) i)
	 (xeval f (domain i) i))
  :hints (("Goal"
	   :do-not-induct t)))

;; Now state it in terms of the official evaluation function feval.

(defthm rename-all-fsound
  (equal (feval (rename-all f) i)
	 (feval f i))
  :hints (("Goal"
	   :in-theory (enable xeval-feval))))

