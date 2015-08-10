(in-package "ACL2")

;; This book contain definitions and theorems about bound variables,
;; free variables, and substituting terms for variables.

(include-book "base")

(defthm domain-term-is-not-cons
  (not (domain-term (cons x y)))
  :hints (("Goal"
           :in-theory (enable domain-term))))

(defthm variable-term-is-not-domain-term
  (implies (variable-term x)
	   (not (domain-term x)))
  :hints (("Goal"
	   :in-theory (enable domain-term))))

(defun var-list (l)
  (declare (xargs :guard t))
  (cond ((atom l) (null l))
	(t (and (variable-term (car l))
		(var-list (cdr l))))))

(defthm var-list-union
  (implies (and (var-list a)
		(var-list b))
	   (var-list (union-equal a b))))

(defmacro var-set (vars)
  (list 'and (list 'var-list vars) (list 'setp vars)))

;;------------------------------------------------
;;  Extract the set of variables from a term.

(defun vars-in-term-list (l)
  (declare (xargs :guard (wft-list l)
		  :verify-guards nil))
  (if (atom l)
      nil
      (union-equal (cond ((variable-term (car l)) (list (car l)))
			 ((domain-term (car l)) nil)
			 ((wf-ap-term-top (car l))
			  (vars-in-term-list (cdar l)))
			 (t nil))  ;; non-term
		   (vars-in-term-list (cdr l)))))

(defmacro vars-in-term (tm)
  (list 'vars-in-term-list (list 'list tm)))

(defthm vars-in-term-list-true-listp
  (true-listp (vars-in-term-list l)))

(verify-guards vars-in-term-list)

(defthm vars-in-term-list-returns-var-list
  (var-list (vars-in-term-list l)))

(defthm setp-vars-in-term-list
  (setp (vars-in-term-list l)))

;; ------------------------------------------------------------
;; Function free-vars returns the set of free variables in a formula.

(defun free-vars (f)
  (declare (xargs :guard (wff f)
		  :verify-guards nil))
  (cond ((wfnot f) (free-vars (a1 f)))
	((wfbinary f) (union-equal (free-vars (a1 f))
				   (free-vars (a2 f))))
	((wfquant f) (remove-equal (a1 f) (free-vars (a2 f))))
	((wfatomtop f) (vars-in-term-list (cdr f)))
	(t nil)))

(defthm free-vars-true-listp
  (true-listp (free-vars f)))

(verify-guards free-vars)

(defthm free-vars-returns-var-list
  (var-list (free-vars f)))

(defthm setp-free-vars
  (setp (free-vars f)))

;;=================
;; When I changed the definition of remove-equal so that it doesn't
;; always return a true-listp, the type of free-vars was no longer
;; deduced during definition.  The next two events seem to fix things.

(defthm true-listp-is-either-consp-or-nil
  (implies (true-listp a)
	   (or (consp a)
	       (equal a nil)))
  :rule-classes nil)

(defthm free-vars-type
  (or (consp (free-vars f))
      (equal (free-vars f) nil))
  :hints (("Goal"
	   :use ((:instance true-listp-is-either-consp-or-nil
			    (a (free-vars f))))))
  :rule-classes :type-prescription)

;;=================

(defun var-occurrence-term-list (x l)
  (declare (xargs :guard (and (variable-term x)
			      (wft-list l))))
  (if (atom l)
      nil
    (or (cond ((variable-term (car l)) (equal (car l) x))
	      ((domain-term (car l)) nil)
	      ((wf-ap-term-top (car l)) (var-occurrence-term-list x (cdar l)))
	      (t nil))  ;; non-term
	(var-occurrence-term-list x (cdr l)))))

(defmacro var-occurrence (x tm)
  (list 'var-occurrence-term-list x (list 'list tm)))

;; Function free-occurrence (x f) checks if formula f contains
;; x as a free variable.

(defun free-occurrence (x f)
  (declare (xargs :guard (and (variable-term x) (wff f))))
  (cond ((wfnot f) (free-occurrence x (a1 f)))
	((wfbinary f) (or (free-occurrence x (a1 f))
			  (free-occurrence x (a2 f))))
	((wfquant f) (if (equal x (a1 f))
			 nil
		         (free-occurrence x (a2 f))))
	((wfatomtop f) (var-occurrence-term-list x (cdr f)))
	(t nil)))

(defun bound-occurrence (x f)
  (declare (xargs :guard (and (variable-term x) (wff f))))
  (cond ((wfnot f) (bound-occurrence x (a1 f)))
	((wfbinary f) (or (bound-occurrence x (a1 f))
			  (bound-occurrence x (a2 f))))
	((wfquant f) (if (equal (a1 f) x)
			 t
		         (bound-occurrence x (a2 f))))
	(t nil)))

(defthm free-occurrence-remove-free-vars
  (implies (not (free-occurrence x f))
	   (equal (remove-equal x (free-vars f))
		  (free-vars f)))
  :hints (("Goal"
	   :do-not generalize)))

(defthm true-listp-append-rewrite  ; move to sets?
  (implies (and (true-listp a)
		(true-listp b))
	   (true-listp (append a b))))

(defun quantified-vars (f)
  (declare (xargs :guard (wff f)))
  (cond ((wfnot f) (quantified-vars (a1 f)))
        ((wfbinary f) (append (quantified-vars (a1 f))
                              (quantified-vars (a2 f))))
        ((wfquant f) (cons (a1 f) (quantified-vars (a2 f))))
        (t nil)))

(defthm true-listp-quantified-vars
  (true-listp (quantified-vars f)))

(defthm var-list-quantified-vars
  (var-list (quantified-vars f)))

(defun quantifier-free (f)
  (declare (xargs :guard (wff f)))
  (cond ((wfnot f) (quantifier-free (a1 f)))
        ((wfbinary f) (and (quantifier-free (a1 f))
                           (quantifier-free (a2 f))))
        ((wfquant f) nil)
        (t t)))

(defthm quant-free-subst
  (implies (quantifier-free f)
	   (quantifier-free (subst-free f x tm))))

;;----------- general theorems about bound, free, subst.

(defthm free-free
  (iff (member-equal x (free-vars f))
       (free-occurrence x f))
  :rule-classes nil)

(defthm free-is-free
  (implies (member-equal x (free-vars f))
	   (free-occurrence x f))
  :hints (("Goal"
	   :use ((:instance free-free)))))

(defthm not-free-is-not-free
  (implies (not (member-equal x (free-vars f)))
	   (not (free-occurrence x f)))
  :hints (("Goal"
	   :use ((:instance free-free)))))

(in-theory (disable free-is-free not-free-is-not-free))

(defthm quantified-iff-bound
  (iff (member-equal x (quantified-vars f))
       (bound-occurrence x f))
  :rule-classes nil)

(defthm quantified-is-bound
  (implies (member-equal x (quantified-vars f))
	   (bound-occurrence x f))
  :hints (("Goal"
	   :use ((:instance quantified-iff-bound)))))

(defthm not-quantified-is-not-bound
  (implies (not (member-equal x (quantified-vars f)))
	   (not (bound-occurrence x f)))
  :hints (("Goal"
	   :use ((:instance quantified-iff-bound)))))

(in-theory (disable quantified-is-bound not-quantified-is-not-bound))

;;---------------------

(defthm not-integerp-subst-term-list
  (implies (wft-list l)
	   (not (integerp (subst-term-list l x tm)))))

(defthm not-integerp-subst-term-list-2
  (implies (not (integerp l))
	   (not (integerp (subst-term-list l x tm)))))

(defthm not-wft-list-subst-term-list
  (implies (not (wft-list l))
	   (not (wft-list (subst-term-list l x e))))
  :hints (("Goal"
	   :do-not generalize)))

(defthm not-var-occurrence-subst
  (implies (and (not (var-occurrence-term-list y l))
                (domain-term e))
           (not (var-occurrence-term-list y (subst-term-list l x e)))))

(defthm not-free-subst
  (implies (and (not (free-occurrence y f))
                (domain-term e))
           (not (free-occurrence y (subst-free f x e)))))

(defthm var-occurrence-subst
  (implies (and (var-occurrence-term-list y l)
                (not (equal x y)))
           (var-occurrence-term-list y (subst-term-list l x tm))))

(defthm free-subst
  (implies (and (free-occurrence y f)
		(not (equal x y)))
           (free-occurrence y (subst-free f x tm))))

;;------------------

(defthm not-var-occurrence-not-change-term-list
  (implies (not (var-occurrence-term-list x l))
	   (equal (subst-term-list l x y) l)))

(defthm not-free-not-change
  (implies (not (free-occurrence x f))
	   (equal (subst-free f x tm) f)))

(defthm not-free-not-change-2
  (implies (not (member-equal x (free-vars f)))
           (equal (subst-free f x tm) f))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (enable not-free-is-not-free))))

;; The preceding three cause rewrite explosions, so disable them.

(in-theory (disable not-var-occurrence-not-change-term-list
		    not-free-not-change
		    not-free-not-change-2))

;;-------------------------

(defthm not-bound-occurrence-subst
  (implies (not (bound-occurrence x f))
	   (not (bound-occurrence x (subst-free f y tm)))))

(defthm unique-vars-bound-not-bound
  (implies (and (setp (quantified-vars f))
		(wfquant f))
	   (not (bound-occurrence (a1 f) (a2 f))))
  :hints (("Goal"
           :in-theory (enable not-quantified-is-not-bound))))

(defthm subst-free-preserves-quantifiers
  (equal (quantified-vars (subst-free f x tm))
	 (quantified-vars f)))

;;----------------------

(defthm subst-subst-term-list
  (implies (and (variable-term x)
		(variable-term y)
		(not (var-occurrence-term-list y l)))
	   (equal (subst-term-list (subst-term-list l x y) y tm)
		  (subst-term-list l x tm))))

(defthm subst-subst-free
  (implies (and (variable-term x)
		(variable-term y)
	        (not (bound-occurrence y f))
		(not (free-occurrence y f)))
	   (equal (subst-free (subst-free f x y) y tm)
		  (subst-free f x tm)))
  :hints (("Goal"
	   :in-theory (enable not-free-not-change))))

(defthm subst-free-preserves-bound-vars
  (equal (bound-occurrence x (subst-free f y e))
	 (bound-occurrence x f)))

(defthm subst-term-list-eliminates-var
  (implies (not (var-occurrence-term-list x (list y)))
	   (not (var-occurrence-term-list x (subst-term-list l x y)))))

(defthm another-subst-does-nothing
  (implies (not (var-occurrence-term-list x (list tm)))
	   (equal (subst-free (subst-free f x tm) x d)
		  (subst-free f x tm)))
  :hints (("Goal"
           :in-theory (enable not-var-occurrence-not-change-term-list))))

(defthm subst-term-list-ident
  (equal (subst-term-list l x x) l))

(defthm subst-term-list-different
  (implies (and (not (equal x y))
		(not (var-occurrence-term-list y (list a)))
		(not (var-occurrence-term-list x (list b))))
	   (equal (subst-term-list (subst-term-list l x a) y b)
		  (subst-term-list (subst-term-list l y b) x a)))
  :hints (("Goal"
	   :in-theory (enable not-var-occurrence-not-change-term-list))))

(defthm subst-different
  (implies (and (not (equal x y))
		(not (var-occurrence-term-list y (list a)))
		(not (var-occurrence-term-list x (list b))))
	   (equal (subst-free (subst-free f x a) y b)
		  (subst-free (subst-free f y b) x a))))

(defthm x-not-in-e
  (implies (domain-term e)
	   (not (var-occurrence-term-list x (list e)))))

(defthm x-not-in-y
  (implies (and (variable-term y)
		(not (equal x y)))
	   (not (var-occurrence-term-list x (list y)))))

(defthm subst-different-special-case
  (implies (and (not (equal x y))
		(variable-term a)
		(not (equal a y))
		(domain-term e))
	   (equal (subst-free (subst-free f x a) y e)
		  (subst-free (subst-free f y e) x a))))

(defthm not-var-subst-term-list
  (implies (and (not (var-occurrence-term-list y l))
		(not (var-occurrence-term-list y (list d))))
	   (not (var-occurrence-term-list y (subst-term-list l x d)))))

;;-----------------------

(defthm subst-free-doesnt-introduce-vars
  (implies (and (domain-term e)
		(not (member-equal y (free-vars f))))
	   (not (member-equal y (free-vars (subst-free f x e)))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance free-is-free (x y) (f (subst-free f x e)))
		 (:instance not-free-is-not-free (x y))))))

(defthm remove-equal-not-member  ; move to sets?
  (implies (and (not (remove-equal x a))
		(not (equal y x)))
	   (not (member-equal y a)))
  :rule-classes nil)

(defthm not-member-x-subst-x
  (implies (domain-term e)
           (not (member-equal x (free-vars (subst-free f x e))))))

(defthm vars-alls-free-almost
  (implies (and (domain-term e)
		(not (remove-equal x (free-vars f))))
	   (not (member-equal y (free-vars (subst-free f x e)))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance not-member-x-subst-x)
		 (:instance subst-free-doesnt-introduce-vars)
		 (:instance remove-equal-not-member (a (free-vars f))))
	   :in-theory (disable not-member-x-subst-x
			       subst-free-doesnt-introduce-vars)
	   :do-not generalize)))

;;---------------------------
;; This theorem turns out to be very useful.

(defthm vars-alls-free
  (implies (and (domain-term e)
		(not (remove-equal x (free-vars f))))
	   (not (free-vars (subst-free f x e))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance consp-has-member-equal
			    (x (free-vars (subst-free f x e))))))))

;;--------------------------

(defthm member-vars-subst-term-list
  (implies (and (not (equal x z))
		(member-equal x (vars-in-term-list l)))
	   (member-equal x (vars-in-term-list (subst-term-list l z tm)))))

(defthm not-member-vars-subst-term-list
  (implies (and (variable-term u)
		(not (equal x u))
		(not (member-equal x (vars-in-term-list l))))
	   (not (member-equal x (vars-in-term-list (subst-term-list l z u))))))

(defthm remove-vars-subst-term-list
  (implies (and (variable-term u)
		(not (equal z u))
		(not (var-occurrence-term-list u l)))
	   (equal (remove-equal u (vars-in-term-list (subst-term-list l z u)))
		  (remove-equal z (vars-in-term-list l)))))

;;-------------------------

(defthm subst-term-list-flip-fix
  (implies (and (not (equal x y))
		(domain-term e))
	   (equal
	    (subst-term-list (subst-term-list l x e) y (subst-term tm x e))
	    (subst-term-list (subst-term-list l y tm) x e))))

(defthm subst-flip-fix
  (implies (and (not (equal x y))
		(domain-term e)
		(not (member-equal x (quantified-vars f))))
	   (equal (subst-free (subst-free f x e) y (subst-term tm x e))
		  (subst-free (subst-free f y tm) x e))))
