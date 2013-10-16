(in-package "ACL2")

;; This book is about syntactic properties of formulas.
;; As the formula goes through the preprocessing
;; steps, it has various properties along the way.
;; Most of these functions are recognizers for those properties.

(include-book "alls")

(defmacro noncomplex-formula (f)
  (list 'not (list 'or
		   (list 'wfnot f)
		   (list 'wfbinary f)
		   (list 'wfquant f))))

(defmacro simple-formula (f)
  (list 'or
	(list 'equal f ''true)
	(list 'equal f ''false)
	(list 'wfatom f)))

;; Function nnfp (f) checks if a formula is in negation normal form.

(defun nnfp (f)
  (declare (xargs :guard t))
  (cond ((wfnot f) (noncomplex-formula (a1 f)))
	((wfbinary f)
	 (cond ((equal (car f) 'and) (and (nnfp (a1 f)) (nnfp (a2 f))))
	       ((equal (car f) 'or)  (and (nnfp (a1 f)) (nnfp (a2 f))))
	       (t nil)))  ; imp, iff not allowed
	((wfquant f) (nnfp (a2 f)))
	((noncomplex-formula f) t)
	(t nil)))

;; Prove that subst-free preserves nnfp.

(defthm subst-free-preserves-car
  (equal (car (subst-free f x tm)) (car f)))

(defthm subst-free-preserves-nnfp
  (implies (nnfp f)
           (nnfp (subst-free f x tm))))

;; Function cnfp (f) checks if a formula is in conjunctive normal form.
;; Note the handling of quantified formulas: the superformula treats
;; it as an atomic formula, and the subformula must be cnfp.

(defun cnfp (f)
  (declare (xargs :guard t))
  (cond ((noncomplex-formula f) t)
	((wfnot f) (noncomplex-formula (a1 f)))
	((wfbinary f)
	 (cond ((wfor f) (and (cnfp (a1 f))
			      (cnfp (a2 f))
			      (not (wfand (a1 f)))
			      (not (wfand (a2 f)))))
	       ((wfand f) (and (cnfp (a1 f))
			       (cnfp (a2 f))))
	       (t nil))) ; imp, iff not allowed
	((wfquant f) (cnfp (a2 f)))
	(t nil)))

;; Prove that subst-free preserves cnfp.

(defthm subst-free-preserves-cnfp
  (implies (cnfp f)
           (cnfp (subst-free f x tm))))

;; Prove that cnfp formulas are always nnfp.

(defthm cnfp-nnfp
  (implies (cnfp f) (nnfp f)))

(in-theory (disable cnfp-nnfp))

;;----------------------
;; Universal-prefix-nnf means that there is a sequence of universal
;; quantifiers at the top, and the rest of the formula is quantifier-free nnf.
;; The other functions are analogous.

(defun universal-prefix-nnf (f)
  (declare (xargs :guard (wff f)))
  (cond ((wfall f) (universal-prefix-nnf (a2 f)))
	(t (and (nnfp f) (quantifier-free f)))))

(defun universal-prefix-cnf (f)
  (declare (xargs :guard (wff f)))
  (cond ((wfall f) (universal-prefix-cnf (a2 f)))
	(t (and (cnfp f) (quantifier-free f)))))

(defun quant-prefix-nnf (f)
  (declare (xargs :guard (wff f)))
  (cond ((wfquant f) (quant-prefix-nnf (a2 f)))
	(t (and (nnfp f) (quantifier-free f)))))

(defun quant-prefix-cnf (f)
  (declare (xargs :guard (wff f)))
  (cond ((wfquant f) (quant-prefix-cnf (a2 f)))
	(t (and (cnfp f) (quantifier-free f)))))

;;------------------------------------------------------------
;; Right-assoc-p checks if all of the conjunctions and disjunctions
;; are right associated.

(defun right-assoc-p (f)  ;; no 'and has and 'and as left child; same for 'or.
  (declare (xargs :guard (and (wff f))))
  (cond ((wfand f) (and (not (wfand (a1 f)))
			(right-assoc-p (a1 f))
			(right-assoc-p (a2 f))))
	((wfor f) (and (not (wfor (a1 f)))
		       (right-assoc-p (a1 f))
		       (right-assoc-p (a2 f))))
	((wfbinary f) (and (right-assoc-p (a1 f))
			   (right-assoc-p (a2 f))))
	((wfnot f) (right-assoc-p (a1 f)))
	((wfquant f) (right-assoc-p (a2 f)))
	(t t)))

;;------------------------------------------------------------
;; Acceptable input for Skolemization.

(defun funcs-in-term-list (l)
  (declare (xargs :guard (wft-list l)
		  :verify-guards nil))
  (if (atom l)
      nil
      (union-equal (cond ((domain-term (car l)) nil)
			 ((variable-term (car l)) nil)
			 ((wf-ap-term-top (car l))
			  (union-equal (list (caar l))
				       (funcs-in-term-list (cdar l))))
			 (t nil)) ;; non-term
		   (funcs-in-term-list (cdr l)))))

(defthm true-listp-funcs-in-term-list ; for verifying guards
  (true-listp (funcs-in-term-list l)))

(verify-guards funcs-in-term-list)

(defun funcs-in-formula (f)
  (declare (xargs :guard (wff f)))
  (cond ((wfnot f) (funcs-in-formula (a1 f)))
	((wfbinary f) (union-equal (funcs-in-formula (a1 f))
				   (funcs-in-formula (a2 f))))
	((wfquant f) (funcs-in-formula (a2 f)))
	((wfatomtop f) (funcs-in-term-list (cdr f)))
	(t nil)))

(defthm true-listp-funcs-in-formula
  (true-listp (funcs-in-formula f)))

(defun ok-for-skolem (f)
  (declare (xargs :guard (wff f)))
  (and (nnfp f)
       (not (free-vars f))
       (setp (quantified-vars f))))

;; Skolemization should produce a formula without existential quantifiers.

(defun exists-count (f)
  (declare (xargs :guard (wff f)))
  (cond ((wfnot f)    (exists-count (a1 f)))
        ((wfbinary f) (+ (exists-count (a1 f)) (exists-count (a2 f))))
        ((wfexists f) (+ 1 (exists-count (a2 f))))
        ((wfall f)    (exists-count (a2 f)))
        (t 0)))

;;--------------------
;; odds and ends

(defthm quant-free-cnf-is-universal-prefix-cnf
  (implies (and (cnfp f)
		(quantifier-free f))
	   (universal-prefix-cnf f))
  :hints (("Goal"
	   :induct (universal-prefix-cnf f))))

(defthm universal-prefix-exists-free
  (implies (and (quant-prefix-nnf f)
		(equal (exists-count f) 0))
	   (universal-prefix-nnf f)))

(defthm qfree-remq-quant-prefix-nnf
  (implies (and (nnfp f)
		(quantifier-free (remove-leading-quants f)))
	   (quant-prefix-nnf f))
  :hints (("Goal"
	   :induct (quant-prefix-nnf f))))

;;------------------------------------------------------------
;; Functions (cdrs l) is different from (strip-cdrs l) in that
;; the argument does not have to be an alistp.  Same for (cdrs l).

(defun cars (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((atom l) nil)
	((consp (car l)) (cons (caar l) (cars (cdr l))))
	(t (cars (cdr l)))))

(defun cdrs (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((atom l) nil)
	((consp (car l)) (cons (cdar l) (cdrs (cdr l))))
	(t (cdrs (cdr l)))))

