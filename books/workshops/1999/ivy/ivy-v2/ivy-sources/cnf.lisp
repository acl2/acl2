(in-package "ACL2")

;; Conjunctive normal form (CNF): definition, syntactic correctness
;; theorem, soundness theorem, and some preservation-of-property theorems.

(include-book "wfftype")

;; ------------------------------------------------
;; CNF - conjunctive normal form

(defun dist-or-and-2 (p q)
  (declare (xargs :guard (and (wff p) (wff q))))
  (if (wfand q)
      (list 'and (dist-or-and-2 p (a1 q)) (dist-or-and-2 p (a2 q)))
      (list 'or p q)))

(defun dist-or-and (p q)
  (declare (xargs :guard (and (wff p) (wff q))))
  (if (wfand p)
      (list 'and (dist-or-and (a1 p) q) (dist-or-and (a2 p) q))
      (dist-or-and-2 p q)))

(defthm dist-or-and-2-wff  ; helps verify guards for cnf below
  (implies (and (wff p)
		(wff q))
	   (wff (dist-or-and-2 p q))))

(defthm dist-or-and-wff    ; helps verify guards for cnf below
  (implies (and (wff p)
		(wff q))
	   (wff (dist-or-and p q))))

(defun cnf (f)
  (declare (xargs :guard (wff f)))
  (cond ((wfbinary f)
	 (cond ((equal (car f) 'and) (list 'and (cnf (a1 f)) (cnf (a2 f))))
	       ((equal (car f) 'or) (dist-or-and (cnf (a1 f)) (cnf (a2 f))))
	       (t f)))
	((wfquant f) (list (car f) (a1 f) (cnf (a2 f))))
	(t f)))

;; Prove that cnf preserves well-formedness.

(defthm cnf-wff
  (implies (wff f)
	   (wff (cnf f))))

;; Prove that cnf rewrites an nnfp formula into cnfp.

(defthm dist-or-and-2-cnfp
  (implies (and (cnfp p)
		(cnfp q)
		(not (wfand p)))
	   (cnfp (dist-or-and-2 p q))))

(defthm dist-or-and-cnfp
  (implies (and (cnfp p)
		(cnfp q))
	   (cnfp (dist-or-and p q))))

(defthm cnf-cnfp
  (implies (nnfp f)
	   (cnfp (cnf f))))

;;---------------------------------
;; Soundness of CNF.  We use feval.  I think xeval would have been as easy.

(defthm subst-dist-dist-2
  (equal (subst-free (dist-or-and-2 p q) x tm)
	 (dist-or-and-2 (subst-free p x tm)
			(subst-free q x tm))))

(defthm subst-dist-dist
  (equal (subst-free (dist-or-and p q) x tm)
	 (dist-or-and (subst-free p x tm)
		      (subst-free q x tm))))

(defthm subst-cnf-commute
  (equal (subst-free (cnf f) x tm)
	 (cnf (subst-free f x tm))))

(defthm dist-or-and-2-fsound
  (equal (feval (dist-or-and-2 p q) i)
	 (feval (list 'or p q) i)))

(defthm dist-or-and-fsound
  (equal (feval (dist-or-and p q) i)
	 (feval (list 'or p q)  i)))

(defthm cnf-fsound-flg
  (if flg
      (equal (feval (cnf f) i)
	     (feval f i))
      (implies (wfquant f)
	       (equal (feval-d (cnf f) dom i)
		      (feval-d f dom i))))
  :hints (("Goal"
	   :induct (feval-i flg f dom i)))
  :rule-classes nil)

(defthm cnf-fsound
  (equal (feval (cnf f) i)
	 (feval f i))
  :hints (("Goal"
	   :by (:instance cnf-fsound-flg (flg t)))))

;;-------------------------------
;; Prove that cnf preserves closedness.
;; (If you need a theorem that cnf preserves the
;; set of free variables, see normal-forms in the m series.)

(defthm dist-or-and-2-doesnt-introduce-free-vars
  (implies (not (free-occurrence x (list 'or f g)))
	   (not (free-occurrence x (dist-or-and-2 f g)))))

(defthm dist-or-and-doesnt-introduce-free-vars
  (implies (not (free-occurrence x (list 'or f g)))
	   (not (free-occurrence x (dist-or-and f g)))))

(defthm cnf-doesnt-introduce-free-vars
  (implies (not (free-occurrence x f))
	   (not (free-occurrence x (cnf f)))))

(defthm cnf-preserves-closedness-almost
  (implies (not (member-equal x (free-vars f)))
	   (not (member-equal x (free-vars (cnf f)))))
  :hints (("Goal"
	   :use ((:instance free-free)
		 (:instance free-free (f (cnf f)))))))

(defthm cnf-preserves-closedness
  (implies (not (free-vars f))
	   (not (free-vars (cnf f))))
  :hints (("Goal"
	   :use ((:instance member-equal
			    (x (car (free-vars (cnf f))))
			    (lst (free-vars (cnf f))))
		 (:instance member-equal
			    (x (car (free-vars f)))
			    (lst (free-vars f)))))))

;;----------------------
;; cnf preserves quantifier-free

(defthm dist-or-and-2-preserves-quantifier-free
  (implies (and (quantifier-free f)
		(quantifier-free g))
	   (quantifier-free (dist-or-and-2 f g))))

(defthm dist-or-and-preserves-quantifier-free
  (implies (and (quantifier-free f)
		(quantifier-free g))
	   (quantifier-free (dist-or-and f g))))

(defthm cnf-preserves-quantifier-free
  (implies (quantifier-free f)
	   (quantifier-free (cnf f))))

;;--------------------
;; cnf preserves leading-alls

(defthm leading-alls-dist-or-and-2
  (not (leading-alls (dist-or-and-2 f g))))

(defthm leading-alls-dist-or-and
  (not (leading-alls (dist-or-and f g))))

(defthm leading-alls-cnf
  (equal (leading-alls (cnf f)) (leading-alls f)))

;;----------------------

(defthm cnf-of-universal-prefix-nnf-is-universal-prefix-cnf
  (implies (universal-prefix-nnf f)
	   (universal-prefix-cnf (cnf f)))
  :hints (("Goal"
	   :induct (universal-prefix-nnf f))))

