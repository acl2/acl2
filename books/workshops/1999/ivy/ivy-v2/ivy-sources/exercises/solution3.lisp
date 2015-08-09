;; Exercise file to accompany
;;
;; Ivy: A Preprocessor and Proof Checker for First-order Logic
;;
;; William McCune (mccune@mcs.anl.gov)
;; Olga Shumsky (shumsky@ece.nwu.edu)
;;
;; Solution for exercise 3.
;;
;; Define a function cnf  that converts negation normal form
;; formulas to conjunctive normal form and a predicate cnfp
;; that recognizes conjunctive normal form formulas.  Prove
;; correctness of the conversion function.

;; Note 1: See book nnf for the predicate nnfp, a recognizer of
;; in negation normal form.

;; Note: to prove correctness in this case means to prove that cnf
;; 	(1) preserves the property wff
;;	(2) converts nnfp formulas to cnfp, and
;;	(3) is sound.

(in-package "ACL2")

;; All neccesary definitions are in:
(include-book "../wfftype")

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
;; Soundness of CNF.

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


