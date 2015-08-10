(in-package "ACL2")

;; Negation normal form (NNF): definition, syntactic correctness
;; theorem, soundness theorem, and some preservation-of-property theorems.

(include-book "stage")

(defmacro car-and (f)    (list 'equal (list 'car f) ''and))
(defmacro car-or (f)     (list 'equal (list 'car f) ''or))
(defmacro car-imp (f)    (list 'equal (list 'car f) ''imp))
(defmacro car-iff (f)    (list 'equal (list 'car f) ''iff))
(defmacro car-all (f)    (list 'equal (list 'car f) ''all))
(defmacro car-exists (f) (list 'equal (list 'car f) ''exists))

;;==================================================================
;; Function nnf converts a formula to negation normal form.
;; That is, in terms of and/or/not, where all nots are up against
;; simple formulas.  ('true and 'false are not simplified away.)

(defun nnf (f)
  (declare (xargs :guard (wff f)))
  (cond
   ((wfbinary f)
    (cond ((car-and f) (list 'and (nnf (a1 f)) (nnf (a2 f))))
	  ((car-or  f) (list 'or  (nnf (a1 f)) (nnf (a2 f))))
	  ((car-imp f) (list 'or  (nnf (list 'not (a1 f))) (nnf (a2 f))))
	  ((car-iff f) (list 'and
			     (list 'or (nnf (list 'not (a1 f))) (nnf (a2 f)))
			     (list 'or (nnf (a1 f)) (nnf (list 'not (a2 f))))))
	  (t f)))  ; should not happen if (wff f)

   ((wfquant f)
    (cond ((car-all    f) (list 'all    (a1 f) (nnf (a2 f))))
	  ((car-exists f) (list 'exists (a1 f) (nnf (a2 f))))
	  (t f)))  ; should not happen if (wff f)

   ((wfnot f)
    (cond ((wfbinary (a1 f))
	   (cond ((car-and (a1 f)) (list 'or
					 (nnf (list 'not (a1 (a1 f))))
					 (nnf (list 'not (a2 (a1 f))))))
		 ((car-or (a1 f))  (list 'and
					 (nnf (list 'not (a1 (a1 f))))
					 (nnf (list 'not (a2 (a1 f))))))
		 ((car-imp (a1 f)) (list 'and
					 (nnf (a1 (a1 f)))
					 (nnf (list 'not (a2 (a1 f))))))
		 ((car-iff (a1 f)) (list 'and
					 (list 'or
					       (nnf (a1 (a1 f)))
					       (nnf (a2 (a1 f))))
					 (list 'or
					       (nnf (list 'not (a1 (a1 f))))
					       (nnf (list 'not (a2 (a1 f)))))))
		 (t f)))  ; should not happen if (wff f)
	  ((wfquant (a1 f))
	   (cond ((car-all (a1 f))
		  (list 'exists (a1 (a1 f)) (nnf (list 'not (a2 (a1 f))))))
		 ((car-exists (a1 f))
		  (list 'all (a1 (a1 f)) (nnf (list 'not (a2 (a1 f))))))
		 (t f)))  ; should not happen if (wff f)

	  ((wfnot (a1 f)) (nnf (a1 (a1 f))))
	  (t f)))
   (t f)))

;; Prove that nnf preserves well-formedness.

(defthm nnf-wff
  (implies (wff f)
	   (wff (nnf f))))

;; Prove that nnf applied to a wff gives negation normal form.

(defthm nnf-nnfp
  (implies (wff x)
	   (nnfp (nnf x))))

(defthm subst-nnf-commute
  (equal (subst-free (nnf f) x tm)
	 (nnf (subst-free f x tm))))

;;---------------------------------
;; Prove that nnf is sound.  The proof seems to be easier with xeval.

(defthm nnf-xsound-for-not
  (equal (xeval (nnf (list 'not f)) dom i)
	 (xeval (list 'not (nnf f)) dom i))
  :hints (("Goal"
	   :induct (xeval-i f dom i))))

(defthm nnf-xsound
  (equal (xeval (nnf f) dom i)
	 (xeval f dom i))
  :hints (("Goal"
	   :induct (xeval-i f dom i))))

(defthm nnf-fsound
  (equal (feval (nnf f) i)
	 (feval f i))
  :hints (("Goal"
	   :in-theory (enable xeval-feval))))

;;---------------------------------
;; Prove that nnf preserves the set of free variables.

(defthm nnf-preserves-free-vars
  (equal (free-vars (nnf f)) (free-vars f)))

