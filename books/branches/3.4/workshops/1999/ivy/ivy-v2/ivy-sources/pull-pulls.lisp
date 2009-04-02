(in-package "ACL2")

;; Here we prove that (pull f) brings all of the quantifiers to
;; the top if f is closed, nnf, with unique quantified variables.

(include-book "pull")

(defmacro quant-prefix (f)
  (list 'quantifier-free (list 'remove-leading-quants f)))

(defthm ptl-quant-prefix-nnf-b
  (implies (and (quant-prefix f)
		(disjoint (quantified-vars f)
			  (free-vars g))
		(or (equal op 'and) (equal op 'or)))
	   (quantifier-free
	    (a1 (remove-leading-quants (pull-top-left op f g)))))
  :hints (("Goal"
	   :in-theory (enable not-free-is-not-free)
	   :do-not generalize
	   :induct (pull-top-left op f g))))

(defthm ptr-quant-prefix-nnf-2-b
  (implies (and (quant-prefix g)
		(quantifier-free f)    ;; a little different from ptl
		(disjoint (quantified-vars g)
			  (free-vars f))
		(or (equal op 'and) (equal op 'or)))
	   (quant-prefix (pull-top-right op f g)))
  :hints (("goal"
	   :in-theory (enable not-free-is-not-free)
	   :do-not generalize
	   :induct (pull-top-right op f g))))

(defthm down-right-prefix-nnf-b
  (implies (and (or (wfand (remove-leading-quants f))
		    (wfor (remove-leading-quants f)))
		(quantifier-free (a1 (remove-leading-quants f)))
		(quant-prefix (a2 (remove-leading-quants f)))
		(disjoint (quantified-vars (a2 (remove-leading-quants f)))
			  (free-vars (a1 (remove-leading-quants f)))))
	   (quant-prefix (down-right f)))
  :hints (("Goal"
	   :do-not generalize
	   :induct (down-right f))))

;;----------------------------

(defthm quantifier-free-means-no-quantifiers
  (implies (quantifier-free f)
	   (equal (quantified-vars f) nil)))

(defthm ptr-preserves-qvars
  (implies (and (or (equal op 'and) (equal op 'or))
		(quantifier-free f))
	   (equal (quantified-vars (pull-top-right op f g))
		  (quantified-vars g))))

;;-----------------------

(defthm disjoint-union-special-1
  (implies
   (and (not (disjoint e (union-equal c d)))
	(not (member-equal x e)))
   (not	(disjoint e (union-equal (remove-equal x c) d)))))

;;----------------------------

(defthm wfand-remove-quants-ptl
  (wfand (remove-leading-quants (pull-top-left 'and f g))))

(defthm wfor-remove-quants-ptl
  (wfor (remove-leading-quants (pull-top-left 'or f g))))

;;-------------------- First do 'and

(defthm ptl-quant-lemma-and
  (implies (and (disjoint (append (quantified-vars f)
				  (quantified-vars g))
			  (union-equal (free-vars f)
				       (free-vars g)))
		(setp (append (quantified-vars f)
			      (quantified-vars g)))
		)
	   (disjoint (quantified-vars g)
		     (free-vars
		      (a1 (remove-leading-quants (pull-top-left 'and f g))))))
  :hints (("goal"
	   :do-not generalize
	   :induct (pull-top-left 'and f g))))

(defthm ptl-a2-and
  (equal (a2 (remove-leading-quants (pull-top-left 'and f g))) g))

(defthm heart-and
  (implies
   (and (quantifier-free (remove-leading-quants f))
	(quantifier-free (remove-leading-quants g))
	(nnfp f)
	(nnfp g)
	(setp (append (quantified-vars f)
		      (quantified-vars g)))
	(disjoint (append (quantified-vars f)
			  (quantified-vars g))
		  (union-equal (free-vars f)
			       (free-vars g)))
	)
   (quantifier-free
    (remove-leading-quants (down-right (pull-top-left 'and f g)))))
  :hints (("goal"
	   :do-not-induct t
	   :use ((:instance down-right-prefix-nnf-b
			    (f (pull-top-left 'and f g)))
		 (:instance ptl-quant-prefix-nnf-b
			    (op 'and)))
	   :in-theory (disable down-right-prefix-nnf-b
			       ptl-quant-prefix-nnf-b
			       pull)))
  :rule-classes nil)

(defthm heart-and-fix
  (implies (and (quantifier-free (remove-leading-quants (pull f)))
		(quantifier-free (remove-leading-quants (pull g)))
		(nnfp f)
		(nnfp g)
		(setp (append (quantified-vars f)
			      (quantified-vars g)))
		(disjoint (append (quantified-vars f)
				  (quantified-vars g))
			  (union-equal (free-vars f)
				       (free-vars g))))
	   (quantifier-free
	    (remove-leading-quants (down-right (pull-top-left 'and
							      (pull f)
							      (pull g))))))
  :hints (("goal"
	   :do-not-induct t
	   :hands-off (pull down-right pull-top-left)
           :use ((:instance heart-and (f (pull f)) (g (pull g)))))))

;;----------------- now do 'or

(defthm ptl-quant-lemma-or
  (implies (and (disjoint (append (quantified-vars f)
				  (quantified-vars g))
			  (union-equal (free-vars f)
				       (free-vars g)))
		(setp (append (quantified-vars f)
			      (quantified-vars g))))
	   (disjoint (quantified-vars g)
		     (free-vars
		      (a1 (remove-leading-quants (pull-top-left 'or f g))))))
  :hints (("goal"
	   :do-not generalize
	   :induct (pull-top-left 'or f g))))

(defthm ptl-a2-or
  (equal (a2 (remove-leading-quants (pull-top-left 'or f g))) g))

(defthm heart-or
  (implies
   (and (quantifier-free (remove-leading-quants f))
	(quantifier-free (remove-leading-quants g))
	(nnfp f)
	(nnfp g)
	(setp (append (quantified-vars f)
		      (quantified-vars g)))
	(disjoint (append (quantified-vars f)
			  (quantified-vars g))
		  (union-equal (free-vars f)
			       (free-vars g))))
   (quantifier-free
    (remove-leading-quants (down-right (pull-top-left 'or f g)))))
  :hints (("goal"
	   :do-not-induct t
	   :use ((:instance down-right-prefix-nnf-b
			    (f (pull-top-left 'or f g)))
		 (:instance ptl-quant-prefix-nnf-b
			    (op 'or)))
	   :in-theory (disable down-right-prefix-nnf-b
			       ptl-quant-prefix-nnf-b
			       pull)))
  :rule-classes nil)

(defthm heart-or-fix
  (implies (and (quantifier-free (remove-leading-quants (pull f)))
		(quantifier-free (remove-leading-quants (pull g)))
		(nnfp f)
		(nnfp g)
		(setp (append (quantified-vars f)
			      (quantified-vars g)))
		(disjoint (append (quantified-vars f)
				  (quantified-vars g))
			  (union-equal (free-vars f)
				       (free-vars g))))
	   (quantifier-free
	    (remove-leading-quants (down-right (pull-top-left 'or
							      (pull f)
							      (pull g))))))
  :hints (("goal"
	   :do-not-induct t
	   :hands-off (pull down-right pull-top-left)
           :use ((:instance heart-or (f (pull f)) (g (pull g)))))))

;;-----------------------
;; dvprop - a formula has this property if, at each subformula,
;; the free variables are disjoint from the quantified variables.

(defun dvprop (f)
  (declare (xargs :guard (wff f)))
  (and (disjoint (quantified-vars f)
		 (free-vars f))
       (cond ((wfnot f) (dvprop (a1 f)))
	     ((wfbinary f) (and (dvprop (a1 f)) (dvprop (a2 f))))
	     ((wfquant f) (dvprop (a2 f)))
	     (t t))))

(defthm dvprop-ptl
  (implies (and (or (equal op 'and) (equal op 'or))
		(setp (quantified-vars (list op f g)))
		(dvprop (list op f g)))
	   (dvprop (pull-top-left op f g)))
  :hints (("Goal"
	   :induct (pull-top-left op f g))))

(defthm pull-prefix-quant-1
  (implies (and (nnfp f)
		(setp (quantified-vars f))
		(dvprop f))
	   (quantifier-free (remove-leading-quants (pull f))))
  :hints (("Goal"
	   :induct (pull f)
	   :do-not generalize)))

;; If the quantified variables are a setp, and the disjointness
;; property holds at the top, then the disjointness property
;; holds everywhere.

(defthm setp-quants-disjoint-dvprop
  (implies (and (setp (quantified-vars f))
		(disjoint (quantified-vars f)
			  (free-vars f)))
	   (dvprop f))
  :rule-classes nil)

;;-----------------------------------
;; Here are the theorems for pull and for pull-quants.

(defthm pull-pulls
  (implies (and (nnfp f)
		(setp (quantified-vars f))
		(not (free-vars f)))
	   (quantifier-free (remove-leading-quants (pull f))))
  :hints (("Goal"
	   :do-not-induct t
	   :hands-off (pull)
	   :use ((:instance setp-quants-disjoint-dvprop)))))

(defthm pull-quants-pulls
  (implies (and (nnfp f)
		(setp (quantified-vars f))
		(not (free-vars f)))
	   (quantifier-free (remove-leading-quants (pull-quants f))))
  :hints (("Goal"
	   :do-not-induct t
	   :hands-off (pull)
           :in-theory (enable pull-quants))))

;;------------------------------------------

(defthm pull-quants-pulls-2
  (implies (and (nnfp f)
		(not (free-vars f))
		(setp (quantified-vars f))
		(equal (exists-count f) 0))
	   (universal-prefix-nnf (pull-quants f)))
  :hints (("Goal"	
	   :in-theory (disable pull)
	   :do-not-induct t)))

