(in-package "ACL2")

;; Soundness of the pull-quant functions.

(include-book "pull")

;;---------------------------------------------------------------------
;; Soundness of pull-top-left and pull-top-right.
;;
;; There are 8 cases: and/or, left/right, and both directions of <=>.
;; All 8 cases do induction using meval-i.  I'd like to find a
;; simpler way to prove this.
;;
;; Working on this caused me to write the first mutually
;; recursive evaluation function (thanks to the ACL2 docs for the
;; clear mutual recursion example).  Because the mutually
;; recursive eval function is clearest, it is now the official eval.

(defthm subst-ptr-dist
  (implies (and (not (free-occurrence x a))
		(or (equal op 'and) (equal op 'or)))
	   (equal (subst-free (pull-top-right op a b) x e)
		  (pull-top-right op a (subst-free b x e))))
  :hints (("Goal"
           :in-theory (enable not-free-not-change))))

;; 'or for pull-top-right

(defthm ptr-or-fsound-1-mutual
  (if flg
      (implies (feval (pull-top-right 'or f g) i)
	       (feval (list 'or f g) i))
    (implies (and (wfquant (pull-top-right 'or f g))
		  (wfquant g)
		  (feval-d (pull-top-right 'or f g) dom i))
	     (or (feval f i)
		 (feval-d g dom i))))
  :hints (("Goal"
           :induct (feval-i flg g dom i)))
  :rule-classes nil)

(defthm ptr-or-fsound-2-mutual
  (if flg
      (implies (feval (list 'or f g) i)
	       (feval (pull-top-right 'or f g) i))
    (implies (and (wfquant g)
		  (wfquant (pull-top-right 'or f g))
		  (or (feval f i)
		      (feval-d g dom i)))
	     (feval-d (pull-top-right 'or f g) dom i)))
  :hints (("Goal"
           :induct (feval-i flg g dom i)))
  :rule-classes nil)

(defthm ptr-or-fsound
  (equal (feval (pull-top-right 'or f g) i)
	 (feval (list 'or f g) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance ptr-or-fsound-1-mutual
			    (flg t) (dom 'junk) (i i) (f f) (g g))
		 (:instance ptr-or-fsound-2-mutual
			    (flg t) (dom 'junk) (i i) (f f) (g g))))))

;; 'and for pull-top-right

(defthm ptr-and-fsound-1-mutual
  (if flg
      (implies (feval (pull-top-right 'and f g) i)
	       (feval (list 'and f g) i))
    (implies (and (wfquant g)
		  (feval-d (pull-top-right 'and f g) dom i))
	     (and (feval f i)
		  (feval-d g dom i))))
  :hints (("Goal"
           :induct (feval-i flg g dom i)))
  :rule-classes nil)

(defthm ptr-and-fsound-2-mutual
  (if flg
      (implies (feval (list 'and f g) i)
	       (feval (pull-top-right 'and f g) i))
    (implies (and (wfquant g)
		  (wfquant (pull-top-right 'and f g))
		  (and (feval f i)
		       (feval-d g dom i)))
	     (feval-d (pull-top-right 'and f g) dom i)))
  :hints (("Goal"
           :induct (feval-i flg g dom i)))
  :rule-classes nil)

(defthm ptr-and-fsound
  (equal (feval (pull-top-right 'and f g) i)
	 (feval (list 'and f g) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance ptr-and-fsound-1-mutual
			    (flg t) (dom 'junk) (i i) (f f) (g g))
		 (:instance ptr-and-fsound-2-mutual
			    (flg t) (dom 'junk) (i i) (f f) (g g))))))

;; Ok, here is the soundness theorem for pull-top-right.

(defthm ptr-fsound
  (equal (feval (pull-top-right op f g) i)
	 (feval (list op f g) i))
  :hints (("Goal"
	   :do-not-induct t
	   :expand (pull-top-right op f g)
	   :use ((:instance ptr-and-fsound)
		 (:instance ptr-or-fsound))
	   :in-theory (disable feval wfquant
			       ptr-and-fsound ptr-or-fsound))))

;; Now, do EXACTLY the same thing for pull-top-left.

(defthm subst-ptl-dist
  (implies (and (not (free-occurrence x b))
		(or (equal op 'and) (equal op 'or)))
	   (equal (subst-free (pull-top-left op a b) x e)
		  (pull-top-left op (subst-free a x e) b)))
  :hints (("Goal"
           :in-theory (enable not-free-not-change))))

;; 'or for pull-top-left

(defthm ptl-or-fsound-1-mutual
  (if flg
      (implies (feval (pull-top-left 'or f g) i)
	       (feval (list 'or f g) i))
    (implies (and (wfquant (pull-top-left 'or f g))
		  (wfquant f)
		  (feval-d (pull-top-left 'or f g) dom i))
	     (or (feval g i)
		 (feval-d f dom i))))
  :hints (("Goal"
           :induct (feval-i flg f dom i)))
  :rule-classes nil)

(defthm ptl-or-fsound-2-mutual
  (if flg
      (implies (feval (list 'or f g) i)
	       (feval (pull-top-left 'or f g) i))
    (implies (and (wfquant f)
		  (wfquant (pull-top-left 'or f g))
		  (or (feval g i)
		      (feval-d f dom i)))
	     (feval-d (pull-top-left 'or f g) dom i)))
  :hints (("Goal"
           :induct (feval-i flg f dom i)))
  :rule-classes nil)

(defthm ptl-or-fsound
  (equal (feval (pull-top-left 'or f g) i)
	 (feval (list 'or f g) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance ptl-or-fsound-1-mutual
			    (flg t) (dom 'junk) (i i) (f f) (g g))
		 (:instance ptl-or-fsound-2-mutual
			    (flg t) (dom 'junk) (i i) (f f) (g g))))))

;; 'and for pull-top-left

(defthm ptl-and-fsound-1-mutual
  (if flg
      (implies (feval (pull-top-left 'and f g) i)
	       (feval (list 'and f g) i))
    (implies (and (wfquant f)
		  (feval-d (pull-top-left 'and f g) dom i))
	     (and (feval g i)
		  (feval-d f dom i))))
  :hints (("Goal"
           :induct (feval-i flg f dom i)))
  :rule-classes nil)

(defthm ptl-and-fsound-2-mutual
  (if flg
      (implies (feval (list 'and f g) i)
	       (feval (pull-top-left 'and f g) i))
    (implies (and (wfquant f)
		  (wfquant (pull-top-left 'and f g))
		  (and (feval g i)
		       (feval-d f dom i)))
	     (feval-d (pull-top-left 'and f g) dom i)))
  :hints (("Goal"
           :induct (feval-i flg f dom i)))
  :rule-classes nil)

(defthm ptl-and-fsound
  (equal (feval (pull-top-left 'and f g) i)
	 (feval (list 'and f g) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance ptl-and-fsound-1-mutual
			    (flg t) (dom 'junk) (i i) (f f) (g g))
		 (:instance ptl-and-fsound-2-mutual
			    (flg t) (dom 'junk) (i i) (f f) (g g))))))

;; Ok, here is the soundness theorem for pull-top-left.

(defthm ptl-fsound
  (equal (feval (pull-top-left op f g) i)
	 (feval (list op f g) i))
  :hints (("Goal"
	   :do-not-induct t
	   :expand (pull-top-left op f g)
	   :use ((:instance ptl-and-fsound (i i) (f f) (g g))
		 (:instance ptl-or-fsound  (i i) (f f) (g g)))
	   :in-theory (disable feval wfquant
			       ptl-and-fsound ptl-or-fsound))))

;;========================================================================
;; For soundness of down-right and pull, we have the hypothesis
;; (setp (quantified-vars f)).  I'm pretty sure this is not necessary,
;; but I didn't see how to get the proofs without it.  This not a problem,
;; because in the the applications I envision, formulas will have that
;; property anyway.

(defthm ptr-not-bound
  (implies (and (not (bound-occurrence x f))
		(not (bound-occurrence x g))
		(or (equal op 'and) (equal op 'or)))
	   (not (bound-occurrence x (pull-top-right op f g)))))

(defthm ptl-not-bound
  (implies (and (not (bound-occurrence x f))
		(not (bound-occurrence x g))
		(or (equal op 'and) (equal op 'or)))
	   (not (bound-occurrence x (pull-top-left op f g)))))

(defthm down-right-not-bound
  (implies (not (bound-occurrence x f))
	   (not (bound-occurrence x (down-right f)))))

(defthm pull-not-bound
  (implies (not (bound-occurrence x f))
	   (not (bound-occurrence x (pull f))))
  :hints (("Goal"
           :in-theory (disable down-right))))

;; The next few thms need (the explosive) not-free-not-change.

(in-theory (enable not-free-not-change))

(defthm subst-ptr-dist-not-bound
  (implies (and (or (equal op 'and) (equal op 'or))
		(not (bound-occurrence x b))
		(domain-term e))
	   (equal (subst-free (pull-top-right op a b) x e)
		  (pull-top-right op (subst-free a x e) (subst-free b x e)))))

(defthm subst-ptl-dist-not-bound
  (implies (and (or (equal op 'and) (equal op 'or))
		(not (bound-occurrence x a))
		(domain-term e))
	   (equal (subst-free (pull-top-left op a b) x e)
		  (pull-top-left op (subst-free a x e) (subst-free b x e)))))

(defthm subst-down-right-commute
  (implies (and (not (bound-occurrence x f))
		(domain-term e))
	   (equal (subst-free (down-right f) x e)
		  (down-right (subst-free f x e)))))

(defthm subst-pull-commute
  (implies (and (not (bound-occurrence x f))
		(domain-term e))
	   (equal (subst-free (pull f) x e)
		  (pull (subst-free f x e))))
  :hints (("Goal"
           :in-theory (disable down-right))))

(in-theory (disable not-free-not-change))  ;; back in its cage

(defthm down-right-fsound-mutual
  (implies (setp (quantified-vars f))
	   (if flg
	       (equal (feval (down-right f) i)
		      (feval f i))
	       (implies (and (domain-term-list (fringe dom))
			     (wfquant f))
			(equal (feval-d (down-right f) dom i)
			       (feval-d f dom i)))))
  :hints (("Goal"
           :induct (feval-i flg f dom i)))
  :rule-classes nil)

(defthm down-right-fsound
  (implies (setp (quantified-vars f))
	   (equal (feval (down-right f) i)
		  (feval f i)))
  :hints (("Goal"
	   :by (:instance down-right-fsound-mutual (flg t)))))

;;=======================
;; The last part is to prove (pull f) fsound.

(defthm setp-append-qvars-pull
  (implies (setp (append (quantified-vars f)
			 (quantified-vars g)))
	   (setp (append (quantified-vars (pull f))
			 (quantified-vars (pull g)))))
  :hints (("Goal"
           :in-theory (disable pull set-equal))))

(defthm pull-fsound-mutual
  (implies (setp (quantified-vars f))
	   (if flg
	       (equal (feval (pull f) i)
		      (feval f i))
	       (implies (and (domain-term-list (fringe dom))
			     (wfquant f))
			(equal (feval-d (pull f) dom i)
			       (feval-d f dom i)))))
  :hints (("Goal"
	   :in-theory (disable down-right)
           :induct (feval-i flg f dom i)))
  :rule-classes nil)

;;---------------

(defthm pull-fsound
  (implies (setp (quantified-vars f))
	   (equal (feval (pull f) i)
		  (feval f i)))
  :hints (("Goal"
	   :by (:instance pull-fsound-mutual (flg t)))))

;;----------------

(defthm pull-quants-fsound
  (equal (feval (pull-quants f) i)
	 (feval f i))
  :hints (("Goal"
	   :in-theory (disable pull))))

