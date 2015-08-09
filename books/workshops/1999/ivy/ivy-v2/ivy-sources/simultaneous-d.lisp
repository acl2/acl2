(in-package "ACL2")

;; Simultaneous substitution and seqify soundness.
;;
;; Author: Olga Shumsky (shumsky@mcs.anl.gov)
;;
;; As Bill suggested in substitution, I will attempt to write a
;; simultaneous-apply and prove soundness of seqify by proving that
;;
;;     (simultaneous-apply s f) = (sequential-apply (seqify s) f)

(include-book "substitution")

(defun simapply-term-list (s l)
  (declare (xargs :guard (and (wft-list l) (wfsubst s))))
  (if (atom l)
      l
      (cons (cond ((variable-term (car l))
		   (if (fassoc (car l) s)
		       (cdr (fassoc (car l) s))
		       (car l)))
		  ((domain-term (car l)) (car l))
		  ((wf-ap-term-top (car l))
		   (cons (caar l) (simapply-term-list s (cdar l))))
		  (t (car l))) ;; leave non-term unchanged
	    (simapply-term-list s (cdr l)))))

(defun sim-apply (s f)
  (declare (xargs :guard (and (wff f) (quantifier-free f) (wfsubst s))))
  (cond ((wfnot f) (list 'not (sim-apply s (a1 f))))
	((wfbinary f) (list (car f)
			    (sim-apply s (a1 f))
			    (sim-apply s (a2 f))))
	((wfatomtop f) (cons (car f) (simapply-term-list s (cdr f))))
	(t f)))

;; let's try a different sequential-apply.  The idea is to match the
;; structure of sequential apply to that of simultaneous apply.
(defun seq-term-list (s l)
  (declare (xargs :guard (and (wfsubst s) (wft-list l))))
  (if (atom s)
      l
      (seq-term-list (cdr s) (subst-term-list l (caar s) (cdar s)))))

(defun seq-apply (s f)
  (declare (xargs :guard (and (wfsubst s) (wff f))))
  (cond ((wfnot f) (list 'not (seq-apply s (a1 f))))
	((wfbinary f) (list (car f)
			    (seq-apply s (a1 f))
			    (seq-apply s (a2 f))))
	((wfatomtop f) (cons (car f) (seq-term-list s (cdr f))))
	(t f)))

;;------------------ Section 1 -----------------------------------
;; If variables in cars and cdrs of the substitution are disjoint
;; seq-apply-term-list and simapply-term-list give the same result

(defthm intersect-with-cons-1
  (implies (intersect-equal x y)
	   (intersect-equal x (cons a y))))

(defthm intersect-with-cons-2
  (implies (not (intersect-equal x (cons y a)))
	   (not (intersect-equal x (list y)))))

(defthm intersect-with-union-1
  (implies (intersect-equal x y)
	   (intersect-equal x (union-equal a y))))

(defthm intersect-with-union-2
  (implies (not (intersect-equal x (union-equal y a)))
	   (not (intersect-equal x y))))

(defthm intersect-nil
  (not (intersect-equal x nil)))

(defthm x-member-listx-intersect
  (implies (and (intersect-equal x (list a))
		(member-equal a y))
	   (intersect-equal x y))
  :rule-classes nil)

;; The lemma subst-term-list-no-change is needed for the
;; proof of lemma seq-term-list-no-change.  It is not needed
;; anywhere else, but if left enable slows things down considerably
(defthm subst-term-list-no-change
  (implies (not (member-equal x (vars-in-term-list l)))
	   (equal (subst-term-list l x tm) l)))

;; The lemma seq-term-list-no-change is used in proofs of
;; lemmas seq-term-listvar-list-fassoc and
;; sim-seq-variable-disjoint-subst-cars-cdrs. It is not needed
;; anywhere else, but if left enable slows things down considerably.
;; The lemmas is disabled after it is proved and explicitly enabled
;; for the proofs of the two lemmas.
(defthm seq-term-list-no-change
  (implies (and (wft-list l)
		(wfsubst s)
		(not (intersect-equal (cars s) (vars-in-term-list l))))
	   (equal (seq-term-list s l) l)))

(in-theory (disable subst-term-list-no-change seq-term-list-no-change))

;; check where used
(defthm wft-list-true-list
  (implies (wft-list l)
	   (true-listp l)))
(in-theory (disable wft-list-true-list))

(defthm seq-term-list-var-list-fassoc
  (implies (and (variable-term x)
		(wfsubst s)
		(not (intersect-equal (cars s) (vars-in-term-list (cdrs s))))
		(fassoc x s))
	   (equal (seq-term-list s (list x))
		  (list (cdr (fassoc x s)))))
  :hints (("Goal"
	   :in-theory (enable wft-list-true-list))
	  ("Subgoal *1/2"
	   :in-theory (enable seq-term-list-no-change
			      wft-list-true-list))
	  ("Subgoal *1/2.2"
	   :use ((:instance x-member-listx-intersect
			    (x (cars (cdr s)))
			    (y (vars-in-term-list (cdrs (cdr s))))
			    (a (cdar s)))))))

(defthm subst-term-list-append-commute
  (implies (and (wft-list l1)
		(wft-list l2))
	   (equal (subst-term-list (append l1 l2) x tm)
		  (append (subst-term-list l1 x tm)
			  (subst-term-list l2 x tm)))))

(defthm seq-term-list-append-commute
  (implies (and (wft-list l1)
		(wft-list l2)
		(wfsubst s))
	   (equal (seq-term-list s (append l1 l2))
		  (append (seq-term-list s l1)
			  (seq-term-list s l2))))
  :rule-classes nil)

;; (in-theory (disable subst-term-list-append-commute ))

(defthm seq-term-list-cons-var-wftlist
  (implies (and (variable-term x)
		(wft-list l)
		(wfsubst s)
		(not (intersect-equal (cars s) (vars-in-term-list (cdrs s))))
		(fassoc x s))
	   (equal (seq-term-list s (cons x l))
		  (append (list (cdr (fassoc x s)))
			  (seq-term-list s l))))
  :hints (("Goal" :use ((:instance seq-term-list-append-commute
				   (l1 (list x)) (l2 l))))))

(defthm variable-not-in-seq-subst
  (implies (and (wft-list l)
		(variable-term x)
		(wfsubst s)
		(not (fassoc x s)))
	   (equal (seq-term-list s (cons x l))
		  (cons x (seq-term-list s l)))))

(defthm domain-term-seq-subst
  (implies (and (wft-list l)
		(domain-term x)
		(wfsubst s))
	   (equal (seq-term-list s (cons x l))
		  (cons x (seq-term-list s l)))))

(defthm term-seq-subst
  (implies (and (wft-list l1)
		(wft-list l2)
		(symbolp p)
		(wfsubst s))
	   (equal (seq-term-list s (cons (cons p l1) l2))
		  (cons (cons p (seq-term-list s l1))
			(seq-term-list s l2))))
  :hints (("Goal" :in-theory (enable wft-list-true-list))))

;; This theorem is the goal of section 1.
(defthm sim-seq-variable-disjoint-subst-cars-cdrs
  (implies (and (wft-list a)
		(wfsubst s)
		(not (intersect-equal (cars s)
				      (vars-in-term-list (cdrs s)))))
	   (equal (seq-term-list s a)
		  (simapply-term-list s a)))
  :hints (("Goal" :in-theory (enable wft-list-true-list))
	  ("Subgoal *1/1" :in-theory (enable seq-term-list-no-change))))

;;(in-theory (disable variable-not-in-seq-subst domain-term-seq-subst
;;		   term-seq-subst))

;;------------------ Section 2 -----------------------------------
;; The goal of this section is to prove that subst-term-list and
;; subst-cdrs cancel each other.  In particular, we need to prove
;; that under certain conditions
;;         (equal (subst-term-list
;;                  (simapply-term-list (subst-cdrs s v1 v2) a) v2 v1)
;;                (simapply-term-list s a))))
;;
;; This is accomplished in two steps.  First, we prove that
;;  (equal (simapply-term-list (subst-cdrs s v1 v2) a)
;;         (subst-term-list (simapply-term-list s a) v1 v2))
;; provided v2 is a new variable.  This is done in lemma
;; subst-term-list-simapply-term-list-distribute.
;;
;; The second step is to prove that (simapply-term-list s l)
;; does not introduce new variables wrt (cdrs s) and l.  This is
;; done in lemma simapply-term-list-introduces-no-new-vars.
;;
;; I use an series of encapsulates so that the auxiliary lemmas
;; do not get in the way later.

;; Step 1:
;; note that the exported theorem of this statement breaks up into
;; too many cases.  maybe it can be fixed and go faster?
(encapsulate
 ()
 (local (defthm fassoc-subst-cdrs
	  (implies (fassoc x y)
		   (fassoc x (subst-cdrs y v tm)))))

 (local (defthm fassoc-subst-cdrs-not
	  (implies (and (symbolp x)
			(wfsubst y)
			(not (fassoc x y)))
		   (not (fassoc x (subst-cdrs y v tm))))))

 (local (defthm member-subst-fassoc
	  (implies (and (wfsubst s)
		(member-equal x (cars s)))
		   (fassoc x s))))

 (local (defthm fassoc-domain-subst-cdrs
	  (implies (and (wfsubst s)
			(domain-term (cdr (fassoc x s))))
		   (equal (fassoc x (subst-cdrs s v1 v2))
			  (fassoc x s)))))

 (local (defthm fassoc-subst-cdr-equal-cdr
	  (implies (and (wfsubst s)
			(fassoc x s)
			(variable-term (cdr (fassoc x s))))
		   (equal (fassoc x (subst-cdrs s (cdr (fassoc x s)) v))
			  (cons x v)))))

 (local (defthm fassoc-subst-cdr-same
	  (implies (and (wfsubst s)
			(fassoc x s)
			(variable-term (cdr (fassoc x s)))
			(not (equal (cdr (fassoc x s)) v1)))
		   (equal (fassoc x (subst-cdrs s v1 v2))
			  (fassoc x s)))))

 (local (defthm fassoc-wft
	  (implies
	   (and (wfsubst s)
		(fassoc x s)
		(consp (cdr (fassoc x s)))
		(not (member-equal v2 (vars-in-term-list (cdrs s)))))
	   (equal (fassoc x (subst-cdrs s v1 v2))
		  (cons x
			(cons (cadr (fassoc x s))
			      (subst-term-list (cddr (fassoc x s)) v1 v2)))))
  :hints (("Goal" :in-theory (enable wft-list-true-list)))))

 (local (defthm simapply-term-list-true-list
	  (implies (true-listp l)
		   (true-listp (simapply-term-list s l)))))

 (local (defthm fassoc-domain-term
	  (implies (and (wfsubst s)
			(fassoc x s)
			(not (symbolp (cdr (fassoc x s))))
			(not (and (consp (cdr (fassoc x s)))
				  (symbolp (cadr (fassoc x s)))
				  (true-listp (cddr (fassoc x s))))))
		   (domain-term (cdr (fassoc x s))))))

 ;; exported theorem of this encapsulate
 (defthm subst-term-list-simapply-term-list-distribute ;; ~20 secs
  (implies (and (wft-list a)
		(wfsubst s)
		(variable-term v1)
		(variable-term v2)
		(member-equal v1 (cars s))
		(not (member-equal v2 (vars-in-term-list a)))
		(not (member-equal v2 (vars-in-term-list (cdrs s)))))
	   (equal (simapply-term-list (subst-cdrs s v1 v2) a)
		  (subst-term-list (simapply-term-list s a) v1 v2))))

 ) ;; end of encapsulate

;; Step 2:
;; Prove that simapply-term-list introduces not new variable occurrences

(encapsulate
 ()
 (local (defthm var-occurrence-tl-fassoc
	  (implies (and (wfsubst s)
			(fassoc a s)
			(not (var-occurrence-term-list x (cdrs s))))
		   (not (var-occurrence-term-list
			 x (list (cdr (fassoc a s))))))))

 (local (defthm var-occurrence-tl-cons
	  (implies (and (true-listp z)
			(not (var-occurrence-term-list x (list y)))
			(not (var-occurrence-term-list x z)))
		   (not (var-occurrence-term-list x (cons y z))))))

 (local (defthm simapply-term-list-wftlist-truelist
	  (implies (and (wfsubst s)
			(wft-list l))
		   (true-listp (simapply-term-list s l)))))

 ;; exported lemma of this encapsulate
 (defthm var-occurrence-simapply-term-list
  (implies (and (wft-list l)
		(variable-term x)
		(wfsubst s)
		(not (var-occurrence-term-list x l))
		(not (var-occurrence-term-list x (cdrs s))))
	   (not (var-occurrence-term-list x (simapply-term-list s l))))
  :rule-classes nil)

 ) ;; end of encapsulate


(local (defthm wfsubst-cdrs-wftlist
	 (implies (wfsubst s)
		  (wft-list (cdrs s)))))

(encapsulate
 ()
 ;; relationship between var-occurrence and vars-in-term-list
 (local (defthm var-occurrence-member-vars-term-list-1
	  (implies (and (wft-list l)
			(not (var-occurrence-term-list x l)))
		   (not (member-equal x (vars-in-term-list l))))))

 (local (defthm var-occurrence-member-vars-term-list-2
	  (implies (and (wft-list l)
			(var-occurrence-term-list x l))
		   (member-equal x (vars-in-term-list l)))))

 ;; lemmas to prove that simapply-term-list is a wft-list
 (local (defthm cdr-fassoc-wftlist
	  (implies (and (wfsubst s)
			(fassoc x s))
		   (wft-list (list (cdr (fassoc x s)))))))

 (local (defthm wftlist-cons
	  (implies (and (wft-list (list x))
			(wft-list y))
		   (wft-list (cons x y)))))

 (local (defthm simapply-term-list-wftlist
	  (implies (and (wft-list l)
			(wfsubst s))
		   (wft-list (simapply-term-list s l)))))

 ;; exported theorem of this section
 (defthm simapply-term-list-introduces-no-new-vars
   (implies (and (wft-list l)
		 (variable-term x)
		 (wfsubst s)
		 (not (member-equal x (vars-in-term-list l)))
		 (not (member-equal x (vars-in-term-list (cdrs s)))))
	    (not (member-equal
		  x (vars-in-term-list (simapply-term-list s l)))))
   :hints (("Goal" :do-not-induct t
	    :use var-occurrence-simapply-term-list)))

 ) ;; end of encapsulate

(defthm subst-term-list-inverse
  (implies (and (variable-term v1)
		(variable-term v2)
		(not (member-equal v2 (vars-in-term-list l))))
	   (equal (subst-term-list (subst-term-list l v1 v2) v2 v1) l)))

;; Putting is all together:  Main lemma of section 2
(defthm subst-term-subst-cdrs-cancel
  (implies (and (wft-list a)
		(wfsubst s)
		(variable-term v1)
		(variable-term v2)
		(member-equal v1 (cars s))
		(not (member-equal v2 (vars-in-term-list a)))
		(not (member-equal v2 (vars-in-term-list (cdrs s)))))
	   (equal (subst-term-list
		   (simapply-term-list (subst-cdrs s v1 v2) a)
		   v2
		   v1)
		  (simapply-term-list s a))))

;;------------------ Section 3 -----------------------------------
;; Here we prove a supporting lemma about sets.

(defthm vars-subst-subset-subset
  (implies (and (variable-term v)
		(subsetp-equal (vars-in-term-list l) vars))
	   (subsetp-equal (vars-in-term-list (subst-term-list l x v))
			  (cons v vars))))

(encapsulate
 ()
 (local (defthm member-intersect-subset-1
	  (implies (and (not (member-equal a x))
			(subsetp-equal (intersect-equal x y) z))
		   (subsetp-equal (intersect-equal x (cons a y)) z))))

 (local (defthm intersect-union-subset-1
	  (implies (and (subsetp-equal (intersect-equal x y1) z)
			(subsetp-equal (intersect-equal x y2) z))
		   (subsetp-equal (intersect-equal
				   x (union-equal y1 y2)) z))))

 (local (defthm intersect-union-subset-2
	  (implies (not (subsetp-equal (intersect-equal x y) z))
		   (not (subsetp-equal (intersect-equal
					x (union-equal y a)) z)))))

 (local (defthm intersect-union-subset-3
	  (implies (not (subsetp-equal (intersect-equal x y) z))
		   (not (subsetp-equal (intersect-equal
					x (union-equal a y)) z)))))

 (local (defthm intersect-cons-subset-1
	  (implies (not (subsetp-equal (intersect-equal x y) z))
		   (not (subsetp-equal (intersect-equal x (cons a y)) z)))))

 (local (defthm subst-vars-subset
	  (implies (and (wft-list l)
			(variable-term v)
			(variable-term y))
		   (subsetp-equal (vars-in-term-list (subst-term-list l v y))
				  (cons y (vars-in-term-list l))))))

 (local (defthm member-subst
	  (implies (and (wft-list l)
			(variable-term v)
			(variable-term y)
			(not (equal v y)))
		   (not (member-equal
			 v (vars-in-term-list (subst-term-list l v y)))))))

 (local
  (defthm subset-intersect-helper-subcase
    (implies (and (subsetp-equal (intersect-equal cs y1) v2)
		  (subsetp-equal (intersect-equal cs (cons a y2))
				 (cons v1 v2))
		  (not (member-equal z cs))
		  (not (equal v1 z))
		  (not (equal v1 a))
		  (not (member-equal v1 y1))
		  (subsetp-equal y1 (cons z y2)))
	     (subsetp-equal (intersect-equal cs (cons a y1)) v2))
    :hints (("Goal" :do-not generalize))))

 (defthm subset-intersect-helper
   (implies
    (and (variable-term y)
	 (variable-term v1)
	 (not (equal y v1))
	 (var-list cs)
	 (wft-list cd)
	 (var-list v2)
	 (subsetp-equal (intersect-equal cs (vars-in-term-list cd))
			(cons v1 v2))
	 (not (member-equal y cs)))
    (subsetp-equal (intersect-equal cs (vars-in-term-list
					(subst-term-list cd v1 y)))
		   v2)))

 ) ;; end of encapsulate
;; end of section 3

;; ------------------ Putting it all together ----------------------
(defthm gensymbol-subset-member
  (implies (subsetp-equal l1 l2)
	   (not (member-equal (gen-symbol 'y l2) l1))))

(defthm gensymbol-subset-not-equal
  (implies (and (subsetp-equal l1 l2)
		(member-equal a l1))
	   (not (equal a (gen-symbol 'y l2)))))

(defthm cars-subst-cdrs
  (implies (wfsubst s)
	   (equal (cars (subst-cdrs s x tm))
		  (cars s))))

(defthm cdrs-subst-cdr
  (implies (wfsubst s)
	   (equal (cdrs (subst-cdrs s v e))
		  (subst-term-list (cdrs s) v e))))

(defthm seq-last-subst-unroll
  (implies (and (wft-list a)
		(wfsubst s)
		(variable-term v1)
		(variable-term v2))
	   (equal (seq-term-list (append s (list (cons v1 v2))) a)
		  (subst-term-list (seq-term-list s a) v1 v2)))
  :hints (("Goal"
	   :in-theory (disable sim-seq-variable-disjoint-subst-cars-cdrs))))

; this lemma is the essence of the proof
(defthm seq-apply-seq-helper-simapply-same
  (implies
   (and (wft-list a)
        (wfsubst s)
        (var-list vars)
        (var-list vars-to-fix)
        (subsetp-equal vars-to-fix vars)
        (subsetp-equal vars-to-fix (cars s))
        (subsetp-equal (vars-in-term-list a) vars)
	(subsetp-equal (vars-in-term-list (cdrs s)) vars)
        (subsetp-equal (cars s) vars)
	(subsetp-equal (intersect-equal (cars s)
					(vars-in-term-list (cdrs s)))
		       vars-to-fix)
	)
   (equal (seq-term-list (seqify-helper s vars-to-fix vars) a)
          (simapply-term-list s a)))
  :hints (("goal"
	   :in-theory (enable wft-list-true-list
			      sim-seq-variable-disjoint-subst-cars-cdrs)
           :induct (seqify-helper s vars-to-fix vars))))

(defthm intersect-subset-of-first
  (subsetp-equal (intersect-equal x y) x))

(defthm intersect-subset-of-union
  (subsetp-equal (intersect-equal x y)
		 (union-equal x (union-equal y z))))

;; Main theorem:
;; Prove that sim-apply and seq-apply/seqify give the same result
;; note: case 2 takes a long time.  Can anything be done?

(defthm simaltaneous-sequential-subst
  (implies (and (wff f)
		(quantifier-free f)
		(var-list vars)
		(subsetp-equal (free-vars f) vars)
		(wfsubst s))
	   (equal (seq-apply (seqify s vars) f)
		  (sim-apply s f)))
  :hints (("Goal" :induct (sim-apply s f))))

;;-----------------------------------------------------------------
;; Now, state the equivalence of simultaneous and sequential
;; substitutions in terms of official sequential-apply

(defthm wfsubst-seqify
  (implies (and (wfsubst s)
		(var-list vars))
           (wfsubst (seqify s vars))))

;; Prove that two sequential apply functions give the same result
;;
;; does several inductions, but it is faster and cleaner to do that
;; then to prove the subgoals separately

(defthm two-seq-versions-same
  (implies (and (wff f)
		(quantifier-free f)
		(wfsubst s))
	   (equal (sequential-apply s f)
		  (seq-apply s f))))

(defthm simaltaneous-sequential-subst-2
  (implies (and (wff f)
		(quantifier-free f)
		(var-list vars)
		(subsetp-equal (free-vars f) vars)
		(wfsubst s))
	   (equal (sequential-apply (seqify s vars) f)
		  (sim-apply s f)))
  :hints (("Goal" :in-theory (disable seqify))))
