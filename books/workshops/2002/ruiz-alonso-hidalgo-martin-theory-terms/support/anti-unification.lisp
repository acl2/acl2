;;; anti-unification.lisp
;;; Definition and correctness of an anti-unification algorithm
;;; A proof of the existence of a greatest lower bound (glb) of two
;;; terms (w.r.t. subsumption).
;;; Created 22-10-99. Last revision: 15-02-2001
;;; =================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "anti-unification")

|#

(in-package "ACL2")
(include-book "subsumption")

;;; ******************************************************
;;; ANTI-UNIFICATION: DEFINITION AND PROPERTIES.
;;; EXISTENCE OF A GLB OF TWO TERMS W.R.T. SUBSUMPTION.
;;; ******************************************************

;;; In this book:
;;; - Definition of anti-unify, a function implementing an
;;;   anti-unification algorithm.
;;; - Main properties of anti-unify, stablishing that (anti-unify t1 t2)
;;;   is the most particular common generalization of t1 and t2, thus
;;;   showing that the set of first order terms (in a given signature)
;;;   is a lower semi-lattice w.r.t. subsumption.

;;; ============================================================================
;;; 1. Definition of anti-unify-aux
;;; ============================================================================

;;; As usual, we will define anti-unification for terms and for list of
;;; terms. This is done by the function anti-unify-aux. An extra
;;; argument phi is needed to take acount of associations of the form
;;; ((s1 . s2) . x), where s1 and s2 are terms s.t. only variables are a
;;; common generalization of them, and x is a variable. We need to store
;;; this associations, since for the same pair of terms the same
;;; variable has to be assigned during the proccess.



;;; The argument phi can be seen as an "injection" from pair of terms to
;;; variables. This injection is built on demmand. That's the role of
;;; the following function. The function returns a multi-value of three:
;;; see the comments below to understand the role of the three
;;; values. Note also the use of assoc-equal.

(defun anti-unify-injection (p phi)
  (declare (xargs :guard (alistp-acl2-numberp phi)))
  (let ((found (assoc-equal p phi)))
    (if found
	(mv (cdr found) phi t)
      (let ((y (if (endp phi) 1 (+ 1 (cdar phi)))))
	(mv y (cons (cons p y) phi) t)))))

;;; The function anti-unify-aux

(defun anti-unify-aux (flg t1 t2 phi)
  (declare (xargs :guard (and (term-p-aux flg t1)
			      (term-p-aux flg t2)
			      (alistp-acl2-numberp phi))
		  :verify-guards nil))
  (if flg
      (cond ((or (variable-p t1) (variable-p t2))
	     (anti-unify-injection (cons t1 t2) phi))
	    ((eql (car t1) (car t2))
	     (mv-let (anti-unify-args phi1 bool)
		     (anti-unify-aux nil (cdr t1) (cdr t2) phi)
		     (if bool
			 (mv (cons (car t1) anti-unify-args) phi1 t)
		       (anti-unify-injection (cons t1 t2) phi))))
	    (t (anti-unify-injection (cons t1 t2) phi)))
    (cond  ((endp t1) (if (eql t1 t2) (mv t1 phi t) (mv nil nil nil)))
	   ((endp t2) (mv nil nil nil))
	   (t (mv-let (anti-unify-cdr phi1 bool1)
		      (anti-unify-aux nil (cdr t1) (cdr t2) phi)
		      (if bool1
			  (mv-let (anti-unify-car phi2 bool2)
				  (anti-unify-aux t (car t1) (car t2) phi1)
				  (if bool2
				      (mv (cons anti-unify-car anti-unify-cdr)
					  phi2
					  t)
				    (mv nil nil nil)))
			(mv nil nil nil)))))))
;;; REMARKS:
;;; - Note that the function returns a multi-value with three values:
;;; the anti-unification term, the "injection" and a boolean value to
;;; indicate success or fail.
;;; - Although for terms there is always a glb for two terms (a variable
;;; in the "worst" case), the same is not true for lists of terms. Thus,
;;; we have to distinguish nil as fail for nil as a list of
;;; terms. That's the reason for the third value of the returned
;;; muti-value.

;;; Guard verification

(local
 (defthm alistp-acl2-numberp-second-anti-unify-aux
   (implies (alistp-acl2-numberp phi)
	    (alistp-acl2-numberp
	     (second (anti-unify-aux flg t1 t2 phi))))))


(verify-guards anti-unify-aux)


;;; An interesting property: anti-unification always suceeds for
;;; terms. For lists of terms, the sucess or failure is independent from
;;; phi. This rule reduces the complexity of the proofs.

(local
 (defthm anti-unify-aux-bool-pair-args
   (iff (third (anti-unify-aux flg t1 t2 phi))
	(if flg t (second (pair-args t1 t2))))))




;;; OUR GOAL: To prove that the first value of the multi-value returned
;;; by (anti-unify-aux flg t1 t2 phi), when succes, it is a glb of t1 t2
;;; (under some assumptions about phi).




;;; ============================================================================
;;; 2. Definition and properties of pre-anti-unify-aux
;;; ============================================================================

;;; INTERESTING REMARK: In a first attempt, we tried to prove the main
;;; properties of anti-unify-aux reasoning about the function definition
;;; (as usual). But it turned out difficult to manage the "incremental
;;; construction of the injection". In particular, we were not able to
;;; proof that the anti-unification is subsumed by any other common
;;; generalization. Thus, we changed our strategy: we defined
;;; pre-anti-unify-aux. In this function we suppose that the injection
;;; phi is already built. Note that anti-unify-aux returns the same term
;;; as pre-anti-unify-aux, whenever the injection finally constructed by
;;; anti-unify-aux is given to pre-anti-unify-aux initially. In this
;;; way, we have an equivalent definition of anti-unification although
;;; less eficcient, because we would need to traverse the terms twice:
;;; one for computing the injection and one for computing the
;;; anti-unification. In contrast, anti-unify-aux does this computation
;;; at the same time. But the main point here is that pre-anti-unify-aux
;;; is much more suitable for reasoning. We first prove the main
;;; properties of pre-anti-unify-aux, then we prove the relation between
;;; pre-anti-unify-aux and anti-unify-aux, and finally we export the
;;; properties of pre-anti-unify-aux to anti-unify-aux. In few words: a
;;; good example of compositional reasoning.


;;; ----------------------------------------------------------------------------
;;; 2.1 Definition of pre-anti-unify-aux
;;; ----------------------------------------------------------------------------


(local
 (defun pre-anti-unify-aux (flg t1 t2 phi)
   (if flg
       (cond ((or (variable-p t1) (variable-p t2))
	      (mv (cdr (assoc (cons t1 t2) phi)) t))
	     ((eql (car t1) (car t2))
	      (mv-let (anti-unify-args bool)
		      (pre-anti-unify-aux nil (cdr t1) (cdr t2) phi)
		      (if bool
			  (mv (cons (car t1) anti-unify-args) t)
			(mv (cdr (assoc (cons t1 t2) phi)) t))))
	     (t (mv (cdr (assoc (cons t1 t2) phi)) t)))
     (cond  ((endp t1) (if (eql t1 t2) (mv t1 t) (mv nil nil)))
	    ((endp t2) (mv nil nil))
	    (t (mv-let (anti-unify-cdr bool1)
		       (pre-anti-unify-aux nil (cdr t1) (cdr t2) phi)
		       (if bool1
			   (mv-let (anti-unify-car bool2)
				   (pre-anti-unify-aux t (car t1) (car t2) phi)
				   (if bool2
				       (mv (cons anti-unify-car anti-unify-cdr)
					   t)
				     (mv nil nil)))
			 (mv nil nil))))))))

;;; REMARK: Note the difference with anti-unify-aux: we assume the
;;; injection phi as a constant association list.

;;; An analogue property to anti-unify-aux-bool-pair-args:
;;; pre-anti-unification always suceeds for terms. For list of terms,
;;; the sucess or failure is independent from phi. This rule reduces the
;;; complexity of the proofs.

(local
 (defthm pre-anti-unify-aux-bool-pair-args
   (iff (second (pre-anti-unify-aux flg t1 t2 phi))
	(if flg t (second (pair-args t1 t2))))))


;;; ----------------------------------------------------------------------------
;;; 2.2 Main properties of pre-anti-unify-aux
;;; ----------------------------------------------------------------------------

;;; We will prove that under some assumptions on phi,
;;; (pre-anti-unify-aux flg t1 t2 phi) computes a glb of t1 and t2,
;;; whenever it exists.

;;; ············································································
;;; 2.2.1 Assumptions on phi
;;; ············································································

;;; The following function defines the properties we are going to
;;; assume about an injection phi: it has to be an association such that
;;; its co-domain is a list of variables without repetitions and its
;;; domain contains the domain of the association list computed by
;;; anti-unify-aux. We will show that this property is enough to
;;; compute properly the anti-unification of two terms.

(local
 (defun injection-p (phi flg t1 t2)
   (and
    (alistp phi)
    (setp (co-domain phi))
    (list-of-variables-p (co-domain phi))
    (mv-let (term phi1 bool)
	    (anti-unify-aux flg t1 t2 nil)
	    (declare (ignore term bool))
	    (subsetp (domain phi1) (domain phi))))))





;;; ············································································
;;; 2.2.2 pre-anti-unify-aux computes a generalization of t1 and t2
;;; ············································································

;;; We have to prove something like:
;  (let* ((glb (pre-anti-unify-aux flg t1 t2 phi))
;	  (sigma1 (subst-anti-unify-1 phi)))
;    (implies (and (alistp phi) (injection-p phi flg t1 t2) (second glb))
; 	      (equal (apply-subst flg sigma1 (first glb)) t1)))
;;; Using completeness of subsumption, this will suffice to prove that
;;; (first (pre-anti-unify-aux flg t1 t2 phi)) subsumes t1. But
;;; previously, we have to define subst-anti-unify-1, the witness
;;; matching substitution for t1. An analogue result has to be proved for t2,
;;; and also we have to define subst-anti-unify-2, the witness
;;; matching substitution for t2.

(local
 (defun subst-anti-unify-1 (phi)
   (if (endp phi)
       nil
     (cons
      (let* ((p (car phi))
	     (pair-of-terms (car p))
	     (variable (cdr p))
	     (s1 (car pair-of-terms)))
	(cons variable s1))
      (subst-anti-unify-1 (cdr phi))))))

(local
 (defun subst-anti-unify-2 (phi)
   (if (endp phi)
       nil
     (cons
      (let* ((p (car phi))
	     (pair-of-terms (car p))
	     (variable (cdr p))
	     (s2 (cdr pair-of-terms)))
	(cons variable s2))
      (subst-anti-unify-2 (cdr phi))))))



;;; We will show previously that (subst-anti-unify-1 phi) and
;;; (subst-anti-unify-2 phi) are, respectively, the first and second
;;; projections of the inverse of phi. The following encapsulate does
;;; it.


(local
 (encapsulate
  ()

  (defthm list-of-variables-p-co-domain-main-property
    (implies (and
	      (member p (domain phi))
	      (list-of-variables-p (co-domain phi)))
	     (variable-p (cdr (assoc p phi)))))

  (local
   (defthm subst-anti-unify-1-inverse
     (implies (and (setp (co-domain phi))
		   (member x (co-domain phi))
		   (list-of-variables-p (co-domain phi)))
	      (equal (val x (subst-anti-unify-1 phi))
		     (car (val x (inverse phi)))))))


  (local
   (defthm subst-anti-unify-2-inverse
     (implies (and (setp (co-domain phi))
		   (member x (co-domain phi))
		   (list-of-variables-p (co-domain phi)))
	      (equal (val x (subst-anti-unify-2 phi))
		     (cdr (val x (inverse phi)))))))

  (local
   (defthm val-val-inverse-lemma
     (implies (and
	       (member x (domain phi))
	       (equal (val x phi) y))
	      (member y (co-domain phi)))))

  (local
   (defthm val-val-inverse
     (implies (and (setp (co-domain phi))
		   (member x (domain phi)))
	      (equal (val (val x phi) (inverse phi)) x))))


  (local
   (defthm member-domain-co-domain
     (implies (member x (domain phi))
	      (member (val x phi) (co-domain phi)))))

  (defthm inverse-projection-1
    (implies (and (setp (co-domain phi))
		  (alistp phi)
		  (list-of-variables-p (co-domain phi))
		  (member (cons t1 t2) (domain phi)))
	     (equal (val (cdr (assoc (cons t1 t2) phi))
			 (subst-anti-unify-1 phi))
		    t1)))

  (defthm inverse-projection-2
    (implies (and (setp (co-domain phi))
		  (alistp phi)
		  (list-of-variables-p (co-domain phi))
		  (member (cons t1 t2) (domain phi)))
	     (equal (val (cdr (assoc (cons t1 t2) phi))
			 (subst-anti-unify-2 phi))
		    t2)))))


;;; The following encapsulate prove some ugly technical lemmas for
;;; delaing with case *1/8 of the theorems subsumes-anti-unify-aux-1
;;; and subsumes-anti-unify-aux-2. Se puede mejorar.

(local
 (encapsulate
  ()

  (local
   (defthm anti-unify-aux-injection-subsetp-1
     (implies (third (anti-unify-aux flg t1 t2 phi))
	      (subsetp (domain phi)
		       (domain (second (anti-unify-aux flg t1 t2 phi)))))))

  (defthm alistp-anti-unify-aux-injection ;;; This rule will be used later
				          ;;; again
    (implies (alistp phi)
	     (alistp (second (anti-unify-aux flg t1 t2 phi)))))

  (defthm anti-unify-aux-injection-subsetp-2 ;;; This rule will be used later
					     ;;; again
    (implies (and (alistp phi2) (subsetp (domain phi1) (domain phi2)))
	     (subsetp (domain (second (anti-unify-aux flg t1 t2 phi1)))
		      (domain (second (anti-unify-aux flg t1 t2
						      phi2))))))



  (defthm subsumes-anti-unify-aux-lemma-1
    (implies
     (not (subsetp (domain (second (anti-unify-aux flg t3 t4 phi0)))
		   (domain phi)))
     (not (subsetp
	   (domain
	    (second
	     (anti-unify-aux t t1 t2
			     (second (anti-unify-aux
				      flg t3 t4 phi0)))))
	   (domain phi))))
    :hints (("Goal"
	     :use
	     (:instance
	      subsetp-transitive
	      (l (domain (second (anti-unify-aux flg t3 t4 phi0))))
	      (m (domain
		  (second
		   (anti-unify-aux t t1 t2
				   (second (anti-unify-aux
					    flg t3 t4 phi0))))))
	      (n (domain phi))))))



  (defthm subsumes-anti-unify-aux-lemma-2
    (implies
     (and
      (alistp phi0)
      (third (anti-unify-aux flg2 t3 t4 phi0))
      (not (subsetp (domain (second (anti-unify-aux flg1 t1 t2 phi0)))
		    (domain phi))))
     (not
      (subsetp
       (domain
	(second (anti-unify-aux flg1 t1 t2
				(second (anti-unify-aux
					 flg2 t3 t4 phi0)))))
       (domain phi))))
    :hints (("Goal"
	     :in-theory (disable subsetp-transitive)
	     :use
	     (:instance
	      subsetp-transitive
	      (l (domain (second (anti-unify-aux flg1 t1 t2 phi0))))
	      (m (domain
		  (second (anti-unify-aux flg1 t1 t2
					  (second
					   (anti-unify-aux
					    flg2 t3 t4 phi0))))))
	      (n (domain phi))))))))


(local (in-theory (disable assoc-val)))

;;; And the intended theorems:

(local
 (defthm subsumes-anti-unify-aux-1
   (let* ((glb (pre-anti-unify-aux flg t1 t2 phi))
	  (sigma (subst-anti-unify-1 phi)))
     (implies (and
	       (injection-p phi flg t1 t2)
	       (second glb))
	      (equal (apply-subst flg sigma (first glb)) t1)))))

(local
 (defthm subsumes-anti-unify-aux-2
  (let* ((glb (pre-anti-unify-aux flg t1 t2 phi))
	 (sigma (subst-anti-unify-2 phi)))
    (implies (and
	      (injection-p phi flg t1 t2)
	      (second glb))
	     (equal (apply-subst flg sigma (first glb)) t2)))))


;;; ············································································
;;; 2.2.3 pre-anti-unify-aux computes the least common generalization of
;;; t1 and t2
;;; ············································································

;;; This means, using completeness, that we have to construct, given an
;;; lower bound of t1 and t2, term, a matching substitution for term and
;;; (first (anti-unify-aux flg t1 t2 phi)). We are going to construct our
;;; matching substitutions using sigma1 and sigma2 (and phi).

;;; SO our problem  REDUCES to:

;;; - We have two substitutions sigma1 and sigma2, and a term.
;;; - We have to construct a substitution a-u-subst s.t. applied to term
;;;   returns (first (anti-unify-aux flg t1 t2 phi)), where t1 is
;;;   (instance term sigma1) and t2 is (instance term sigma2). The
;;;   function anti-unify-substitutions does the construction.

;;; ======== ANTI-UNIFY-SUBSTITUTIONS


(local
 (defun anti-unify-substitutions (sigma1 sigma2 l phi)
   (if (endp l)
      nil
     (cons
      (cons (car l)
	    (mv-let (anti-unify bool)
		    (pre-anti-unify-aux
		     t (val (car l) sigma1) (val (car l) sigma2) phi)
		    (declare (ignore bool))
		    anti-unify))
      (anti-unify-substitutions sigma1 sigma2 (cdr l) phi)))))

;;; REMARK: We only need to know the value of anti-unify-substitutions
;;; in the variables of term. This is the reason to define it with its
;;; domain depending on a list l.


(local
 (defthm anti-unify-instances-success
  (second (pre-anti-unify-aux flg
			      (apply-subst flg sigma1 term)
			      (apply-subst flg sigma2 term)
			      phi))))


;;; The main theorem of 2.2.3
;;;
;;; REMARK: note the role of the list l in the proof.

(local
 (defthm
   pre-anti-unify-aux-greatest-lower-bound-main-lemma
   (let ((anti-unif-sigma (anti-unify-substitutions sigma1 sigma2 l phi))
	 (anti-unif-term (first (pre-anti-unify-aux
				 flg
				 (apply-subst flg sigma1 term)
				 (apply-subst flg sigma2 term)
				 phi))))
     (implies (subsetp (variables flg term) l)
	      (equal (apply-subst flg anti-unif-sigma term)
		     anti-unif-term)))))



;;; ----------------------------------------------------------------------------
;;; 2.3 Closure property of pre-anti-unify-aux
;;; ----------------------------------------------------------------------------

(local
 (encapsulate
  ()

  (local
   (defthm alistp-acl2-numberp-eqlablep
     (implies (and
	       flg
	       (alistp-acl2-numberp phi)
	       (assoc x phi))
	      (term-s-p-aux flg (cdr (assoc x phi))))))

  (local
   (defthm pre-anti-unify-aux-equal-len
     (implies (second (pre-anti-unify-aux nil l1 l2 phi))
	      (equal (len (first (pre-anti-unify-aux nil l1 l2 phi)))
		     (len l1)))))


  (defthm pre-anti-unify-aux-term-s-p-aux
    (let* ((glb (pre-anti-unify-aux flg t1 t2 phi)))
      (implies (and (injection-p phi flg t1 t2)
		    (alistp-acl2-numberp phi)
		    (second glb)
		    (term-s-p-aux flg t1)
		    (term-s-p-aux flg t2))
	       (term-s-p-aux flg (first glb)))))))


;;; Needed for guard verification

(local
 (defthm pre-anti-unify-aux-term-p-aux
   (let* ((glb (pre-anti-unify-aux flg t1 t2 phi)))
     (implies (and (injection-p phi flg t1 t2)
		   (alistp-acl2-numberp phi)
		   (second glb)
		   (term-p-aux flg t1)
		   (term-p-aux flg t2))
	      (term-p-aux flg (first glb))))
   :hints (("Goal" :use (:functional-instance
			 pre-anti-unify-aux-term-s-p-aux
			 (signat (lambda (x n) (eqlablep x)))
			 (term-s-p-aux term-p-aux))))))



;;; ============================================================================
;;; 3 The bridge between anti-unify-aux and pre-anti-unify-aux
;;; ============================================================================



;;; ----------------------------------------------------------------------------
;;; 3.1 Relation between anti-unify-aux and pre-anti-unify-aux
;;; ----------------------------------------------------------------------------



;;; First, the auxiliary concept of extension-assoc. Intuitively ph1 is
;;; "extension-assoc" of phi if phi1 can be expressed as (append phi2
;;; phi), where the domain of phi2 is disjoint with the domain of ph1.

(local
 (defun extension-assoc (phi1 phi)
   (cond ((equal phi1 phi) t)
	 ((endp phi1) nil)
	 (t (and (not (assoc (caar phi1) phi))
		 (extension-assoc (cdr phi1) phi))))))


(local
 (encapsulate
  ()

;;; Relation between extension-assoc and assoc

  (local
   (defthm extension-assoc-main-property
     (implies (and (extension-assoc phi1 phi) (assoc x phi))
	      (and (assoc x phi1)
		   (equal (cdr (assoc x phi1)) (cdr (assoc x phi)))))))

;;; Transitivity of extension-assoc

  (local
   (defthm extension-assoc-transitive
     (implies (and (extension-assoc phi2 phi1) (extension-assoc phi1 phi))
	      (extension-assoc phi2 phi))))

;;; Note that in every step, anti-unify-aux obtains an injection that
;;; "extends-assoc" the injection given as input.

  (local
   (defthm anti-unify-aux-extension
     (implies (third (anti-unify-aux flg t1 t2 phi))
	      (extension-assoc (second (anti-unify-aux flg t1 t2 phi)) phi))))

;;; The intended relation between pre-anti-unify-aux and anti-unify-aux

  (local
   (defthm anti-unify-aux-pre-anti-unify-aux-main-lemma
     (implies (extension-assoc phi1 (second (anti-unify-aux flg t1 t2 phi)))
	      (equal (first (anti-unify-aux flg t1 t2 phi))
		     (first (pre-anti-unify-aux flg t1 t2 phi1))))
     :rule-classes nil))

;;; A rewrite rule

  (defthm anti-unify-aux-pre-anti-unify-aux
    (equal (first (anti-unify-aux flg t1 t2 phi))
	   (first (pre-anti-unify-aux
		   flg t1 t2 (second (anti-unify-aux flg t1 t2
						     phi)))))
    :hints (("Goal" :use
	     (:instance anti-unify-aux-pre-anti-unify-aux-main-lemma
			(phi1 (second (anti-unify-aux flg t1 t2 phi)))))))))


;;; ----------------------------------------------------------------------------
;;; 3.2 anti-unify-aux returns a suitable injection for pre-anti-unify-aux
;;; ----------------------------------------------------------------------------

;;; The theorem anti-unify-aux-pre-anti-unify-aux shows the relation
;;; between anti-unify-aux and pre-anti-unify-aux, giving an alternative
;;; definition of anti-unify-aux, in terms of pre-anti-unify-aux.  We
;;; will be able to export the properties of pre-anti-unify-aux if we
;;; prove that (second (anti-unify-aux flg t1 t2 phi)) meets the
;;; property injection-p.


(local
 (defun acl2-numberp-increasing-list (l)
   (cond ((endp l) t)
	 ((endp (cdr l)) (acl2-numberp (first l)))
	 (t
	  (and
	   (acl2-numberp (first l))
	   (> (first l) (second l))
	   (acl2-numberp-increasing-list (cdr l)))))))

(local
 (encapsulate
  ()
  (local
   (defthm acl2-numberp-increasing-list-set-of-variables-co-domain
     (implies (acl2-numberp-increasing-list L)
	      (and (setp l) (list-of-variables-p l)))))

  (local
   (defthm anti-unify-aux-injection-setp-co-domain
     (implies (acl2-numberp-increasing-list (co-domain phi0))
	      (acl2-numberp-increasing-list
	       (co-domain
		(second (anti-unify-aux flg t1 t2 phi0)))))))

  (defthm anti-unify-aux-injection-injection-p
    (implies
     (and (acl2-numberp-increasing-list (co-domain phi0))
	  (alistp phi0))
     (injection-p
      (second
       (anti-unify-aux flg t1 t2 phi0)) flg t1 t2)))))

;;; To apply the closure property we also need to prove that the second
;;; value of anti-unify-aux is a alistp-acl2-numberp

(local
 (defthm anti-unify-aux-injection-alistp-acl2-numberp
   (implies (alistp-acl2-numberp phi0)
	    (alistp-acl2-numberp
	     (second
	      (anti-unify-aux flg t1 t2 phi0))))))

;;; The above properties are enough to prove the main theorems below. So
;;; we disable:
(local
 (in-theory (disable anti-unify-aux
		     pre-anti-unify-aux
		     injection-p)))



;;; ============================================================================
;;; 4 anti-unify: definition and (non-local) main properties
;;; ============================================================================

;;; ========= ANTI-UNIFY

(defun anti-unify (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (mv-let (anti-unify phi bool)
	  (anti-unify-aux t t1 t2 nil)
	  (declare (ignore phi bool))
	  anti-unify))

;;; REMARK: Note how the following properties are proved, in general:
;;; - (first of) anti-unify-aux is rewritten to (first of)
;;; pre-anti-unify-aux using the rule anti-unify-aux-pre-anti-unify-aux
;;; - The corresponding property of pre-anti-unify-aux is used, since
;;;   (second (anti-unify-aux t t1 t2 nil)) has the property injection-p



(defthm anti-unify-lower-bound

  (and (subs (anti-unify t1 t2) t1)
       (subs (anti-unify t1 t2) t2))


  :hints (("Goal" :use
	   ((:instance
	     subs-completeness
	     (sigma (subst-anti-unify-1
		     (second
		      (anti-unify-aux t t1 t2 nil))))
	     (t1 (first (anti-unify-aux t t1 t2 nil)))
	     (t2 t1))
	    (:instance
	     subs-completeness
	     (sigma (subst-anti-unify-2
		     (second
		      (anti-unify-aux t t1 t2 nil))))
	     (t1 (first (anti-unify-aux t t1 t2 nil))))))))




(defthm anti-unify-greatest-lower-bound

   (implies (and (subs term t1)
		 (subs term t2))
	    (subs term (anti-unify t1 t2)))

   :hints (("Goal"
	    :use
	    ((:instance
	      subs-completeness
	      (sigma (anti-unify-substitutions
		      (matching term t1)
		      (matching term t2)
		      (variables t term)
		      (second
		       (anti-unify-aux t t1 t2 nil))))
	      (t1 term)
	      (t2 (anti-unify t1 t2)))))))


;;; Closure property:

(defthm anti-unify-term-s-p
  (implies (and (term-s-p t1) (term-s-p t2))
	   (term-s-p (anti-unify t1 t2))))


;;; Needed for guard verification:

(defthm anti-unify-term-p
  (implies (and (term-p t1) (term-p t2))
	   (term-p (anti-unify t1 t2))))

;;; REMARK: We could have obtained this last theorem by functional
;;; instantiation of the
;;; previous theorem, but it is also a trivial consequence of
;;; pre-anti-unify-aux-term-p-aux


(in-theory (disable anti-unify (anti-unify)))












