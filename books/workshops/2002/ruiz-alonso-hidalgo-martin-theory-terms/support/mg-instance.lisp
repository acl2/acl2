;;; mg-instance.lisp
;;; Proof of the existence of a least upper bound - lub - (most general
;;; instance - mgi -) of two terms with respect to the subsumption
;;; relation.
;;; Creation: 24-10-99. Last revision: 11-12-2000
;;; =================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "mg-instance")

|#

(in-package "ACL2")
(include-book "renamings")
(include-book "unification")

;;; **********************************
;;; MOST GENERAL INSTANCE OF TWO TERMS
;;; **********************************

;;; We prove here that, given two terms, there exists a most
;;; general instance (if they are unifiable). We will define such most
;;; general instance in the following way:
;;; "Given t1 and t2 we rename their variables in order to get their
;;;  set of variables disjoint. Let t1' and t2' the respective renamed
;;;  versions of t1 and t2. Let sigma = (mgu t1' t2') (if  they are
;;;  unifiable). Then sigma(t1') is a more general instantiation (a
;;;  least upper bound w.r.t. subsumption) of t1 and t2. If t1' and t2'
;;;  are not unifiable, there are no common instance of t1 and t2."

;;; ============================================================================
;;; 1. Most general instance
;;; ============================================================================

;;; Needed for guard verification
(local
 (defthm substitution-p-alistp
   (implies (substitution-p sigma)
	    (alistp sigma))))


;;; ===== MG-INSTANCE-MV

(defun mg-instance-mv (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (let ((rename-t1 (number-rename t1 0 -1))
	(rename-t2 (number-rename t2 1 1)))
    (mv-let (mgu unifiable)
	    (mgu-mv rename-t1 rename-t2)
	    (if unifiable
		(mv (instance rename-t1 mgu) t)
	      (mv nil nil)))))

;;; REMARK: We use multi-values to distinguish the variable term "nil"
;;; from nil. Although our concrete implementation of mgu-mv makes
;;; impossible to return the term "nil" as the first element of the
;;; result returned by mg-instance-mv (since we have numeric variables),
;;;  we use multivalues because we are only using the fundamental
;;; properties given in unification.lisp

;;; Closure property:

(local
 (defthm mg-instance-mv-term-s-p
   (implies (and (term-s-p t1) (term-s-p t2))
	    (term-s-p (first (mg-instance-mv t1 t2))))))

;;; Guard verification:

(local
 (defthm mg-instance-mv-term-p
   (implies (and (term-p t1) (term-p t2))
	    (term-p (first (mg-instance-mv t1 t2))))
   :hints (("Goal" :use (:functional-instance
			 mg-instance-mv-term-s-p
			 (signat (lambda (x n) (eqlablep x)))
			 (term-s-p-aux term-p-aux)
			 (substitution-s-p substitution-p))))))


;;; ============================================================================
;;; 2. Properties of mg-instance-mv for renamings
;;; ============================================================================

;;; GOAL. In this section we want to prove:

;;; * If (second (mg-instance-mv t1 t2)), then:
;;;    (1) and (2): (first (mg-instance-mv t1 t2)) is a common instance of
;;;        (number-rename t1 1 1) and (number-rename t2 0 -1).
;;;    (4): (first (mg-instance-mv t1 t2)) is a most general instance of
;;;         (number-rename t1 1 1) and (number-rename t2 0 -1).

;;; * If (not (second (mg-instance-mv t1 t2))):
;;;    (3): There are no common instance of (number-rename t1 1 1) and
;;;         (number-rename t2 0 -1).


;;; IMPORTANT REMARK: Since we are going to work with renamed terms,
;;; we disable  renamed-implies-iff-subs-1 and renamed-implies-iff-subs-2

(local
 (in-theory (disable renamed-implies-iff-subs-1 renamed-implies-iff-subs-2)))

;;; And also the following rule:
(local (in-theory (disable subsumption-apply-subst)))


;;; ----------------------------------------------------------------------------
;;; 2.1 (number-rename t1 0 -1) subsumes (first (mg-instance-mv t1 t2))
;;; ----------------------------------------------------------------------------

(local
 (defthm mg-instance-mv-subsumes-rename-1
  (implies (second (mg-instance-mv t1 t2))
	   (subs (number-rename t1 0 -1) (first (mg-instance-mv t1 t2))))
  :hints (("Goal"
	   :use (:instance
		  subs-completeness
		  (t1 (number-rename t1 0 -1))
		  (t2 (first (mg-instance-mv t1 t2)))
		  (sigma (mgu (number-rename t1 0 -1)
			      (number-rename t2 1 1))))))))


;;; ----------------------------------------------------------------------------
;;; 2.2 (number-rename t2 1 1) subsumes (first (mg-instance-mv t1 t2))
;;; ----------------------------------------------------------------------------


(local
 (defthm mg-instance-mv-subsumes-rename-2
  (implies (second (mg-instance-mv t1 t2))
	   (subs (number-rename t2 1 1) (first (mg-instance-mv t1 t2))))
  :hints (("Goal" :use
	   ((:instance
	     subs-completeness
	     (t1 (number-rename t2 1 1))
	     (t2 (first (mg-instance-mv t1 t2)))
	     (sigma (mgu (number-rename t1 0 -1)
			 (number-rename t2 1 1)))))))))



;;; ----------------------------------------------------------------------------
;;; 2.3 Disjoint union of two substitution: definition and main property
;;; ----------------------------------------------------------------------------


;;; ====== DISJOINT-UNION-SUBST
;;; Given two terms t1 and t2 and two substitutions sigma1 and sigma2 ,
;;; we append the restriction of sigma1 and sigma2 to the variables of
;;; (number-rename t1 0 -1) and (number-rename t2 1 1)

(local
 (defun disjoint-union-subst (sigma1 sigma2 t1 t2)
   (append (restriction sigma1 (variables t (number-rename t1 0 -1)))
	   (restriction sigma2 (variables t (number-rename t2 1 1))))))


;;;; Main property of (disjoint-union-subst sigma1 sigma2 t1 t2):
;;; (disjoint-union-subst sigma1 sigma2 t1 t2) is an unifier of t1r and t2r.

(local
 (defthm disjoint-union-subst-unifier
  (implies (equal (instance (number-rename t1 0 -1) sigma1)
		  (instance (number-rename t2 1 1) sigma2))
	   (equal (instance (number-rename t2 1 1)
			    (disjoint-union-subst sigma1 sigma2 t1 t2))
		  (instance (number-rename t1 0 -1)
			    (disjoint-union-subst sigma1 sigma2 t1 t2))))))





;;; REMARK: Strategy in the following to prove (3) and (4):

;;; Let t1r = (number-rename t1 0 -1) and t2r = (number-rename t2 1 1):

;;; If term is an upper bound of t1r and t2r, we have to prove that
;;; (first (mg-instance-mv t1 t2)) subsumes term (whenever
;;; (second (mg-instance-mv t1 t2))

;;; We will prove it
;;; - (first (mg-instance-mv t1 t2)) is (instance t1r unifier) and
;;; - term is (instance t1r sigma12 )
;;;   where sigma12 is the disjoint union of the two matching substitution
;;;   for t1r and term and t2r and term, respectively.
;;; - sigma12 is an unifier of t1r and t2r, so unifier subsumes sigma12
;;;   using the lemma subs-sust-main-property (see
;;;   subsumption-subst.lisp)




;;; ----------------------------------------------------------------------------
;;; 2.4 (mg-instance-mv t1 t2) does not fail if there exists a common instance
;;; ----------------------------------------------------------------------------

;;; A lemma before disabling disjoint-union-subst:

(local
 (defthm
   if-there-is-a-common-instance-of-renamings-then-unify
   (implies (equal (instance (number-rename t1 0 -1) sigma1)
		   (instance (number-rename t2 1 1) sigma2))
	    (unifiable (number-rename t1 0 -1) (number-rename t2 1 1)))
   :hints (("Goal" :use
	    (:instance
	      mgu-completeness
	      (sigma (disjoint-union-subst sigma1 sigma2 t1 t2))
	      (t1 (number-rename t1 0 -1))
	      (t2 (number-rename t2 1 1)))))))



;;; Main lemma for (3)
;;; The same as the previous lemma, but using subsumption.

(local
 (defthm
  if-subsume-common-therm-mg-instance-mv
  (implies (and (subs (number-rename t1 0 -1) term)
		(subs (number-rename t2 1 1) term))
	   (second (mg-instance-mv t1 t2)))
  :hints (("Goal" :use
	   (:instance
	    if-there-is-a-common-instance-of-renamings-then-unify
	    (sigma1 (matching (number-rename t1 0 -1) term))
	    (sigma2 (matching (number-rename t2 1 1) term)))))))


;;; We disable disjoint-union-subst
(local (in-theory (disable disjoint-union-subst)))




;;; ----------------------------------------------------------------------------
;;; 2.5 mg-instance-mv is a most general instance of the renamed terms
;;; ----------------------------------------------------------------------------

;;; An important lemma:
;;; mgu of t1r and t2r subsumes disjoint union of matching substitutions

(local
 (defthm subsumption-sust-mgu-disjoint-union
  (implies (equal (instance (number-rename t1 0 -1) sigma1)
		  (instance (number-rename t2 1 1) sigma2))
	   (subs-subst (mgu (number-rename t1 0 -1) (number-rename t2 1 1))
		      (disjoint-union-subst sigma1 sigma2 t1 t2)))))


;;; A bridge lemma:

(local
 (defthm mg-instance-mv-lub-rename-bridge-lemma
  (implies (equal (instance (number-rename t1 0 -1) sigma1)
		  (instance (number-rename t2 1 1) sigma2))
	   (subs (first (mg-instance-mv t1 t2))
		 (instance (number-rename t1 0 -1)
			   (disjoint-union-subst sigma1 sigma2 t1 t2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable mgu-soundness)))))

;;;; We disable mg-instance-mv
(in-theory (disable mg-instance-mv))


;;; (4)
;;; mg-instance-mv is a most general instance of the renamed terms

(local
 (defthm mg-instance-mv-lub-rename
  (implies (and (subs (number-rename t1 0 -1) term)
		(subs (number-rename t2 1 1) term))
	   (subs (first (mg-instance-mv t1 t2)) term))
  :hints (("Goal" :use
	   (:instance mg-instance-mv-lub-rename-bridge-lemma
		      (sigma1 (matching (number-rename t1 0 -1) term))
		      (sigma2 (matching (number-rename t2 1 1) term)))
	   :in-theory (enable disjoint-union-subst)))))


;;; REMARK: The results (1), (2), (3) and (4) are enough to show that
;;; every pair of unifiable terms have a most general instance of their
;;; renamed versions. We can easily translate these properties to the
;;; original terms, using the fact that renamed versions are equivalent
;;; w.r.t. subsumption to the original term. For that purpose we enable
;;; again the congruence rules.

(local
 (in-theory
  (enable renamed-implies-iff-subs-1 renamed-implies-iff-subs-2)))



;;; ============================================================================
;;; 3. mg-instance: definition and non-local properties.
;;; ============================================================================



(defun mg-instance (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (mv-let (mg-instance bool)
	  (mg-instance-mv t1 t2)
    (if bool
	(number-rename mg-instance 1 1)
      nil)))


;;; REMARK: We also rename the result given by mg-instance-mv. This is
;;; for two reassons:
;;; - Pretty printing
;;; - In this way, mg-instance returns nil ONLY WHEN mg-instance-mv
;;;   fails. So we no longer need multivalues.

(defthm mg-instance-subsumes-rename-1
  (implies (mg-instance t1 t2)
	   (subs t1 (mg-instance t1 t2)))

  :hints (("Goal" :use mg-instance-mv-subsumes-rename-1)))


(defthm mg-instance-subsumes-rename-2
  (implies (mg-instance t1 t2)
	   (subs t2 (mg-instance t1 t2)))

  :hints (("Goal" :use mg-instance-mv-subsumes-rename-2)))


(defthm
  if-subsume-common-therm-mg-instance
  (implies (and (subs t1 term)
		(subs t2 term))
	   (mg-instance t1 t2))

  :hints
  (("Goal"
    :use if-subsume-common-therm-mg-instance-mv)))

(defthm mg-instance-lub
  (implies (and (subs t1 term)
		(subs t2 term))
	   (subs (mg-instance t1 t2) term))
  :hints (("Goal" :use (mg-instance-mv-lub-rename
			if-subsume-common-therm-mg-instance-mv))))

;;; Closure property:
(defthm mg-instance-term-s-p
  (implies (and (term-s-p t1) (term-s-p t2))
	   (term-s-p (mg-instance t1 t2))))

;;; Needed for guard verification:
(defthm mg-instance-term-p
  (implies (and (term-p t1) (term-p t2))
	   (term-p (mg-instance t1 t2))))
;;; REMARK: We could have obtained this by functional instantiation of the
;;; previous lemma, but it is also a trivial consequence of
;;; mg-instance-mv-term-p

;;; Now we disable mg-instance.

(in-theory (disable mg-instance (mg-instance)))




