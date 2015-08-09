;;; subsumption-subst.lisp
;;; The subsumption relation between substitutions
;;; Created 13-10-99. Last revision: 09-01-2001
;;; =================================================================


#| To certify this book:

(in-package "ACL2")

(certify-book "subsumption-subst")

|#

(in-package "ACL2")
(include-book "subsumption")




;;; *******************************************************************
;;; THE SUBSUMPTION RELATION BETWEEN SUBSTITUTIONS.
;;; DEFINITION AND PROPERTIES.
;;; *******************************************************************

;;; Our goal is to define the subsumption relation between
;;; substitutions. In the literature, this relation is defined in this
;;; way:
;;;     sigma <= delta iff (exists gamma) gamma·sigma = delta
;;; where "·" stands for composition.

;;; Note that equality between substitutions is functional equality (we cannot
;;; use equal), so we reformulate this property as:

;;; (*) sigma <= delta iff (exists gamma)
;;;                        s.t. for all term
;;;                        gamma·sigma(term) = delta(term)


;;; Our goal in this book is to define the subsumption relation between
;;; substitutions as a function, subs-subst. We will define that
;;; function paying attention only to a restricted list of
;;; variables. Then will prove (*) in the ACL2 logic. As subsumption
;;; between terms (due to existential quantification) we have to give
;;; the substitution gamma in a constructive way, so our definition of
;;; the subsumption relation will be based on a algorithm that finds
;;; such substitution gamma, whenever it exists.


;;; That is to say, we are going to:

;;; 1) Define the subsumption relation, (subs-subst sigma delta) as a
;;;    function and the witness matching substitution, called
;;;    (matching-subst-r sigma delta). Both functions will be based on a
;;;    matching algorithm called subs-subst-mv.

;;; 2) Prove that if (subs-subst sigma delta), then
;;;    (matching-subst-r sigma delta) applied to sigma(term) is equal to
;;;    delta(term), with the same matching substitution, for all
;;;    term. The reverse implication is trivial.


;;; ============================================================================
;;; 1. Definition of subs-subst
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 1.1. Some previous definitions and lemmas
;;; ----------------------------------------------------------------------------

;;; ===== TRUE-LIST-OF-VARIABLES
(local
 (defun true-list-of-variables (l)
   (if (atom l)
       (equal l nil)
     (and (variable-p (car l))
	  (true-list-of-variables (cdr l))))))

(local
 (defthm true-list-of-variables-append
   (implies (and (true-list-of-variables l)
		 (true-list-of-variables m))
	    (true-list-of-variables (append l m)))))

(local
 (defthm true-list-of-variables-variables
   (true-list-of-variables (variables flg term))))


;;; ===== TRUE-LIST-OF-EQLABLEP (needed for guard verification)
(local
 (defun true-list-of-eqlablep (l)
   (if (atom l)
       (equal l nil)
     (and (eqlablep (car l))
	  (true-list-of-eqlablep (cdr l))))))

(local
 (defthm true-list-of-eqlablep-append
   (implies (and (true-list-of-eqlablep l)
		 (true-list-of-eqlablep m))
	    (true-list-of-eqlablep (append l m)))))

(local
 (defthm true-list-of-eqlablep-variables
   (implies (term-s-p-aux flg term)
	    (true-list-of-eqlablep (variables flg term)))))



;;; ===== DOMAIN-VAR
;;; The variables of the domain (to remove anomalies).

(defun domain-var (sigma)
  (if (endp sigma)
      nil
    (if (variable-p (caar sigma))
	(cons (caar sigma) (domain-var (cdr sigma)))
      (domain-var (cdr sigma)))))



;;; Its main properties

(local
 (defthm domain-var-main-property
   (iff (member x (domain-var sigma))
	(and (member x (domain sigma))
	     (variable-p x)))))

;;; Needed for guard verification
(local
 (defthm true-list-of-variables-domain-var
   (true-list-of-variables (domain-var sigma))))

(local
 (defthm true-list-of-eqlablep-domain-var
   (implies (substitution-s-p sigma)
	    (true-list-of-eqlablep (domain-var sigma)))))


(local (in-theory (disable domain-var)))




;;; ====== CO-DOMAIN-VAR
;;; The "values" of the variables in domain-var


(defun co-domain-var (sigma)
  (if (endp sigma)
      nil
    (if (variable-p (caar sigma))
	(cons (cdar sigma) (co-domain-var (cdr sigma)))
      (co-domain-var (cdr sigma)))))

;;; Needed for guard verification
(local
 (defthm term-s-p-aux-co-domain-var
   (implies (substitution-s-p sigma)
	    (term-s-p-aux nil (co-domain-var sigma)))))



;;; ====== IMPORTANT-VARIABLES
;;; For subsumption of substitutions, we only pay atention to these
;;; variables

(defun important-variables (sigma delta)
  (append (domain-var sigma)
	  (append (domain-var delta)
		  (variables nil (co-domain-var sigma)))))



;;; ===== SYSTEM-SUBS-SUBST.
;;; A technical macro definition
;;; We will prove below that two substitutions are related by
;;; subsumption iff the following system of equations is matchable.

(local
 (defmacro system-subs-subst (sigma delta)
   `(first
     (pair-args
      (apply-subst nil ,sigma (important-variables ,sigma ,delta))
      (apply-subst nil ,delta (important-variables ,sigma ,delta))))))


;;; ----------------------------------------------------------------------------
;;; 1.2. Definition of subs-subst
;;; ----------------------------------------------------------------------------


;;;; NOTATION:
;;;; ^^^^^^^^^
;;;; In the followin comments, V will be
;;;; (important-variables sigma delta))

;;; ===== SUBS-SUBST-MV
;;; Subsumption between substitutions.
;;; To decide wether sigma subsumes delta, then we take the list of
;;; variables of the domain of sigma, the domain of delta and the
;;; variables of the terms in the co-domain of sigma (i.e, the list V), and
;;; test if the list of terms sigma(V) subsumes the list of terms
;;; delta(V).

(defun subs-subst-mv (sigma delta)
  (let ((V (important-variables sigma delta)))
    (mv-let (system bool)
	    (pair-args (apply-subst nil sigma V)
		       (apply-subst nil delta V))
	    (declare (ignore bool))
	    (match-mv system))))

;;; ====== SUBS-SUBST
;;; The subsumption relation between substitutions:


(defun subs-subst (sigma delta)
  (mv-let (match bool)
	  (subs-subst-mv sigma delta)
	  (declare (ignore match))
	  bool))


;;; ===== MATCHING-SUBST
;;; An important auxiliary definition: when
;;; (subs-subst sigma delta) returns t, this is the substitution that
;;; applied to the list (apply-subst nil sigma V) returns
;;; (apply-subst nil delta V)

(defun matching-subst (sigma delta)
  (mv-let (match bool)
	  (subs-subst-mv sigma delta)
	  (declare (ignore bool))
	  match))

;;; ====== MATCHING-SUBST-R
;;; Restriction of (subs-sust sigma delta) to V.

(defun matching-subst-r (sigma delta)
  (restriction (matching-subst sigma delta)
	       (important-variables sigma delta)))


;;; REMARKS:
;;;
;;; 1) The substitution subs-sust-r is the witness substitution to prove
;;; subsumption between sigma(term) and delta(term), for all terms, as
;;; we will prove.

;;; 2) For our particular implementation of subsumption between terms,
;;; subs-sust and subs-sust-r are exactly the same (from a functional
;;; pont of view) (when subs-sust is not nil). But we have to define
;;; subs-sust-r to assure explicitly that outside V, the substitution is
;;; the identity, because this is not derived from the soundness and
;;; completeness theorems of and we forbid ourselves to use particular
;;; properties of a particular matching algorithms.

;;; 3) Note that subst-sust-r probably has many repetitions in his
;;; domain, but this is not a problem for us. We will not use
;;; subs-sust-r to compute, only as a tool to deduce properties.


;;; ============================================================================
;;; 2. Soundness theorem
;;; ============================================================================

;;; We want to prove: if (subs-sust sigma delta), then
;;; the substitutions
;;; delta
;;; and
;;; (composition (subs-subst-r sigma delta) sigma)
;;; are functionally equal.

;;; ----------------------------------------------------------------------------
;;; 3.1 The main lemma needed for the soundness theorem
;;; ----------------------------------------------------------------------------


;;; The main goal here is to prove that:
;;; For all variable x,
;;; (val x (composition (subs-subst-r sigma delta) sigma)) = (val x delta)
;;; if (subs-sust sigma delta)
;;; WE DISTINGUISH THREE CASES.

;;; ············································································
;;; 3.1.1 Case 1: x is a variable outside V
;;; ············································································



(local
 (defthm subs-subst-main-property-variable-x-not-in-V
   (let ((V (important-variables sigma delta)))
     (implies (and
	       (variable-p x)
	       (not (member x V))
	       (subs-subst sigma delta))
	      (equal (instance (val x sigma) (matching-subst-r sigma delta))
		     (val x delta))))
   :hints (("Goal" :in-theory (enable x-not-in-domain-remains-the-same)))))


;;; ············································································
;;; 3.1.2. Case 2: x is a variable of (domain-var sigma)
;;; ············································································


;;; 3.1.2.1 A lemma for this case 2:
;;; subs-subst composed with sigma is equal to delta in V.
;;; ······················································

(local
 (encapsulate
  ()

;;; Two  previous lemmas:
  (local
   (defthm pair-args-success
     (second (pair-args (apply-subst nil sigma l)
			(apply-subst nil delta l)))))

  (local
   (defthm apply-nil-apply-t
     (implies (and (equal (apply-subst nil sigma1 l)
			  (apply-subst nil sigma2 l))
		   (member x l))
	      (equal (instance x sigma1)
		     (instance x sigma2)))
     :rule-classes nil))

;;; A technical lemma:

  (local
   (defthm apply-subst-from-matchers-to-lists-of-terms
     (implies (and
	       (second (pair-args l m))
	       (matcher sigma (first (pair-args l m))))
	      (equal (equal (apply-subst nil sigma l) m) t))
     :hints (("Goal" :induct (pair-args l m)))))

;;; And the intended lemma:

  (defthm matching-subst-composed-sigma-coincide-with-delta-in-V
    (let ((V (important-variables sigma delta)))
      (implies (and
		(variable-p x)
		(member x V)
		(subs-subst sigma delta))
	       (equal (instance (val x sigma) (matching-subst sigma delta))
		      (val x delta))))
    :hints (("Goal" :in-theory (disable important-variables)
	     :use (:instance apply-nil-apply-t
			     (l (important-variables sigma delta))
			     (sigma1 (composition
				      (matching-subst sigma delta) sigma))
			     (sigma2 delta)))))))



;;; REMARKS:
;;; 1) If we not disable important-variables the proof is longer.
;;; 2) The condition (variable-p x) is not necessary, but the proof is
;;; shorter.


;;; The above lemma gives the fundamental property of subs-subst and
;;; matching-subst . We can forget its definition, so we disable their
;;; definitions:

(local (in-theory (disable subs-subst matching-subst)))

;;; 3.1.2.2 Another lemma for case 2:
;;; ·······························

(local
 (defthm variables-co-domain-var
  (implies (member x (domain-var sigma))
	   (subsetp (variables t (val x sigma))
		    (variables nil (co-domain-var sigma))))))


;;; 3.1.2.3 The main result for Case 2
;;; ································

(local
 (defthm
   subs-subst-main-property-variable-x-in-domain-var-sigma
   (implies (and
	     (variable-p x)
	     (member x (domain-var sigma))
	     (subs-subst sigma delta))
	    (equal (apply-subst t (matching-subst-r sigma delta) (val x sigma))
		   (val x delta)))))


;;; ············································································
;;; 3.1.3. Case 3: x in V but not in (domain-var sigma)
;;; ············································································


;;; 3.1.3.1 A lemma for Case 3
;;; In this case, matching and matching-subst-r take the same values.
;;; ·································································

(local
 (defthm
   subsumption-subst-main-property-variable-in-V-not-in-domain-var-sigma-lemma
   (let ((V (important-variables sigma delta)))
     (implies (and
	       (variable-p x)
	       (not (member x (domain-var sigma)))
	       (member x V)
	       (subs-subst sigma delta))
	      (equal (apply-subst t (matching-subst-r sigma delta) (val x sigma))
		     (apply-subst t (matching-subst sigma delta)
				  (val x sigma)))))
   :hints (("Goal" :in-theory (enable x-not-in-domain-remains-the-same)))))


;;; We disable important-variables and matching-subst-r since we do not
;;; need to "extract" more properties from the definitions.

(local (in-theory (disable important-variables matching-subst-r)))


;;; 3.1.3.2 The main result for this case.
;;; This result is not strictly needed, bu we include in favour of
;;; clarity.

(local
 (defthm
   subs-subst-main-property-variable-x-in-V-not-in-domain-var-sigma
   (let ((V (important-variables sigma delta)))
     (implies (and
	       (variable-p x)
	       (not (member x (domain-var sigma)))
	       (member x V)
	       (subs-subst sigma delta))
	      (equal (apply-subst t (matching-subst-r sigma delta) (val x sigma))
		     (val x delta))))))



;;; ----------------------------------------------------------------------------
;;; 3.2 Statements of the soundness theorem
;;; ----------------------------------------------------------------------------

;;; Joining the three cases together, we prove
;;; functional equality between
;;; (composition (matching-subst-r sigma delta) sigma) and delta.


(local
 (defthm
   equal-composition-matching-subst-with-sigma-to-delta-variable
   (implies (and (variable-p x)
		 (subs-subst sigma delta))
	    (equal (val x (composition (matching-subst-r sigma delta) sigma))
		   (val x delta)))
   :hints
   (("Goal"
     :cases ((not (member x (important-variables sigma delta)))
	     (member x (domain-var sigma)))))))




;;; DIFFERENT VERSIONS OF THE SOUNDNESS THEOREM


;;; With terms and list of terms (not only with variables)
;;; ······················································

(local
 (defthm
   equal-composition-subs-subst-with-sigma-to-delta
   (implies (subs-subst sigma delta)
	    (equal (apply-subst
		    flg
		    (composition (matching-subst-r sigma delta) sigma)
		    term)
		   (apply-subst flg delta term)))
   :hints (("Goal" :in-theory (disable
			       composition-of-substitutions-apply)))
   :rule-classes nil))

;;; We prefer this formulation to be called the soundness theorem of
;;; subs-subst

(defthm
  subs-subst-soundness
  (implies (subs-subst sigma delta)
	   (equal
	    (instance term (composition (matching-subst-r sigma delta)
					sigma))

	    (instance term delta)))
   :rule-classes nil
   :hints (("Goal" :use
	    (:instance
	     equal-composition-subs-subst-with-sigma-to-delta
	     (flg t)))))




;;; REMARK: we do not use the two above lemmas as a rewrite rule to avoid
;;; conflicts with composition-of-substitutions-appply. Instead, the
;;; following version will be used as a rewrite rule.

;;; With terms but without using composition
;;; ········································

(defthm
  subs-subst-implies-matching-subst-r-appplied-to-sigma-term-is-delta-term
  (implies (subs-subst sigma delta)
	   (equal (apply-subst flg (matching-subst-r sigma delta)
			 (apply-subst flg sigma term))
		  (apply-subst flg delta term)))
  :hints
  (("Goal" :use
    (:instance equal-composition-subs-subst-with-sigma-to-delta))))


;;; With respect to subsumption between terms
;;; ·········································


;;; Trivial consequence of completeness of subsumption and the previous
;;; lemma:


(defthm
  subs-subst-main-property
  (implies (subs-subst sigma delta)
	   (subs (instance term sigma) (instance term delta)))
  :hints (("Goal" :use
	   ((:instance subs-completeness
		       (t1 (instance term sigma))
		       (t2 (instance term delta))
		       (sigma (matching-subst-r sigma delta)))))))




;;; ============================================================================
;;; 3. Completeness theorem
;;; ============================================================================

(local (in-theory (enable subs-subst)))


;;; We want to prove the following:
;;; If sigma <= delta, then (subs-subst sigma delta).
;;; In fact, it will be more useful to prove


;;; The theorem is very easy to prove, but the problem is how we
;;; formulate the hypothesis sigma <= delta.  We will assume the
;;; existence of two substitutions, called sigma-w and delta-w and the
;;; only property we will assume about them is that sigma-w <=
;;; delta-w. That is, exists another substitution gamma-w such that
;;; delta-w = gamma-w·sigma-w.

;;; We will use encapsulate for that purpose. Let sigma-w, delta-w and
;;; gamma-w three susbtitutions such that delta-w is functionally equal
;;; to (composition gamma-w sigma-w)

;;; HYPOTHESIS:

(encapsulate
 (((sigma-w) => *)
  ((delta-w) => *)
  ((gamma-w) => *))

 (local (defun sigma-w () nil))
 (local (defun delta-w () nil))
 (local (defun gamma-w () nil))

 (defthm sigma-w-delta-w-subsumption-hypothesis
   (equal (instance term (composition (gamma-w) (sigma-w)))
	  (instance term (delta-w)))
   :rule-classes nil))

;;; Now our goal is to prove (subs-subst (sigma-w) (delta-w)).

;;; The assumption as a rewrite rule:
(local
 (defthm sigma-w-delta-w-subsumption-hypothesis-rewrite-rule
   (equal (instance (instance term (sigma-w)) (gamma-w))
	  (instance term (delta-w)))
   :hints (("Goal" :use sigma-w-delta-w-subsumption-hypothesis))))

;;; The main lemma
(defthm gamma-w-matcher
  (matcher (gamma-w)
	   (first (pair-args (apply-subst nil (sigma-w) l)
			     (apply-subst nil (delta-w) l)))))

;;; And the completeness theorem:

(defthm subs-subst-completeness
  (subs-subst (sigma-w) (delta-w))
  :rule-classes nil
  :hints (("Goal" :use
	   (:instance match-mv-completeness
		      (sigma (gamma-w))
		      (S (system-subs-subst (sigma-w) (delta-w)))))))

;;; REMARK: Note that this result can be easily used by functional
;;; instantiation (see for example unification-definition.lisp).


;;; ============================================================================
;;; 4. Closure properties of subs-subst
;;; ============================================================================

(local (in-theory (enable matching-subst matching-subst-r
		   important-variables)))

;;; ============================================================================
;;; 4.1 Closure properties for the soundness theorem
;;; ============================================================================


;;; We are going to prove that, provided the two substitutions are in a
;;; given signature, the witness substitution used for the soundness
;;; proof above, is also in the given signature.

(encapsulate
 ()

 (local
  (defthm substitution-s-p--apply-subst-nil-term-s-p-aux
    (implies (and (substitution-s-p sigma)
		  (true-list-of-eqlablep l))
	     (term-s-p-aux nil (apply-subst nil sigma l)))))

 (local
  (defthm pair-args-system-p
    (implies (and (term-s-p-aux nil l)
		  (term-s-p-aux nil m))
	     (system-s-p (first (pair-args l m))))))

 (defthm matching-subst-substitution-s-p
   (implies (and (substitution-s-p sigma)
		 (substitution-s-p delta))
	    (substitution-s-p (matching-subst sigma delta))))

 (local
  (defthm restriction-substitution-s-p
    (implies (and (substitution-s-p sigma)
		  (true-list-of-eqlablep l))
	     (substitution-s-p (restriction sigma l)))))

 (defthm matching-subst-r-substitution-s-p
   (implies (and (substitution-s-p sigma)
		 (substitution-s-p delta))
	    (substitution-s-p (matching-subst-r sigma delta)))))





;;; ----------------------------------------------------------------------------
;;; 4.2 Closure property for the completeness theorem
;;; ----------------------------------------------------------------------------

;;; We can prove a slightly different version of the completeness
;;; theorem: the closure property of the completeness theorem
;;;

;;; We want to prove the following:
;;; let us suppose that sigma and gamma are two substitutions IN A GIVEN
;;; SIGNATURE. Suppose that sigma <= delta, i.e., there exists a
;;; substitution gamma IN THE SAME SIGNATURE such that sigma(term) =
;;; gamma.sigma(term), FOR ALL TERM IN THE SIGNATURE.
;;; Then (subs-subst sigma delta).

;;; Let us formulate the hypothesis using encapsulate:


(encapsulate
 (((sigma-w-s) => *)
  ((delta-w-s) => *)
  ((gamma-w-s) => *))

 (local (defun sigma-w-s () nil))
 (local (defun delta-w-s () nil))
 (local (defun gamma-w-s () nil))

 (defthm sigma-w-s-substitution-s-p (substitution-s-p (sigma-w-s)))
 (defthm delta-w-s-substitution-s-p (substitution-s-p (delta-w-s)))
 (defthm gamma-w-s-substitution-s-p (substitution-s-p (gamma-w-s)))

 (defthm sigma-w-s-delta-w-s-subsumption-hypothesis
   (implies (term-s-p term)
	    (equal (instance term (composition (gamma-w-s) (sigma-w-s)))
		   (instance term (delta-w-s))))
   :rule-classes nil))

;;; Now our goal is to prove (subs-subst (sigma-w-s) (delta-w-s)).


;;; The assumption as a rewrite rule:
(local
 (defthm sigma-w-s-delta-w-s-subsumption-hypothesis-rewrite-rule
   (implies (variable-s-p x)
	    (equal (instance (val x (sigma-w-s)) (gamma-w-s))
		   (val x (delta-w-s))))
   :hints (("Goal"
	    :use (:instance
		  sigma-w-s-delta-w-s-subsumption-hypothesis
		  (term x))))))

;;; The main lemma
(local
 (defthm gamma-w-s-matcher
   (implies (true-list-of-eqlablep l)
	    (matcher (gamma-w-s)
		     (first (pair-args (apply-subst nil (sigma-w-s) l)
				       (apply-subst nil (delta-w-s)
						    l)))))))
;;; And the closure property for the completeness theorem

(defthm subs-subst-completeness-closure
  (subs-subst (sigma-w-s) (delta-w-s))
  :rule-classes nil
  :hints (("Goal" :use
	   (:instance match-mv-completeness
		      (sigma (gamma-w-s))
		      (S (system-subs-subst (sigma-w-s) (delta-w-s)))))))

;;; REMARK: Note that this result can be easily used by functional
;;; instantiation.

;;; We disable the defintions of subs-subst (the subsumption relation)
;;; and matching-subst-r (the witness substitution)

(in-theory (disable subs-subst matching-subst-r))





