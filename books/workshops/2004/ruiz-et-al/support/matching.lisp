;;; matching.lisp
;;; Definition and correctness of a RULE BASED matching
;;; algorithm between systems of equations.
;;; This definition is a PATTERN for concrete matching
;;; algorithms. See subsumption.lisp for a concrete
;;; implementation.
;;; This is an alternative to a more classical formulation in
;;; matching.lisp
;;; Created: 9-10-99 Last revison: 05-01-2001
;;; =============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "matching")

|#



(in-package "ACL2")
(include-book "terms")

;;; ********************************************************************
;;; DEFINITION AND VERIFICATION OF A RULE-BASED SUBSUMPTION ALGORITHM WE
;;; USE THIS BOOK TO PROVIDE A "PATTERN" FOR DEFINING A CONCRETE AND
;;; EXECUTABLE SUBSUMPTION ALGORITHM.
;;; ********************************************************************



;;; ============================================================================
;;; 1. The transformation rules
;;; ============================================================================


;;; ----------------------------------------------------------------------------
;;; 1.1 Definition.
;;; ----------------------------------------------------------------------------


;;; First, we introduce some kind of non-determinism, by partially
;;; defining a selection function a-pair, assuming only the property that
;;; a-pair selects an element of every non-empty list:

(encapsulate

 ((a-pair (lst) t))

 (local (defun a-pair (lst) (car lst)))

 (defthm a-pair-selected
   (implies (consp l) (member (a-pair l) l))))


;;; The rules of transformation. This function is intended to act on a
;;; pair of systems, S-match. The first one, S, has the equations to be
;;; solved, and the second one has the bindings done for the moment. An
;;; equation is selected from S, and according to this equation, a rule
;;; of transformation is applied.

(defun transform-subs-sel (S-match)
  (let* ((S (car S-match)) (match (cdr S-match))
	 (ecu (a-pair S))
	 (t1 (car ecu)) (t2 (cdr ecu))
	 (R (eliminate ecu S)))
    (cond
     ((variable-p t1)
      (let ((bound (assoc t1 match)))
	(if bound
	    (if (equal (cdr bound) t2)
		(cons R match)                        ;;; *** DELETE
	      nil)                                    ;;; *** FAIL-BIND
	  (cons R (cons (cons t1 t2) match)))))       ;;; *** BIND
     ((variable-p t2) nil)                            ;;; *** FAIL-VAR
     ((equal (car t1) (car t2))
      (mv-let (pair-args bool)
	      (pair-args (cdr t1) (cdr t2))
	      (if bool
		  (cons (append pair-args R) match)   ;;; *** DECOMPOSE
		nil)))                                ;;; *** CONFLICT-1
     (t nil))))                                       ;;; *** CONFLICT-2



;;; ----------------------------------------------------------------------------
;;; 1.2 Main properties of transform-subs-sel
;;; ----------------------------------------------------------------------------


;;; ············································································
;;; 1.2.1 How we deal with selection.
;;; ············································································


;;; Firs we prove that equal-set is a congruence w.r.t. the second
;;; argument of matcher:
(local
 (encapsulate
  ()

  (local
   (defthm member-matcher
     (implies (and (matcher sigma S)
		   (member equ S))
	      (equal (instance (car equ) sigma) (cdr equ)))))

  (local
   (defthm subsetp-matcher
     (implies (and (matcher sigma S)
		   (subsetp S1 S))
	      (matcher sigma S1))))


  (defcong equal-set iff (matcher x y) 2)))

;;; Then we define a rewrite rule w.r.t. the equivalence equal-set. This
;;; rule allows the prover to put the selected equation in front of the
;;; system, when we are talking of matchers:

(local
 (encapsulate
  ()
  (local
   (defthm equal-set-selection-and-eliminate-lemma
     (implies (member x S)
	      (equal-set (cons x (eliminate x S)) S))))

  (defthm equal-set-selection-and-eliminate
    (implies (consp (car S-match))
	     (equal-set (car S-match)
			(cons (a-pair (car S-match))
			      (eliminate (a-pair (car S-match))
					 (car S-match))))))))

;;; REMARK: Note why we use (car S-match) (instead of S) in the above rule:
;;; we avoid non-termination.



;;; ············································································
;;; 1.2.2 transform-subs-sel preserves the set of matchers.
;;; ············································································


(local
 (defthm matcher-append
   (equal (matcher sigma (append S1 S2))
	  (and (matcher sigma S1) (matcher sigma S2)))))


(local
 (encapsulate
  ()

  (local
   (defun induction-pair-args (l1 l2)
     (if (or (endp l1) (endp l2))
	 t
       (induction-pair-args (cdr l1) (cdr l2)))))

  (local
   (defthm matcher-pair-args
     (implies (second (pair-args l1 l2))
	      (equal (matcher sigma (car (pair-args l1 l2)))
		     (equal (apply-subst nil sigma l1) l2)))
     :hints (("Goal" :induct (induction-pair-args l1 l2)))))



  (local
   (defthm matcher-sigma-value
     (implies (and
	       (matcher sigma S)
	       (variable-p x)
	       (assoc x S))
	      (equal (val x sigma) (cdr (assoc x S))))))


  (local
   (defthm pair-args-apply-subst
     (second (pair-args term (apply-subst nil sigma term)))))

  (local
   (defthm matcher-topmost-function-symbol
     (implies (and (not (variable-p t1))
		   (not (equal (car t1) (car t2))))
	      (not (equal (instance t1 sigma) t2)))))


  (local
   (defthm matcher-variable-non-variable
     (implies (and (not (variable-p t1))
		   (variable-p t2))
	      (not (equal (instance t1 sigma) t2)))))


  (local
   (defthm matcher-not-pair-args
     (implies (and (not (variable-p t1))
		   (not (second (pair-args t1 t2))))
	      (not (equal (instance t1 sigma) t2)))))

  (local
   (defthm matcher-assoc
     (implies (and
	       (variable-p x)
	       (assoc x S)
	       (not (equal (val x sigma) (cdr (assoc x S)))))
	      (not (matcher sigma S)))))

;;; The three main theorems of this subsubsection
;;; ·············································

  (defthm transform-subs-sel-preserves-matchers-1
    (implies
     (and (not (normal-form-syst S-match))
	  (matcher sigma (union-systems S-match)))
     (matcher sigma (union-systems (transform-subs-sel S-match)))))

  (defthm transform-subs-sel-preserves-matchers-2
    (implies
     (and (not (normal-form-syst S-match))
	  (transform-subs-sel S-match)
	  (matcher sigma (union-systems (transform-subs-sel S-match))))
     (matcher sigma (union-systems S-match))))

  (defthm transform-subs-sel-fail
    (implies
     (and (not (normal-form-syst S-match))
	  (not (transform-subs-sel S-match)))
     (not (matcher sigma (union-systems S-match)))))))




;;; ············································································
;;; 1.2.3 (system-substitution (cdr S-match)) is an invariant in the rules
;;;     of transformation.
;;; ············································································



(local
 (encapsulate
  ()

  (local
   (defthm not-assoc-not-member-domain
     (implies  (and
		(system-substitution S)
		(not (assoc x S)))
	       (not (member x (domain S))))))


  (defthm transform-subs-sel-preserves-system-substitution
    (implies
     (and (not (normal-form-syst S-match))
	  (system-substitution (cdr S-match)))
     (system-substitution (cdr (transform-subs-sel S-match)))))))


;;; ············································································
;;; 1.2.4 Main property of the property system-substitution
;;; ············································································


(local
 (encapsulate
  ()

  (local
   (defthm matcher-extended
     (implies (and (matcher sigma s)
		   (not (member x (domain s)))
		   (system-substitution s))
	      (matcher (cons (cons x term) sigma) s))))

  (defthm system-substitutions-main-property
    (implies (system-substitution S)
	     (matcher S S)))))


;;; ----------------------------------------------------------------------------
;;; 1.3 Termination properties of transform-subs-sel
;;; ----------------------------------------------------------------------------

;;; Let's see that the rules of transformation decreases the length of
;;; the first system of the pair of systems

(encapsulate
 ()

 (local
  (defthm length-system-positive-if-consp
    (implies (consp S)
	     (< 0 (length-system S)))
    :rule-classes :linear))

 (local
  (defthm length-system-append
    (equal (length-system (append s1 s2))
	   (+ (length-system s1) (length-system s2)))))

 (local
  (defthm eliminate-not-member
    (implies (not (member x S))
	     (equal (length-system (eliminate x S))
		    (length-system S)))
    :rule-classes (:rewrite :linear)))

 (local
  (defthm length-system-eliminate
    (implies (member e S)
	     (< (length-system (eliminate e S))
		(length-system S)))
    :rule-classes :linear))

 (local
  (defthm length-system-eliminate-leq
    (<= (length-system (eliminate e S))
	(length-system S))
    :rule-classes :linear))

 (local
  (defthm length-system-selection-and-delete-one-lemma
    (implies (member x S)
 	     (equal (length-system (cons x (delete-one x S)))
 		    (length-system S)))
    :hints (("Goal" :in-theory
	     (disable (:META CANCEL_PLUS-EQUAL-CORRECT))))
    :rule-classes nil)) ;;; I needed this disable, surprisingly (20-8-2002)

 (local
  (defthm length-system-selection-and-delete-one
    (implies (consp (car S-match))
	     (equal (length-system (car S-match))
		    (length-system
		     (cons (a-pair (car S-match))
			   (delete-one (a-pair (car S-match))
				       (car S-match))))))
    :hints (("Goal" :use
	     (:instance length-system-selection-and-delete-one-lemma
			(S (car S-match))
			(x (a-pair (car S-match))))))))

;;; NOTE: This is a very similar technique to use
;;; equal-set-selection-and-eliminate. Note that the same is not true with
;;; eliminate. But the following lemma relates both.

  (local
   (defthm length-system-eliminate-delete-one-x
     (<= (length-system (eliminate x S)) (length-system (delete-one x S)))
     :rule-classes :linear))

  (local
   (defthm length-size-pair-args
     (implies (second (pair-args args1 args2))
	      (equal (length-system (first (pair-args args1 args2)))
		     (+ (length-term nil args1)
			(length-term nil args2))))))

;;; And the main result:
;;; ····················

  (defthm transform-subs-sel-decreases-length-of-first-system
    (implies (not (normal-form-syst S-match))
	     (o< (length-system (car (transform-subs-sel s-match)))
		 (length-system (car s-match))))))

;;; REMARK: This is non-local because will be used to prove admission of
;;; concrete subsumption algorithms by functional instantiation


;;; ----------------------------------------------------------------------------
;;; 1.4 Guard verification: system-p for the first system and
;;; substitution-p for the second system are preserved
;;; ----------------------------------------------------------------------------

(local
 (encapsulate
  ()
;;; ***
  (local
   (defthm system-s-p-variable-s-p
     (implies (and (system-s-p S)
 		   (member equ S)
 		   (variable-p (car equ)))
 	      (variable-s-p (car equ)))))

  (local
   (defthm termp-s-p-member-system-s-p
     (implies (and (system-s-p S)
		   (member equ S))
	      (term-s-p (cdr equ)))))


;;; Closure properties:

  (defthm transform-subs-sel-preserves-system-s-p
    (implies
     (and (not (normal-form-syst S-match))
	  (system-s-p (first S-match)))
     (system-s-p (first (transform-subs-sel S-match)))))


  (defthm transform-subs-sel-sel-preserves-substitution-s-p
    (implies
     (and (not (normal-form-syst S-match))
	  (system-s-p (first S-match))
	  (substitution-s-p (cdr S-match)))
     (substitution-s-p (cdr (transform-subs-sel S-match)))))))

;;; -----------------


;;; ******* We have just "extracted" all the required knowledge of
;;; ******* transform-subs-sel

(in-theory (disable transform-subs-sel))

;;; Other necessary disable:

(local (in-theory (disable union-systems))) ; we will enable later




;;; ============================================================================
;;; 2. Applying transformation rules until a solution (or nil) is found
;;; ============================================================================


;;; ----------------------------------------------------------------------------
;;; 2.1 Definition of subs-system-sel
;;; ----------------------------------------------------------------------------

(defun subs-system-sel (S-match)
  (declare (xargs :measure (length-system (car S-match))))
  (if (normal-form-syst S-match)
      S-match
    (subs-system-sel (transform-subs-sel S-match))))



;;; ----------------------------------------------------------------------------
;;; 2.2 Main properties of subs-system-sel
;;; ----------------------------------------------------------------------------

;;; subs-system-sel inherits the properties of transform-subs-sel

;;; Technical lemma:

(local
 (defthm if-matchable-transform-subs-sel-success
  (implies (subs-system-sel (transform-subs-sel S-match))
	   (transform-subs-sel S-match))))


;;; Three lemmas to state that the set of matchers is preserved by
;;; subs-system-sel
;;; ··········································································

(local
 (defthm subs-system-sel-preserves-matchers-1
   (implies (matcher sigma (union-systems S-match))
	    (matcher sigma (union-systems (subs-system-sel S-match))))))


(local
 (defthm subs-system-sel-preserves-matchers-2
  (implies (and (subs-system-sel S-match)
		(matcher sigma (union-systems (subs-system-sel S-match))))
	   (matcher sigma (union-systems S-match)))))


(local
 (defthm subs-system-sel-fail
  (implies (and (not (subs-system-sel S-match))
		(consp S-match))
	   (not (matcher sigma (union-systems S-match))))))


;;; REMARK: we don't need (consp S-match), but the proofs are shorter.


(in-theory (enable union-systems))

;;; subs-system-sel preserves the property of being a system-substitution.
;;; ··································································

(local
 (defthm subs-system-sel-preserves-system-substitution
  (implies (system-substitution (cdr S-match))
	   (system-substitution (cdr (subs-system-sel S-match))))))

;;; Guard verification: a substitution-s-p is returned
;;; ···················································

(local
 (defthm
   subs-system-sel-substitution-s-p
   (let* ((S (first S-match))  (match (cdr S-match))
	  (subs-system-sel (subs-system-sel S-match))
	  (matcher (cdr subs-system-sel)))
      (implies (and (system-s-p S) (substitution-s-p match))
	       (substitution-s-p matcher)))
      :hints (("Goal" :induct (subs-system-sel S-match)))))



;;; ============================================================================
;;; 3. A (non-deterministic) matching algorithm for systems of equations
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 3.1 Definition of match-sel
;;; ----------------------------------------------------------------------------

(defun match-sel (S)
  (let ((subs-system-sel (subs-system-sel (cons S nil))))
    (if subs-system-sel (list (cdr subs-system-sel)) nil)))

;;; REMARK: To distinguish unsolvability (nil) from the empty
;;; substitution, we "pack" the result in a list.

;;; ----------------------------------------------------------------------------
;;; 3.2 Main properties of match-sel
;;; ----------------------------------------------------------------------------

;;; Technical lemma:

(local
 (defthm
   in-normal-forms-S-is-matchable-by-any-sigma
   (matcher sigma (first (subs-system-sel S-sol)))))


;;; The following properties are inmediate consequence of those given in
;;; 2.2 for subs-system-sel

(defthm match-sel-soundness
  (implies (match-sel S)
	   (matcher (first (match-sel S)) S))
  :rule-classes nil
  :hints
  (("Goal" :use
    (:instance subs-system-sel-preserves-matchers-2
	       (S-match (cons S nil))
	       (sigma (first (match-sel S)))))))


(defthm match-sel-completeness
  (implies (matcher sigma S)
	   (match-sel S))
  :rule-classes nil
  :hints
  (("Goal" :use
    (:instance subs-system-sel-fail (S-match (cons S nil))))))


;;; Closure property: This theorem is needed for guard verification.


(defthm match-sel-substitution-s-p
  (implies (system-s-p S)
	   (substitution-s-p (first (match-sel S))))
  :hints (("Goal" :use
	   (:instance
	    subs-system-sel-substitution-s-p
	    (S-match (cons S nil))))))



;;; We disable match-sel

(local (in-theory (disable match-sel)))

;;; ============================================================================
;;; 4. A (non-deterministic) subsumption algorithm (matching of two terms)
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 4.1 Definition of matching-sel and subs-sel.
;;; ----------------------------------------------------------------------------


(defun subs-sel (t1 t2)
  (match-sel (list (cons t1 t2))))



(defun matching-sel (t1 t2)
  (first (subs-sel t1 t2)))

;;; REMARK: subs-sel checks the subsumption relation between to
;;; terms. If non-nil is a list containing a matching substitution as
;;; its firs element.


;;; ----------------------------------------------------------------------------
;;; 4.2 Soundness and completeness of the subsumption algorithm
;;; ----------------------------------------------------------------------------

;;; Soundness
;;; ·········


(defthm subs-sel-soundness
  (implies (subs-sel t1 t2)
	   (equal (instance t1 (matching-sel t1 t2)) t2))

  :rule-classes nil
  :hints (("Goal" :use
	   (:instance match-sel-soundness (S (list (cons t1 t2)))))))



;;; Completeness
;;; ············


(defthm subs-sel-completeness
  (implies (equal (instance t1 sigma) t2)
	   (subs-sel t1 t2))
  :rule-classes nil
  :hints (("Goal" :use
	   (:instance match-sel-completeness (S (list (cons t1 t2)))))))



;;; Closure property:
;;; (the following theorem is needed for guard verification)
;;; ························································


(defthm matching-sel-substitution-s-p
  (implies (and (term-s-p t1) (term-s-p t2))
	   (substitution-s-p (matching-sel t1 t2))))


;;; SOME CONCLUSIONS:
;;; =================

;;; A comparison is made w.r.t. the more classical definition of a
;;; subsumption algorithm given in the book subsumption-definition-v0.lisp

;;; ADVANTAGES of this rule-based approach:

;;; 1) Several selection strategies could be implemented. A family of
;;; algorithms has been verified.
;;; 2) Less intermediate concepts are needed (extension,
;;; coincide,...). This proof seems easier (although I'm now more
;;; trained with the prover).
;;; 3) A common methodlogy with the verification of a rule-based
;;; unification algorithm is used.


;;; ADVANTAGES of the classical recursive definition:

;;; 1) At the same time, the algorithm for terms and for lists of terms
;;; is verified (nevertheless, the rule-based algorithm can be adapted
;;; to deal with subsumption of lists of terms).





