;;; unification-pattern.lisp
;;; Definition and correctness of a rule-based unification algorithm
;;; with undefined selection function. This is a "pattern" for concrete
;;; unification algorithms. See unification.lisp
;;; Created 14-10-99. Last revision: 10-12-2000
;;; =================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "unification-pattern")

|#

(in-package "ACL2")
(include-book "subsumption-subst")
(include-book "../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

;;; ********************************************************************
;;; DEFINITION AND VERIFICATION OF A RULE-BASED UNIFICATION ALGORITHM
;;; WE USE THIS BOOK TO PROVIDE A "PATTERN" FOR DEFINING A CONCRETE AND
;;; EXECUTABLE UNIFICATION ALGORITHM.
;;; ********************************************************************

;;; ============================================================================
;;; 1. The transformation rules
;;; ============================================================================


;;; ----------------------------------------------------------------------------
;;; 1.1 Definition.
;;; ----------------------------------------------------------------------------


;;; To formalize some kind of non-determinism, we partially define a
;;; selection function sel, assuming only the property that sel selects
;;; an element of every non-empty list. This function will be used to
;;; select an equation from the set unsolved equations.


(encapsulate

 ((sel (lst) t))

 (local (defun sel (lst) (car lst)))

 (defthm sel-selects
   (implies (consp l) (member (sel l) l))))

;;; The rules of transformation. This function is intended to act on a
;;; pair of systems, S-sol. The first one, S, has the equations to be
;;; solved, and the second one has the bindings done for the moment. An
;;; equation is selected from S, and according to this equation, a rule
;;; of transformation is applied. Note that for every particular
;;; instance of sel, we have a concrete unification algorithm.

;;; We define here a function that applies one step of
;;; transformation. The rules of transformation are essentially the ones
;;; given by Martelli and Montanari.

;;; There are seven rules of transformations, every rule named as in the
;;; comments. Note that the selected equation determines the rule to
;;; apply. If unsolvability is detected, nil is returned.


(defun transform-mm-sel (S-sol)
  (let* ((S (first S-sol)) (sol (rest S-sol))
	 (ecu (sel S))
	 (t1 (car ecu)) (t2 (cdr ecu)) (R (eliminate ecu S)))
    (cond ((equal t1 t2) (cons R sol))                 ;;; *DELETE*
	  ((variable-p t1)
	   (if (member t1 (variables t t2))
	       nil                                     ;;; *CHECK*
	     (cons                                     ;;; *ELIMINATE*
	      (apply-syst (list ecu) R)
	      (cons ecu (apply-range (list ecu) sol)))))
	  ((variable-p t2)
	   (cons (cons (cons t2 t1) R) sol))           ;;; *ORIENT*
	  ((not (equal (car t1) (car t2))) nil)        ;;; *CONFLICT*
	  (t (mv-let (pair-args bool)
		     (pair-args (cdr t1) (cdr t2))
		   (if bool
		       (cons (append pair-args R) sol) ;;; *DESCOMPOSE*
		     nil))))))                         ;;; *NOT-PAIR*


;;; PROOF PLAN:

;;; Prove that applying transformations repeatedly, beginning with (cons
;;; S nil), and stopping when the first system is empty (or
;;; unsolvability is detected), we obtain:
;;; 1) If S is solvable, a most general solution.
;;; 2) nil otherwise.

;;; Iterative application of transform-mm will be defined by:
;(defun solve-system-sel (S-sol)
;  (if (normal-form-syst S-sol)
;      S-sol
;    (solve-system-sel (transform-mm-sel S-sol))))


;;; We will follow the satandard proof given in the literature.
;;; We have to prove that:
;;; - Transformations preserves the set of solutions.
;;; - Idempotence of the second system is preserved.
;;; - Every idempotent substitution is a most general solution of itself.
;;; - A normal form is always reached (giving a suitable ordinal
;;;   measure for the admission of solve-system-sel)

;;; For guard verification purposes, we will also prove that the
;;; properties system-p and substitution-p are preserved for the first
;;; and second system, respectively.


;;; ----------------------------------------------------------------------------
;;; 1.2 How we deal with selection (first part)
;;; ----------------------------------------------------------------------------

;;; Since S and (cons x (eliminate x S)) are equal-set, and some of our
;;; predicates are congruences (in some of their arguments) w.r.t. the
;;; equal-set equivalence relation, let's take advantage of this.

;;; The rewriting rule

(local
 (encapsulate
  ()
  (local (defthm select-eliminate-and-cons-equal-set
	   (implies (member ecu S)
		    (and (subsetp S (cons ecu (eliminate ecu S)))
			 (subsetp (cons ecu (eliminate ecu S)) S)))
	   :hints (("Goal" :induct (eliminate ecu S)))
	   :rule-classes nil))

  (defthm select-eliminate-and-cons-equal-set-instance
    (let* ((S (first S-sol)) (ecu (sel S)))
      (implies (and (consp S-sol) (consp S))
	       (equal-set S (cons ecu (eliminate ecu S)))))
    :hints (("Goal" :use
	     ((:instance select-eliminate-and-cons-equal-set
			 (S (first S-sol))
			 (ecu (sel (first S-sol))))))))))

;;; REMARK: This is only a trick: if select-eliminate-and-cons-equal-set is
;;; used as a rewrite rule, it lead us to non-terminating rewritings. We
;;; will only use the rule when the system S is (car S-sol), so we only
;;; need the above (terminating) rewriting rule



;;; The congruence respect solution
(local
 (encapsulate
  ()
  (local (defthm member-solution
	   (implies (and
		     (member ecu S)
		     (solution sigma S))
		    (equal (instance (car ecu) sigma)
			   (instance (cdr ecu) sigma)))))
  (local (defthm subsetp-solution
	   (implies (and (subsetp s1 s2)
			 (solution sigma s2))
		    (solution sigma s1))))

  (defcong equal-set iff (solution sigma s) 2)))


;;; The congruence with respect to system-var

(local
 (encapsulate
  ()
  (local (defthm subsetp-variables-lemma-1
	   (implies (member ecu s2)
		    (subsetp (variables t (car ecu))
			     (system-var s2)))))

  (local (defthm subsetp-variables-lemma-2
	   (implies (member ecu s2)
		    (subsetp (variables t (cdr ecu))
			     (system-var s2)))))

  (local (defthm subsetp-system-var
		       (implies (subsetp S1 S2)
				(subsetp (system-var S1) (system-var S2)))))

  (defcong equal-set equal-set (system-var s) 1)))


;;; ============================================================================
;;; 2. Main properties of transform-mm-sel
;;; ============================================================================

;;; This is the main section of this book. We are going to prove some
;;; properties of transform-mm. Since transform-mm implements a set of
;;; transformation rules, we will need a set of lemmas for each property
;;; we want to prove and each rule of the transformation system. In the
;;; sequel, the name of the transformation rule will precede the
;;; corresponding set of lemmas.


;;; ----------------------------------------------------------------------------
;;; 2.1 transform-mm-sel preserves the set of solutions of S-sol
;;; ----------------------------------------------------------------------------


;;; One previous lemma:

(local
 (defthm solution-append
   (equal (solution sigma (append S1 S2))
	  (and (solution sigma S1) (solution sigma S2)))))


;;; Equivalence for each rule (some rules do not need auxiliary lemmas)
;;; ···································································


;;; ····················
;;; 2.1.1 rule DECOMPOSE
;;; ····················
(local
 (defun induction-transform-sel-decompose-rule (l1 l2)
   (if (or (atom l1) (atom l2))
       t
     (induction-transform-sel-decompose-rule (cdr l1) (cdr l2)))))

(local
 (defthm transform-sel-rule-decompose
   (implies (second (pair-args l1 l2))
	    (equal (solution sigma (first (pair-args l1 l2)))
		   (equal (apply-subst nil sigma l1)
			  (apply-subst nil sigma l2))))
   :hints (("Goal" :induct
	    (induction-transform-sel-decompose-rule l1 l2)))))

;;; REMARK: The induction hint makes the proof shorter.



;;; ·····················
;;; 2.1.2  rule ELIMINATE
;;; ·····················

;;; If sigma is a solution of sol, and x is a variable, then
;;; sigma(sol(x)) = sol(x).

(local
 (encapsulate
  ()
  (local
   (defthm main-property-eliminate-lemma
     (implies (and (solution sigma sol) (variable-p x) flg)
	      (equal
	       (apply-subst flg sigma (val x sol))
	       (val x sigma)))))

;;; If sigma is a solution of S, sigma = sigma · S

  (defthm substitutions-solution-system
    (implies (solution sigma S)
	     (equal
	      (apply-subst flg sigma (apply-subst flg S term))
	      (apply-subst flg sigma term))))))

;;; IMPORTANT REMARK: The above rule is key to prove the generality of
;;; the solution obatained.

;;; Two corolaries:

(local
 (defthm main-property-eliminate
   (implies (solution sigma sol)
	    (equal
	     (solution sigma (apply-syst sol S))
	     (solution sigma S)))))


(local
 (defthm main-property-eliminate-corolary
   (implies (solution sigma sol)
	    (equal
	     (solution sigma (apply-range sol s))
	     (solution sigma s)))))


;;; ················
;;; 2.1.3 rule CHECK
;;; ················

;;; GOAL:
;;; Prove that x = term, when x is not in term and is not term, has no
;;; solution.

;;; PROOF PLAN:
;;; We will see sigma(x) /= sigma (term), for every sigma.
;;; We need:
;;; * term is of the form (f t1...tn), and x is in some t_i.
;;; * sigma(x) is subterm of sigma(t_i)
;;; * sigma(t_i) is a son of sigma(term)
;;; * Every subterm has size less or equal than the term.
;;; * Every son has less size than the term.
;;; * so size(sigma(x)) < size (sigma(term)) (they are not equal).

(local
 (encapsulate
  ()

  (local
   (defthm if-x-in-term-sigma-x-subterm-of-sigma-term
     (implies (and (variable-p x)
		   (member x (variables flg term)))
	      (subterm flg (val x sigma) (apply-subst flg sigma term)))))

  (local
   (defthm
     if-x-is-not-term-and-is-in-term-then-is-in-some-argument
     (implies (and (member x (variables t term))
		   (not (equal x term)))
	      (member x (variables nil (cdr term))))))

  (local
   (defthm size-subterm
     (implies (subterm flg t1 t2)
	      (>= (size flg t2) (size t t1)))
     :rule-classes nil))

  (local
   (defthm
     size-of-sigma-x-leq-than-the-size-of-sigma-of-arguments
     (implies (and
	       (variable-p x)
	       (member x (variables t term))
	       (not (equal x term)))
	      (>= (size nil (apply-subst nil sigma (cdr term)))
		  (size t (val x sigma))))
     :rule-classes nil
     :hints (("Goal" :use
	      ((:instance size-subterm (flg nil)
			  (t1 (val x sigma))
			  (t2 (apply-subst nil sigma (cdr term)))))))))

;;; ===== Corolary:
;;; sigma(x) does not have the same size than sigma(term).
  (defthm
    transform-sel-check-rule-not-equal-size
    (implies (and
	      (variable-p x)
	      (member x (variables t term))
	      (not (equal x term)))
	     (not (equal (size t (val x sigma))
			 (size t (apply-subst t sigma term)))))
    :rule-classes nil
    :hints (("Goal"
	     :use (:instance
		   size-of-sigma-x-leq-than-the-size-of-sigma-of-arguments))))))

;;; REMARK: It can be proved that is <, but it is not necessary


;;; And finally:
;;; x = term, if x is a variable in term and term is not variable, has
;;; no solution.

(local
 (defthm transform-sel-check-rule
   (implies (and
	     (variable-p x)
	     (member x (variables t term))
	     (not (equal x term)))
	    (not (equal  (val x sigma)
			 (apply-subst t sigma term))))
   :hints (("Goal"
	    :use ((:instance
		   transform-sel-check-rule-not-equal-size))))))

;;; ···················
;;; 2.1.4 rule CONFLICT
;;; ···················

;;; The equation (f t1 ... tn) = (g s1 ... sm), with f/=g has no
;;; solution:

(local
 (defthm transform-mm-sel-conflict-rule
   (implies (and (not (variable-p t1))
		 (not (variable-p t2))
		 (not (equal (car t1) (car t2))))
	    (not (equal (apply-subst t sigma t1)
			(apply-subst t sigma t2))))))

;;; ····················
;;; 2.1.5 rule NOT-PAIR
;;; ····················

;;; If sigma(t1...tn . a) = sigma(s1...sm . b), then n=m and a=b:
;;; ======= Corolary: The equation (f t1 ... tn . a) = (g s1 ... sm . b)
;;; has no solution when n/=m o' a/=b.

(local
 (encapsulate
  ()
  (local
   (defthm transform-sel-not-pair-rule-lemma
     (implies (equal (apply-subst nil sigma l)
		     (apply-subst nil sigma m))
	      (second (pair-args l m)))))

  (defthm transform-sel-not-pair-rule
    (implies (and (not (variable-p t1))
		  (not (variable-p t2))
		  (not (second (pair-args (cdr t1) (cdr t2)))))
	     (not (equal (apply-subst t sigma t1)
			 (apply-subst t sigma t2)))))))


;;; ··················
;;; 2.1.6 And finally:
;;; ··················

;;; Three lemmas to state that transform-mm-sel preserves the set of
;;; solutions:


(local
 (defthm transform-mm-sel-equivalent-1
   (implies (and
	     (consp S-sol)
	     (consp (first S-sol))
	     (solution sigma (union-systems S-sol)))
	    (solution sigma (union-systems (transform-mm-sel S-sol))))))



(local
 (defthm transform-mm-sel-equivalent-2
   (implies (and
	     (consp S-sol)
	     (consp (first S-sol))
	     (transform-mm-sel S-sol)
	     (solution sigma (union-systems (transform-mm-sel S-sol))))
	    (solution sigma (union-systems S-sol)))))



(local
 (defthm transform-sel-unsolvable
   (implies (and (not (transform-mm-sel S-sol))
		 (consp S-sol)
		 (consp (first S-sol)))
	    (not (solution sigma (union-systems S-sol))))))


;;; REMARK: although redundant, (consp S-sol) makes proofs shorter.


;;; ----------------------------------------------------------------------------
;;; 2.2 transform-mm-sel preserves idempotence of the second system.
;;; ----------------------------------------------------------------------------

;;; Our goal:
; (defthm transform-mm-sel-preserves-idempotency
;   (let ((transformed (transform-mm-sel (cons S sol))))
;     (let ((St (first transformed)) (solt (cdr transformed)))
;       (implies (and
; 		(consp S)
; 		transformed
; 		(idempotent sol)
; 		(disjointp (system-var S) (domain sol)))
; 	       (and (idempotent solt)
; 		    (disjointp (system-var St) (domain
; 						       solt)))))))
;;; INTERESTING REMARK: Note that we are proving that there are a number
;;; of INVARIANTS in any sequence of transformations:
;;; - Set of solutions.
;;; - Idempotence of the second system.
;;; - Every variable in the domain of the second system does not appear
;;;   elsewher in the pair of system.
;;; This last two properties needs to be proved together. Note that
;;; idempotence needs two prove two properties: that we have a
;;; system-substitution and that the variables of the co-domain are not
;;; in the domain. See the definition of idempotence in terms.lisp


;;; A technical lemma:

(local
 (defthm system-var-append
   (equal (system-var (append x y))
	  (append (system-var x) (system-var y)))))


;;; As we said before, in the following, we have to prove this result
;;; for every transformation rule. Only two rules, DECOMPOSE and
;;; ELIMINATE needs help form the user


;;; ····················
;;; 2.2.1 rule DECOMPOSE
;;; ····················

;;; Properties to prove that, for the rule decompose, the variables of
;;; the system S are disjoint from the domain of sol.

(local
 (encapsulate
  ()
  (defthm pair-args-system-var-lemma-1  ;;it will be used later
    (subsetp (system-var (first (pair-args l1 l2)))
	     (append (variables nil l1) (variables nil l2))))

  (local (defthm pair-args-system-var-lemma-2
	   (implies (second (pair-args l1 l2))
		    (subsetp (append (variables nil l1)
				     (variables nil l2))
			     (system-var (first (pair-args l1 l2)))))
	   :hints (("Goal" :induct
		    (induction-transform-sel-decompose-rule l1 l2)
		    :in-theory
		    (disable select-eliminate-and-cons-equal-set-instance)))))

  (defthm pair-args-system-var
    (implies (second (pair-args l1 l2))
	     (equal-set (system-var (first (pair-args l1 l2)))
			(append (variables nil l1)
				(variables nil l2)))))))


;;; ····················
;;; 2.2.2 rule ELIMINATE
;;; ····················

;;; Properties to prove that, for the rule eliminate, the variables of
;;; the system S and the co-domain of sol are disjoint from the domain
;;; of sol.


(local
 (defthm apply-range-preserves-domain
   (equal (domain (apply-range sigma S)) (domain S))))

(local
 (defthm co-domain-de-apply-range
  (equal (co-domain (apply-range sigma s))
	 (apply-subst nil sigma (co-domain s)))))


(local
 (defthm apply-range-preserves-system-substitution
  (implies (system-substitution S)
	   (system-substitution (apply-range sigma S)))))


(local
 (defthm eliminate-variables-in-co-domain
  (implies (not (member (car ecu) (variables t (cdr ecu))))
	   (not (member (car ecu)
			(variables flg (apply-subst flg (list ecu) s)))))))

(local
 (defthm variables-apply-subsetp-lemma
  (implies (and (not (member x (variables flg term)))
		(not (member x (variables nil (co-domain sigma)))))
	   (not (member x (variables flg (apply-subst flg sigma term)))))))


(local
 (defthm variables-apply-subsetp
  (subsetp (variables flg (apply-subst flg sigma term))
	   (append (variables flg term) (variables nil (co-domain sigma))))
  :hints (("Goal" :in-theory (enable not-subsetp-witness-lemma)))))

(local
 (defthm subsetp-disjoint
   (implies (and (subsetp a b)
		 (disjointp m b))
	    (disjointp m a))
   :rule-classes nil))

(local
 (defthm
   domain-disjoint-co-domain-eliminate-bridge-lemma
  (implies (disjointp m
		      (append (variables flg term)
			      (variables nil (co-domain sigma))))
	   (disjointp m (variables flg (apply-subst flg sigma term))))
  :hints (("Goal" :use
	   ((:instance
	     subsetp-disjoint
	     (b (append (variables flg term) (variables nil (co-domain sigma))))
	     (a (variables flg (apply-subst flg sigma term)))))))))


(local
 (defthm eliminate-eliminate-variables
  (implies (not (member (car ecu) (variables t (cdr ecu))))
	   (not (member (car ecu) (system-var
				   (apply-syst (list ecu) s)))))
  :hints (("Goal" :induct (len s)))))


(local
 (defthm eliminate-eliminate-variables-2
  (implies (and (not (member x (variables nil (co-domain sigma))))
		(not (member x (system-var s))))
	   (not (member x (system-var
			   (apply-syst sigma s)))))))


(local
 (defthm subsetp-system-var-co-domain
  (subsetp (system-var (apply-syst sigma s))
	   (append (variables nil (co-domain sigma))
		   (system-var s)))
  :hints (("Goal" :in-theory
	   (enable not-subsetp-witness-lemma)))))


(local
 (defthm
   domain-disjoint-system-eliminate-bridge-lemma
   (implies (disjointp m
		       (append (variables nil (co-domain sigma))
			       (system-var S)))
	   (disjointp m
		      (system-var (apply-syst sigma S))))
   :hints (("Goal"
	    :use ((:instance
		   subsetp-disjoint
		   (b (append (variables nil (co-domain sigma)) (system-var S)))
		   (a (system-var (apply-syst sigma S)))))))))


;;; ····················
;;; 2.2.3 And finally
;;; ····················

(local
 (defthm transform-mm-sel-preserves-idempotency
   (let* ((S (first S-sol)) (sol (rest S-sol))
	  (transformado (transform-mm-sel S-sol))
	  (St (first transformado)) (solt (cdr transformado)))
     (implies (and
	       (consp S-sol)
	       (consp S)
	       transformado
	       (idempotent sol)
	       (disjointp (system-var S) (domain sol)))
	      (and (idempotent solt)
		   (disjointp (system-var St) (domain solt)))))))

;;; We extracted all we wanted about idempotent. So we disable it.
(local (in-theory (disable idempotent)))


;;; ----------------------------------------------------------------------------
;;; 2.3 transform-mm-sel preserves system-p and substitution-p
;;; ----------------------------------------------------------------------------

;;; This section is needed for guard verification.

;;; ············································································
;;; 2.3.1 preservation of the system-p property
;;; ············································································

(local
 (encapsulate
  ()

;;; Some previous lemmas for the result


  (local
   (defthm system-s-p-apply-syst
     (implies (and (system-s-p S)
		   (substitution-s-p sigma))
	      (system-s-p (apply-syst sigma S)))))

  (local
   (defthm system-s-p-variable-s-p-cdr
     (implies (and (system-s-p S)
 		   (member equ S)
 		   (variable-p (cdr equ)))
 	      (eqlablep (cdr equ)))))


  (local
   (defthm substitution-s-p-member-system-s-p
     (implies (and (system-s-p S)  ;;; the order between the hypothesis is
	       		           ;;; important (free variables)
		   (member equ S)
		   (variable-p (car equ)))
	      (substitution-s-p (list equ)))))

  (local
   (defthm term-s-p-member-system-s-p
     (implies (and (system-s-p S)  ;;; the order between the hypothesis is
		     	         ;;; important (free variables)
		   (member equ S))
	      (term-s-p (car equ)))))


  (local
   (defthm system-s-p-term-p-bridge-lemma
     (implies (and (system-s-p S)
		   (member ecu S)
		   (not (variable-p (car ecu)))
		   (not (variable-p (cdr ecu))))
	      (and (term-s-p-aux nil (cdar ecu))
		   (term-s-p-aux nil (cddr ecu))))))

;;; And the main result:

  (defthm transform-mm-sel-preserves-system-s-p
    (implies (and
	      (consp S-sol)
	      (consp (first S-sol))
	      (system-s-p (first S-sol)))
	     (system-s-p (first (transform-mm-sel S-sol))))
    :hints (("Goal" :in-theory (disable substitution-s-p))))))


;;; ············································································
;;; 2.3.2 preservation of the system-p property
;;; ············································································

(local
 (encapsulate
  ()

;;; Previous lemmas:
  (local
   (defthm system-s-p-eqlablep-car
     (implies (and (system-s-p S)
 		   (member equ S)
 		   (variable-p (car equ)))
 	      (eqlablep (car equ)))))


  (local
   (defthm substitution-s-p-apply-range
     (implies (and (substitution-s-p sol)
		   (substitution-s-p sigma))
	      (substitution-s-p (apply-range sigma sol)))))


  (local
   (defthm termp-s-p-member-system-s-p
     (implies (and (system-s-p S)
		   (member equ S))
	      (and
	       (term-s-p (cdr equ))))))

;;; And the main result:

  (defthm transform-mm-sel-preserves-substitution-s-p
    (implies (and
	      (consp S-sol)
	      (consp (first S-sol))
	      (system-s-p (first S-sol))
	      (substitution-s-p (cdr S-sol)))
	     (substitution-s-p (cdr (transform-mm-sel S-sol)))))))



;;; ----------------------------------------------------------------------------
;;; 2.4 Termination properties of transform-mm-sel
;;; ----------------------------------------------------------------------------


;;; Recall, we want define:
;(defun solve-system-sel (S-sol)
;  (if (normal-form-syst S-sol)
;      S-sol
;    (solve-system-sel (transform-mm-sel S-sol))))


;;; Proof plan for the admission of solve-system-sel:

;;; We will define a measure unification-measure
;;; We will prove that unification-measure to prove that
;;; (unification-measure (transform-mm-sel S-sol)) is e0-ord-< than
;;; (unification-measure S-sol)

;;; Unification-measure is a lexicographical
;;; combination of these three quantities (let S the first of S-sol):
;;; - Number of distinct variables of S.
;;; - Number of function symbols of S.
;;; - Number of equations of S with a variable as its righ-hand side.

;;; See the definition of unification-measure in terms.lisp


;;; In this section, we will provide a number of lemmas needed to prove
;;; the following:

;(defthm unification-measure-decreases
;  (implies (not (normal-form-syst S-sol))
;	   (e0-ord-< (unification-measure (transform-mm-sel S-sol))
;		     (unification-measure S-sol))))

;;; Due to the definition of e0-ord-<, this lemma means the
;;; following. Let S be (car S-sol).
;;; 1) The number of distinct variables of S does not increase after one
;;; step of transformation.
;;; 2) If the number of distinct variables of the transformed system
;;; does not change, then size-system does not increase after one step of
;;; transformation.
;;; 3) If the above two quantities do not change, then
;;; n-variables-right-hand-side strictly decreases.



;;; ············································································
;;; 2.4.1 transform-mm-sel does not add new variables
;;; ············································································

;;; Goal:
;;; We will prove that the variables of S are a subset of
;;; the variables of the transformed, for every rule.

;;; Some lemmas about eliminate
;;; ···························

(local
  (defthm subsetp-variables-delete
   (subsetp (system-var (eliminate ecu S))
	    (system-var S))))

(local
  (defthm subsetp-variables-eliminate-lemma
    (implies (member ecu S)
  	    (subsetp (append (system-var (list ecu))
  			     (system-var (eliminate ecu S)))
  		     (system-var S)))
     :rule-classes nil))


(local
  (defthm subsetp-variables-eliminate
   (implies
    (and (member ecu s)
 	(variable-p (car ecu)))
    (subsetp (system-var
 	     (apply-syst (list ecu) (eliminate ecu s)))
 	    (system-var s)))
   :hints (("Goal"
 	   :in-theory (disable subsetp-system-var-co-domain)
 	   :use ((:instance subsetp-variables-eliminate-lemma)
 		 (:instance subsetp-system-var-co-domain
 			    (sigma (list ecu))
 			    (S (eliminate ecu S))))))))

;;; Lemmas dealing with length, setps and subsetps
;;; ··············································

(local
 (defthm len-subsetp-setp
   (implies (and (setp l) (setp m) (subsetp l m))
	   (<= (len l) (len m)))
   :hints (("Goal" :induct (subset-induction l m)))))

(local
 (defthm subsetp-make-set
   (implies (subsetp l m)
	    (subsetp (make-set l) (make-set m)))))


(local
 (encapsulate
  ()

;;; Main lemma (in terms of subsetp)
;;; ································

  (local
   (defthm transform-sel-does-not-add-new-variables
     (let* ((S (first S-sol))
	    (transformed (transform-mm-sel S-sol))
	    (St (first transformed)))
       (implies (and (consp S) (consp S-sol))
		(subsetp (system-var St)
			 (system-var S))))
     :hints (("Subgoal 5"
	      :use (:instance subsetp-variables-eliminate
			       (ecu (sel (car S-sol)))
			       (S (car S-sol)))))))

;;; The main lemma (the previous lemma in terms of n-system-var)
;;; ····························································

  (defthm
    transform-does-not-increases-n-variables
    (implies (not (normal-form-syst S-sol))
	     (>= (n-system-var (first S-sol))
		 (n-system-var (first (transform-mm-sel S-sol)))))
    :rule-classes :linear
    :hints (("Goal" :in-theory
	     (disable system-var transform-mm-sel))))))


;;; ············································································
;;; 2.4.2 The rule eliminate eliminates one variable from S
;;; ············································································

;;; This subsection is needed to show that when n-system-var does not
;;; change after one step of transformation, then the rule ELIMNATE has
;;; not been applied.

;;; PROOF PLAN:
;;; The idea is to use length-subsetp-setp-strict (see below), where x
;;; is (car ecu)):

(local
 (encapsulate
  ()

  (local
   (defthm positive-length-member
     (implies (member x l)
	      (< 0 (len l)))
     :rule-classes (:rewrite :linear)))

  (local
   (defthm member-eliminate
     (implies (and (member x l)
		   (not (equal x y)))
	      (member x (eliminate y l)))))

  (defthm len-subsetp-setp-strict
    (implies (and
	      (setp l)
	      (setp m)
	      (subsetp l m)
	      (member x m)
	      (not (member x l)))
	     (< (len l) (len m)))
    :hints (("Goal" :induct (subset-induction l m)))
    :rule-classes nil)))


;;; A technical lemma:

(local
 (defthm subsetp-variables-orient-2
  (implies (and (member ecu S) (variable-p (car ecu)))
	   (member (car ecu) (system-var S)))))

;;; REMARK: The previous lemma is trivial, but is needed because we
;;; disable system-var in the following lemma.

;;; And the main lemma:

(local
  (defthm eliminate-variables-strict
   (implies
    (and
     (member ecu S)
     (variable-p (car ecu))
     (not (member (car ecu) (variables t (cdr ecu)))))
    (> (n-system-var S)
       (n-system-var (apply-syst (list ecu)
				 (eliminate ecu S)))))
   :rule-classes :linear
   :hints (("Goal" :use
 	   ((:instance len-subsetp-setp-strict
 		       (l (make-set
 			   (system-var (apply-syst (list ecu)
 						   (eliminate ecu S)))))
 		       (m (make-set (system-var S)))
 		       (x (car ecu))))
 	   :in-theory (disable system-var)))))

;;; REMARK: In this lemma, the (first S-sol) version is more
;;; complicated.


;;; ············································································
;;; 2.4.3 How we deal with selection (second part).
;;; ············································································

;;; equal-set is not a congruence w.r.t. size-system and
;;; n-variables-right-hand-side. See observaciones.txt to understand why
;;; a congruence based approach does not work We define the following
;;; rewrite rules to rewrite (size-system (first S-sol)) y
;;; (n-variables-right-hand-side S-sol)

(local
 (defthm size-system-cons-select-and-delete-one-lemma
    (implies (member ecu S)
	     (equal (size-system S)
		    (size-system (cons ecu (delete-one ecu S)))))
    :rule-classes nil))

(local
 (defthm size-system-cons-select-and-delete-one
   (implies (consp (first S-sol))
	    (equal (size-system (first S-sol))
		   (size-system (cons (sel (first S-sol))
				      (delete-one (sel (first S-sol))
						  (first S-sol))))))
   :hints (("Goal"
	    :use ((:instance size-system-cons-select-and-delete-one-lemma
			     (S (first S-sol))
			     (ecu (sel (first S-sol)))))))))



(local
 (defthm n-variables-rhs-cons-select-and-delete-one-lemma
  (implies (member ecu S)
	   (equal (n-variables-right-hand-side S)
		  (if (variable-p (cdr ecu))
		      (1+ (n-variables-right-hand-side
			   (delete-one ecu S)))
		    (n-variables-right-hand-side (delete-one ecu S)))))
  :rule-classes nil))

(local
 (defthm n-variables-rhs-cons-select-and-delete-one
  (let ((S (first S-sol)) (ecu (sel (first S-sol))))
    (implies (consp S)
	     (equal (n-variables-right-hand-side S)
		    (if (variable-p (cdr ecu))
			(1+ (n-variables-right-hand-side
			     (delete-one ecu S)))
		      (n-variables-right-hand-side (delete-one ecu
							       S))))))
  :hints (("Goal" :use
	   (:instance
	    n-variables-rhs-cons-select-and-delete-one-lemma
	    (ecu (sel (first S-sol)))
	    (S (first S-sol)))))))


;;; Note that our transformation select and ELIMINATE (which removes all
;;; occurrences, not only the first on, as delete-one does): The
;;; following linear arithmetic rules relates eliminate and delete-one:

(local
 (defthm size-system-eliminate-delete-one-lemma
  (<= (size-system (delete-one x S))
      (size-system S))
  :rule-classes :linear))


(local
 (defthm size-system-eliminate-delete-one
  (>= (size-system (delete-one x S))
      (size-system (eliminate x S)))
  :rule-classes :linear))


(local
 (defthm n-variables-right-hand-side-eliminate-delete-one-lemma
  (<= (n-variables-right-hand-side (delete-one x S))
      (n-variables-right-hand-side S))
  :rule-classes :linear))


(local
 (defthm n-variables-right-hand-side-eliminate-delete-one
   (>= (n-variables-right-hand-side (delete-one x S))
       (n-variables-right-hand-side (eliminate x S)))
   :rule-classes :linear))



;;; ············································································
;;; 2.4.4 Size-system does not increase (when n-variables remains the same)
;;; ············································································

;;; Technical lemma:

(local
 (defthm size-system-append
   (equal (size-system (append x y))
	  (+ (size-system x) (size-system y)))))


;;; Needed for the DECOMPOSE rule:

(local
  (defthm size-systems-decompose-lemma
   (implies (second (pair-args l1 l2))
 	   (equal (size-system (first (pair-args l1 l2)))
 		  (+ (size nil l1) (size nil l2))))))


;;; And  the main lemma:

(local
 (defthm
   si-permanece-system-var-al-transformar-decrece-size-system
   (implies (and
	     (not (normal-form-syst S-sol))
	     (equal (n-system-var (first S-sol))
		    (n-system-var (first (transform-mm-sel S-sol)))))
	    (>= (size-system (first S-sol))
		(size-system (first (transform-mm-sel S-sol)))))
   :rule-classes :linear
   :hints (("Goal" :in-theory
	    (disable n-system-var)))))

(local (in-theory (disable size-system-cons-select-and-delete-one)))



;;; ············································································
;;; 2.4.5 n-variables-right-hand-side does not increase (when the two above
;;; quantities remain the same)
;;; ············································································

;;; Lemmas:

(local
 (encapsulate
  ()
  (local
   (defthm size-system-equation-lemma
     (implies (member ecu S)
	      (equal (size-system S)
		     (+ (size t (car ecu))
			(size t (cdr ecu))
			(size-system (delete-one ecu S)))))
     :rule-classes nil))

  (defthm size-system-equation
    (let ((S (first S-sol)) (ecu (sel (first S-sol))))
      (implies (consp S)
	       (equal (size-system S)
		      (+ (size t (car ecu))
			 (size t (cdr ecu))
			 (size-system (delete-one ecu S))))))
    :hints (("Goal" :use
	     (:instance
	      size-system-equation-lemma
	      (S (first S-sol))
	      (ecu (sel (first S-sol)))))))))

;;; REMARK: the form of this rule to avoid non-termination.


(local
 (defthm size-t->-0
  (implies (not (variable-p term)) (< 0 (size t term)))
  :rule-classes :linear))

(local
 (defthm n-variables-right-hand-side-orient
  (implies
   (and
    (member ecu S)
    (variable-p (cdr ecu))
    (not (variable-p (car ecu))))
   (< (n-variables-right-hand-side (eliminate ecu S))
      (n-variables-right-hand-side S)))))


(local
 (defthm n-variables-right-hand-side-check-lemma
  (implies (and (member ecu S) (variable-p (car ecu)))
	   (consp  (system-var S)))
  :rule-classes nil))

(local
 (defthm n-variables-right-hand-side-check
  (implies (and (consp S) (variable-p (car (sel S))))
	   (consp  (system-var S)))
  :hints (("Goal"
	   :use ((:instance
		  n-variables-right-hand-side-check-lemma
		  (ecu (sel S))))))))


;;; And the main lemma:

(local
 (defthm
  if-n-variables-and-size-are-equal-transform-mm-sel-decrease-n-variables-r-h-s
  (implies (and
	    (not (normal-form-syst S-sol))
	    (equal (n-system-var (first S-sol))
		   (n-system-var (first (transform-mm-sel S-sol))))
	    (equal (size-system (first S-sol))
		   (size-system (first (transform-mm-sel S-sol)))))
	   (< (n-variables-right-hand-side
	       (first (transform-mm-sel S-sol)))
	      (n-variables-right-hand-side (first S-sol))))
  :otf-flg t
  :rule-classes :linear
  :hints (("Goal" :in-theory
	   (disable n-system-var size-system)))))


(local (in-theory (disable n-variables-rhs-cons-select-and-delete-one)))

;;; ············································································
;;; 2.4.6 Compiling the previous results: the  main termination property
;;; ············································································

;;; We disable some definition and lemmas


(local (in-theory (disable n-system-var
		    size-system
		    n-variables-right-hand-side)))
(local (in-theory
	(disable size-system-equation)))

;;; We disable transform-mm-sel
;;; This will allow previous lemmas about transform-sel be used.

(in-theory (disable transform-mm-sel))


;;; AND THE MAIN TERMINATION THEOREMS
;;; ·································

(defthm ordinalp-unification-measure
  (e0-ordinalp (unification-measure S-sol)))


(defthm unification-measure-decreases
  (implies (not (normal-form-syst S-sol))
	   (e0-ord-< (unification-measure (transform-mm-sel S-sol))
		     (unification-measure S-sol))))

;;; We disable unification-measure (we already know all we needed)

(local (in-theory (disable unification-measure)))






;;; ============================================================================
;;; 3. solve-system-sel: applying transform-sel until a normal form is reached
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 3.1 Definition.
;;; ----------------------------------------------------------------------------


;;; IMPORTANT REMARK:
;;; The following functions are partially defined because the selection
;;; function sel is partially defined. Concrete instantiations of this
;;; algorithm can be defined and their properties can be easily obtained
;;; by functional instantiations. See unification-one-definition.lisp
;;; for a concrete unification algorithm

;;; ======= SOLVE-SYSTEM-SEL

(defun solve-system-sel (S-sol)
  (declare (xargs :measure (unification-measure S-sol)))
  (if (normal-form-syst S-sol)
      S-sol
    (solve-system-sel (transform-mm-sel S-sol))))

;;; ----------------------------------------------------------------------------
;;; 3.2 Properties of solve-system-sel
;;; ----------------------------------------------------------------------------


;;; ··········································
;;; 3.2.1 solve-system-sel preserves solutions
;;; ··········································

;;; A technical lemma

(local
  (defthm if-solvable-transform-sel-success
   (implies (solve-system-sel (transform-mm-sel S-sol))
	    (transform-mm-sel S-sol))))


;;; This is for the three following lemmas:
(local (in-theory (disable union-systems)))

;;; The main three lemmas to state that the set of solutions is preserved
;;; by sove-sel.

(local
 (defthm
   solve-system-sel-equivalent-1
   (implies (and (solution sigma (union-systems S-sol))
		 (consp S-sol))
	    (solution sigma (union-systems (solve-system-sel S-sol))))
   :rule-classes nil))

(local
 (defthm solve-system-sel-equivalent-2
  (implies (and  (solve-system-sel S-sol)
		 (solution sigma (union-systems (solve-system-sel S-sol)))
		 (consp S-sol))
	   (solution sigma (union-systems S-sol)))
  :rule-classes nil))

(local
 (defthm solve-system-sel-unsolvable
  (implies (and (not (solve-system-sel S-sol))
		(consp S-sol))
	   (not (solution sigma (union-systems S-sol))))
  :rule-classes nil))

;;; REMARK: we don't need (consp S-sol), but the proof is shorter.

(local (in-theory (enable union-systems)))


;;; ·············································
;;; 3.2.2 solve-system-sel preserves idempotence
;;; ·············································


(local (in-theory (disable disjointp-conmutative)))


(local
 (defthm
   solve-system-sel-preserves-idempotency
   (let* ((S (first S-sol))  (sol (cdr S-sol))
	  (solve-system-sel (solve-system-sel S-sol))
	  (solucion (cdr solve-system-sel)))
      (implies (and
		(consp S-sol)
		solve-system-sel
		(idempotent sol)
		(disjointp (system-var S) (domain sol)))
	       (idempotent solucion)))
   :hints (("Goal" :induct (solve-system-sel S-sol)))))


;;; ····························································
;;; 3.2.3 solve-system-sel preserves system-p and substitution-p
;;; ····························································

;;; Closure property

(local
 (defthm
   solve-system-sel-substitution-s-p
   (let* ((S (first S-sol))  (sol (cdr S-sol))
	  (solve-system-sel (solve-system-sel S-sol))
	  (solucion (cdr solve-system-sel)))
      (implies (and
		(consp S-sol)
		solve-system-sel
		(system-s-p S) (substitution-s-p sol))
	       (substitution-s-p solucion)))
      :hints (("Goal" :induct (solve-system-sel S-sol)))))



;;; ============================================================================
;;; 4. mgs-sel: An algorithm for finding the most general solution of S
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 4.1 Definition.
;;; ----------------------------------------------------------------------------

;;; We simply call solve-system-sel with the input (cons S nil)

;;; ========= MGS-SEL

(defun mgs-sel (S)
  (let ((solve-system-sel (solve-system-sel (cons S nil))))
    (if solve-system-sel (list (cdr solve-system-sel)) nil)))

;;; REMARK: In order to distinguish the empty substitution nil, from nil
;;; as fail, "pack" the result in a list.

;;; ----------------------------------------------------------------------------
;;; 4.2 Main properties of mgs-sel
;;; ----------------------------------------------------------------------------

;;; ······························································
;;; THEOREM 4.2.1. If S is solvable, then (mgs-sel S) succeeds.
;;; ······························································

(defthm mgs-sel-completeness
  (implies (solution sigma S)
	   (mgs-sel S))
  :rule-classes nil
  :hints
  (("Goal" :use
    ((:instance solve-system-sel-unsolvable (S-sol (cons S nil)))))))

;;; ======= One technical lemmas:

(local
 (defthm
   in-normal-forms-S-is-solvable-by-any-sigma
   (solution sigma (first (solve-system-sel S-sol)))))


;;; ·······································································
;;; THEOREM 4.2.2: If (mgs-sel S) succeeds, then the system is solvable
;;; (and a solution is (first (mgs-sel S))
;;; ·······································································

(local
 (defthm mgs-sel-soundness
  (implies (mgs-sel S)
	   (solution (first (mgs-sel S)) S))
  :rule-classes nil
  :hints (("Goal" :use
	   ((:instance solve-system-sel-equivalent-2
		       (S-sol (cons S nil))
		       (sigma (first (mgs-sel S)))))))))

;;; ····················································
;;; THEOREM 4.2.3: (first (mgs-sel S)) is idempotent.
;;; ·····················································


(local
 (defthm mgs-sel-idempotent
  (idempotent (first (mgs-sel S)))))


;;; REMARK: This is true even if (mgs-sel S) fails


;;; ···························································
;;; THEOREM 4.2.4:  The substitution returned by mgs-sel is
;;; substitution-p, whenever its input system is system-p
;;; ····························································

;;; This theorem is needed for guard verification.


(local
 (defthm substituion-s-p-mgs-sel
   (implies (system-s-p S)
	    (substitution-s-p (first (mgs-sel S))))
   :hints (("Goal" :use
	    (:instance
	     solve-system-sel-substitution-s-p
	     (S-sol (cons S nil)))))))





;;; ··································································
;;; THEOREM 4.2.5: If sigma is a solution of S, (first (mgs-sel S))
;;; subsumes sigma.  (thus, (first (mgs-sel S)) is a mgs of S)
;;; ···································································

;;; Lemma: If sigma is a solution of S, then for all term, (first
;;; (mgs-sel S))(term) subsumes sigma(term), with the matching
;;; substitution, sigma, for all terms.


(local
 (defthm mgs-sel-most-general-solution-main-lemma
  (implies (solution sigma S)
	   (equal (instance (instance term (first (mgs-sel S)))
			    sigma)
		  (instance term sigma)))
  :hints (("Goal" :use
	   (:instance
	    solve-system-sel-equivalent-1 (S-sol (cons S nil)))))))

;;; We disable mgs-sel

(in-theory (disable mgs-sel))

(local
 (defthm mgs-sel-most-general-solution
  (implies (solution sigma S)
	   (subs-subst (first (mgs-sel S)) sigma))
  :hints (("Goal"
	   :use
	   ((:functional-instance
	     subs-subst-completeness
	     (sigma-w (lambda ()
			(if (solution sigma S) (first (mgs-sel S)) nil)))
	     (gamma-w (lambda ()
			(if (solution sigma S) sigma nil)))
	     (delta-w (lambda ()
			(if (solution sigma S) sigma nil)))))))))


;;; REMARK: note the interesting use of functional instantiation here,
;;; where the functional substitutions assigns to sigma-w, gamma-w and
;;; delta-w, lambda expressions with free variables in their
;;; bodies. This trick is used several times in the ACL2 books.


;;; ============================================================================
;;; 5. mgu-sel: Unification of two terms
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 5.1 Definitions.
;;; ----------------------------------------------------------------------------

;;; ======= UNIFIABLE-SEL
;;; This is only a particular case of solve-sel. We solve the sistem
;;; (list (cons t1 t2))

(defun unifiable-sel (t1 t2)
  (mgs-sel (list (cons t1 t2))))

;;; We can also define the property the computed unifier:
(defun mgu-sel (t1 t2)
  (first (unifiable-sel t1 t2)))

;;; ----------------------------------------------------------------------------
;;; 5.2 Main properties mgu-sel and unifiable-sel.
;;; ----------------------------------------------------------------------------

;;; Inmediate consequences of the properties of mgs-sel: note that two
;;; terms t1 and t2 are unifiable iff the system (list (cons t1 t2)) is
;;; solvable (and an unifier of t1 and t2 is a solution of (list (cons
;;; t1 t2)))


;;; ······································································
;;; THEOREM 5.2.1: If t1 and t2 are unifiable, then (unifiable-sel t1 t2).
;;; ······································································

(defthm  unifiable-sel-completeness
  (implies (equal (instance t1 sigma)
		  (instance t2 sigma))
	   (unifiable-sel t1 t2))
  :rule-classes nil
  :hints (("Goal" :use
	   (:instance mgs-sel-completeness
		       (S (list (cons t1 t2)))))))


;;; ········································································
;;; THEOREM 5.2.2: If (unifiable-sel t1 t2), t1 and t2 are unifiable
;;; (and (mgu-sel t1 t2) is an unifier).
;;; ········································································


(defthm unifiable-sel-soundness
  (implies (unifiable-sel t1 t2)
	   (equal (instance t1 (mgu-sel t1 t2))
		  (instance t2 (mgu-sel t1 t2))))
  :hints (("Goal" :use
	   ((:instance mgs-sel-soundness
		       (S (list (cons t1 t2))))))))


;;; ········································································
;;; THEOREM 5.2.3: (mgu-sel t1 t2) is idempotent.
;;; ········································································

(defthm mgu-sel-idempotent
  (idempotent (mgu-sel t1 t2)))

;;; ········································································
;;; THEOREM 5.2.4: If t1 and t2 are terms of a given signature, then mgu-sel
;;; returns a substitution of that signature
;;; ········································································



(defthm mgu-sel-substitution-s-p
  (implies (and (term-s-p t1) (term-s-p t2))
	   (substitution-s-p (mgu-sel t1 t2))))



;;; ········································································
;;; THEOREM 5.2.5: If sigma is an unifier of t1 and t2, then (mgu-sel t1 t2)
;;; subsumes sigma (thus, (mgu-sel t1 t2) is a mgu of t1 and t2).
;;; ········································································

(defthm mgu-sel-most-general-unifier
  (implies (equal (instance t1 sigma)
		  (instance t2 sigma))
	   (subs-subst (mgu-sel t1 t2) sigma)))


;;; We disable mgu-sel

(in-theory (disable mgu-sel))








