;;; ============================================================================
;;; q-dag-unification-rules.lisp
;;; Título: Unification rules on term dags for the quadratic algorithm
;;; 12-03-03
;;; ============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "q-dag-unification-rules")

|#

(in-package "ACL2")


(include-book "dag-unification-rules")



;;; ============================================================================
;;;
;;; 0) Introducción
;;;
;;; ============================================================================

;;; In this book, we define and verify a set of rules of transformation
;;; designed to reflect the behaviour of a quadratic unification
;;; algorithmm to obtain most general solutions of systems of equations,
;;; when these systems of equations are represented as directed acyclicic
;;; graphs (dags). The transformation relation is an extension of the
;;; transformation relation defined in the book {\tt
;;; dag-unification-rules.lisp}: we include a new operator, called
;;; IDENTIFICATION, that identifies two nodes whenever the subtrees
;;; associated to them are equal. We proved in the book {\tt
;;; dag-unification-rules.lisp} that every transformation
;;; done at the dag level corresponds with a transformation done at the
;;; "prefix" level (and that the well-formedness conditions are
;;; preserved). We now prove that the new operator also preserves the
;;; well-formedness conditions and that application of that operator
;;; does not change the "prefix terms" represented. All these
;;; properties imply that some sequences of operators build most general
;;; unifiers (or detect failure of unification).

;;; ============================================================================
;;;
;;; 1) Extending the transformation rules
;;;
;;; ============================================================================


;;; A new operator of the form (IDENTIFY i j):

;;; * Applicability test: whenever i and j are distinct indices in the
;;; dag and the terms whose root nodes are, respectively, i and j, are
;;; equal.
;;; * Step of reduction: modify the dag, making i point to j.


;;; -----------------------------------
;;;
;;; 1.1) Applicability test on term dags
;;;
;;; -----------------------------------



(defun unif-legal-q-identify (i j g)
  (and
   (natp i) (< i (len g))
   (natp j) (< j (len g))
   (not (equal i j))
   (term-dag-non-variable-p i g)
   (term-dag-non-variable-p j g)
   (equal (dag-as-term t i g)
	  (dag-as-term t j g))))

(defun unif-legal-q (upl op)
  (if (equal (first op) 'identify)
      (unif-legal-q-identify (second op) (third op) (third upl))
    (unif-legal-d upl op)))

;;; -----------------------------------
;;;
;;; 1.2) One step of reduction on term dags
;;;
;;; -----------------------------------


(defun unif-reduce-one-step-q-identify (i j S sol g)
  (list S sol (update-dagi-l i j g)))

(defun unif-reduce-one-step-q (upl op)
  (if (equal (first op) 'identify)
      (unif-reduce-one-step-q-identify (second op) (third op) (first upl)
				(second upl) (third upl))
    (unif-reduce-one-step-d upl op)))

;;; ============================================================================
;;;
;;; 2) Relation between the transformations acting on both representations
;;;
;;; ============================================================================

;;; -----------------------------------
;;;
;;; 2,1) Well--formed term dags preserved by the transformations
;;;
;;; -----------------------------------



;;; REPEATED (tye same as induct-occur-check-l-path de dag-unification-rules-bis)

(encapsulate
 ()

 (local
  (defun induct-path-subterm (flg h g path)
    (declare (xargs :measure (measure-rec-dag flg h g)))
    (if (dag-p g)
	(if flg
	    (let ((p (dagi-l h g)))
	      (if (integerp p)
		  (induct-path-subterm flg p g (cdr path))
		(let ((args (cdr p)))
		  (if (equal args t)
		      t
		    (induct-path-subterm nil args g (cdr path))))))
	  (if (endp h)
	      t
	    (cons (induct-path-subterm t (car h) g path)
		  (induct-path-subterm nil (cdr h) g path))))
      path))) ;;; to make this formal relevant

 (local
  (defthm map-nfix-nat-true-listp
    (implies (nat-true-listp l)
	     (equal (map-nfix l) l))))

;;; Repeated
 (local
  (defthm ugly-lemma-1
    (implies flg
	     (equal (dag-as-term flg h g)
		    (dag-as-term t h g)))
    :rule-classes nil))


 (local
  (defthm path-subterm
    (implies (and (dag-p g)
		  (bounded-term-graph-p g n)
		  (if flg (natp h) (nat-true-listp h))
		  (consp p)
		  (path-p p g)
		  (equal (car (last p)) x)
		  (if flg
		      (equal (first p) h)
		    (member (first p) h)))
	     (subterm flg
		      (dag-as-term t x g)
		      (dag-as-term flg h g)))
    :hints (("Goal" :induct
	     (induct-path-subterm flg h g p))
	    ("Subgoal *1/1" :use (:instance ugly-lemma-1
					    (h (nth h g)))))))
;;; Repeated
 (local
  (defthm size-subterm
    (implies (subterm flg t1 t2)
	     (>= (size flg t2) (size t t1)))
    :rule-classes nil))


 (defthm identify-preserves-dag-p-main-lemma
   (implies (and
	     (dag-p g)
	     (bounded-term-graph-p g n)
	     (natp i) (natp j)
	     (term-dag-non-variable-p i g)
	     (term-dag-non-variable-p j g)
	     (not (equal i j))
	     (path-p p g)
	     (equal (first p) j)
	     (equal (car (last p)) i))
	    (not (equal (size t (dag-as-term t j g))
			(size t (dag-as-term t i g)))))
   :hints (("Subgoal 1'" :expand (dag-as-term t p1 g))
	   ("Subgoal 1''" :use
	    (:instance size-subterm
		       (flg nil)
		       (t1 (dag-as-term t (car (last p2)) g))
		       (t2 (dag-as-term nil (cdr (nth p1 g)) g))))
	   ("Subgoal 1'''"
	    :use (:instance path-subterm
			    (flg nil)
			    (h (cdr (nth p1 g)))
			    (x (car (last p2)))
			    (p p2)))))




;;; It would be better to disable obtain-path-from-h-to-x-from-an-updated-dag
;;; in dags.lisp
 (defthm identify-preserves-dag-p
   (implies (and (dag-p g)
		 (bounded-term-graph-p g n)
		 (natp i) (natp j)
		 (not (equal i j))
		 (term-dag-non-variable-p i g)
		 (term-dag-non-variable-p j g)
		 (not (dag-p (update-nth i j g))))

	    (not (equal (dag-as-term t i g)
			(dag-as-term t j g))))

   :hints (("Goal" :use
	    (:instance identify-preserves-dag-p-main-lemma
		       (p (obtain-path-from-h-to-x-from-an-updated-dag i
								       j g)))
	    :in-theory (disable
			obtain-path-from-h-to-x-from-an-updated-dag)))))



(local
 (defthm unif-reduce-one-step-q-preserves-bounded-well-formed-upl
   (implies (and (bounded-well-formed-upl upl n)
		 (<= (len (third upl)) n)
		 (unif-legal-q upl op))
	    (bounded-well-formed-upl (unif-reduce-one-step-q upl op)
				     n))))

;;; Later, we will need that the @n@ of the above theorem be (len (third
;;; upl)). That is, we need a similar theorem for well-formed-upl. Le us
;;; prove it.

(encapsulate
 ()
 (local
  (defthm unif-reduce-one-step-q-preserves-length
    (implies (and (well-formed-upl upl)
		  (unif-legal-q upl op)
		  (unif-reduce-one-step-q upl op))
	     (equal (len (third (unif-reduce-one-step-q upl op)))
		    (len (third upl))))))

 (local (in-theory (enable well-formed-upl-def)))

 (defthm unif-reduce-one-step-q-preserves-well-formed-upl
   (implies (and (well-formed-upl upl)
		 (unif-legal-q upl op))
	    (well-formed-upl (unif-reduce-one-step-q upl op)))
   :hints (("Goal"
	    :in-theory (disable bounded-well-formed-upl
				unif-legal-q
				unif-reduce-one-step-q)
	    :cases ((unif-reduce-one-step-q upl op))))))



;;; -----------------------------------
;;;
;;; 2,2) Applicability
;;;
;;; -----------------------------------

(defthm unif-legal-q-implies-unif-legal-p-for-non-identifications
  (implies (and (well-formed-upl upl)
		(unif-legal-q upl op)
		(not (equal (first op) 'identify)))
	   (unif-legal-p (upl-as-pair-of-systems upl) op)))


;;; -----------------------------------
;;;
;;; 2,3) One step of reduction
;;;
;;; -----------------------------------

;;; When the operator is not an identification:

(defthm unif-reduce-one-step-q-unif-reduce-one-step-s-for-non-identifications
  (implies (and (well-formed-upl upl)
		(unif-legal-q upl op)
		(not (equal (first op) 'identify)))
	   (equal (upl-as-pair-of-systems (unif-reduce-one-step-q upl op))
		  (unif-reduce-one-step-p (upl-as-pair-of-systems upl)
					  op))))


;;; When the operator is an identification:

(defthm identify-on-term-dags
  (implies (and (bounded-term-graph-p g n)
		(dag-p g)
		(natp i) (natp j)
		(term-dag-non-variable-p i g)
		(term-dag-non-variable-p j g)
		(not (equal i j))
		(equal (dag-as-term t i g)
		       (dag-as-term t j g))
		(if flg (natp h) (nat-true-listp h)))
	   (equal
	    (dag-as-term flg h (update-nth i j g))
	    (dag-as-term flg h g))))



(encapsulate
 ()


 (local
  (defthm identify-on-term-dags-tbs-as-system
    (implies (and (bounded-term-graph-p g n)
		  (dag-p g)
		  (natp i) (natp j)
		  (term-dag-non-variable-p i g)
		  (term-dag-non-variable-p j g)
		  (not (equal i j))
		  (equal (dag-as-term t i g)
			 (dag-as-term t j g))
		  (bounded-nat-pairs-true-listp S n))

	     (equal
	      (tbs-as-system S (update-nth i j g))
	      (tbs-as-system S g)))))



 (local
  (defthm identify-on-term-dags-solved-as-system
    (implies (and (bounded-term-graph-p g n)
		  (dag-p g)
		  (natp i) (natp j)
		  (term-dag-non-variable-p i g)
		  (term-dag-non-variable-p j g)
		  (not (equal i j))
		  (equal (dag-as-term t i g)
			 (dag-as-term t j g))
		  (bounded-nat-substitution-p sol n))
	     (equal
	      (solved-as-system sol (update-nth i j g))
	      (solved-as-system sol g)))))


;;; Este se tiene cuando se tenga el anterior
 (defthm unif-reduce-one-step-q-for-identifications
   (implies (and (well-formed-upl upl)
		 (unif-legal-q upl op)
		 (equal (first op) 'identify))
	    (equal (upl-as-pair-of-systems (unif-reduce-one-step-q upl op))
		   (upl-as-pair-of-systems upl)))
   :hints (("Goal" :in-theory (enable well-formed-upl-def
				      upl-as-pair-of-systems
				      unif-legal-q
				      unif-reduce-one-step-q)))))





;;; ============================================================================
;;;
;;; 4) Sequences of transformation rules
;;;
;;; ============================================================================

(in-theory (disable unif-reduce-one-step-q
		    unif-legal-q))


(defun unif-seq-q-p (upl unif-seq)
  (declare (xargs :measure (acl2-count unif-seq)))
  (if (endp unif-seq)
      t
    (let ((op (car unif-seq)))
      (and (unif-legal-q upl op)
	   (unif-seq-q-p
	    (unif-reduce-one-step-q upl op)
	    (cdr unif-seq))))))

(defun unif-seq-q-last (upl unif-seq)
  (if (endp unif-seq)
      upl
    (unif-seq-q-last (unif-reduce-one-step-q upl (car unif-seq))
		     (cdr unif-seq))))

(local
 (defun remove-identifications (unif-seq)
   (cond ((endp unif-seq) unif-seq)
	 ((equal (first (car unif-seq))
		 'identify)
	  (remove-identifications (cdr unif-seq)))
	 (t (cons (car unif-seq)
		  (remove-identifications (cdr unif-seq)))))))

(local
 (defthm unif-seq-q-p-unif-seq-p-p
   (implies (and (well-formed-upl upl)
		 (unif-seq-q-p upl unif-seq))
	    (unif-seq-p-p (upl-as-pair-of-systems upl)
			  (remove-identifications unif-seq)))
   :rule-classes nil))


(local
 (defthm unif-seq-p-last-unif-seq-q-last
   (implies (and (well-formed-upl upl)
		 (unif-seq-q-p upl unif-seq))
	    (and
	     (well-formed-upl (unif-seq-q-last upl unif-seq))
	     (equal
	      (upl-as-pair-of-systems (unif-seq-q-last upl unif-seq))
	      (unif-seq-p-last (upl-as-pair-of-systems upl)
			       (remove-identifications unif-seq)))))
   :rule-classes nil))


;;; For upl with empty initial substitutions


(defun mgs-seq-q-p (S g seq)
  (and (unif-seq-q-p (list S nil g) seq)
       (normal-form-syst (unif-seq-q-last (list S nil g) seq))))

(defun mgs-seq-q (S g seq)
  (unif-seq-q-last (list S nil g) seq))

(local
 (in-theory
  (enable mgs-seq-p mgs-seq bounded-well-formed-upl upl-as-pair-of-systems)))


(local
 (defthm mgs-seq-q-p-mgs-seq-p
   (implies (and (well-formed-dag-system S g)
		 (mgs-seq-q-p S g unif-seq))
	    (mgs-seq-p (tbs-as-system S g) (remove-identifications unif-seq)))
   :hints (("Goal" :use ((:instance unif-seq-q-p-unif-seq-p-p
				    (upl (list S nil g)))
			 (:instance unif-seq-p-last-unif-seq-q-last
				    (upl (list S nil g))))))))


(local
 (defthm mgs-seq-q-mgs-seq-failure-success
   (implies (and (well-formed-dag-system S g)
		 (mgs-seq-q-p S g unif-seq))
	    (iff (mgs-seq (tbs-as-system S g) (remove-identifications unif-seq))
		 (mgs-seq-q S g unif-seq)))
   :hints (("Goal" :use ((:instance unif-seq-q-p-unif-seq-p-p
				    (upl (list S nil g)))
			 (:instance unif-seq-p-last-unif-seq-q-last
				    (upl (list S nil g))))))))

(local
 (defthm mgs-seq-q-mgs-seq-computed-substitution
   (let ((last-upl (mgs-seq-q S g unif-seq)))
     (implies (and (well-formed-dag-system S g)
		   (mgs-seq-q-p S g unif-seq))
	      (equal
	       (solved-as-system (second last-upl)
				 (third last-upl))
	       (second (mgs-seq (tbs-as-system S g)
				(remove-identifications unif-seq))))))
   :hints (("Goal" :use ((:instance unif-seq-q-p-unif-seq-p-p
				    (upl (list S nil g)))
			 (:instance unif-seq-p-last-unif-seq-q-last
				    (upl (list S nil g))))))))

;;; This theorem is also interesting. The graph obtained by a complete
;;; legal sequence of transformations is acyclic:

(defthm mgs-seq-q-dag-p
  (implies (and (well-formed-dag-system S g)
		(mgs-seq-q-p S g unif-seq))
	   (dag-p (third (mgs-seq-q S g unif-seq))))
  :hints (("Goal"
	   :in-theory (enable well-formed-upl-def)
	   :use ((:instance unif-seq-q-p-unif-seq-p-p
			    (upl (list S nil g)))
		 (:instance unif-seq-p-last-unif-seq-q-last
			    (upl (list S nil g)))))))

(local (in-theory (disable mgs-seq-p mgs-seq)))
(in-theory (disable mgs-seq-q-p mgs-seq-q))



;;; ============================================================================
;;;
;;; 5) Using the rules to obtain most general solutions
;;;
;;; ============================================================================

(defthm mgs-seq-q-completeness
  (let ((S (tbs-as-system S-dag g)))
    (implies (and (well-formed-dag-system S-dag g)
		  (solution sigma S)
		  (mgs-seq-q-p S-dag g unif-seq))
	     (mgs-seq-q S-dag g unif-seq)))
  :hints (("Goal" :use (:instance mgs-seq-completeness
				  (unif-seq (remove-identifications unif-seq))
				  (S (tbs-as-system S-dag g))))))


;;; If a complete legal sequence of transformations on term dags
;;; succeeds, then the indices substitution finally obtained represents
;;; a solution of the system represented by the initial indices system:

(defthm mgs-seq-q-soundness
  (let* ((S (tbs-as-system S-dag g))
	 (last-upl (mgs-seq-q S-dag g unif-seq))
	 (sol (solved-as-system (second last-upl) (third last-upl))))
    (implies (and (well-formed-dag-system S-dag g)
		  (mgs-seq-q-p S-dag g unif-seq)
		  last-upl)
	     (solution sol S)))
  :hints (("Goal" :use (:instance mgs-seq-soundness
				  (unif-seq (remove-identifications unif-seq))
				  (S (tbs-as-system S-dag g))))))


;;; If a complete legal sequence of transformations on term dags
;;; succeeds, then the indices substitution finally obtained represents
;;; an idempotent substitution:

(defthm mgs-seq-q-idempotent
  (let* ((last-upl (mgs-seq-q S-dag g unif-seq))
	 (sol (solved-as-system (second last-upl) (third last-upl))))
    (implies (and (well-formed-dag-system S-dag g)
		  (mgs-seq-q-p S-dag g unif-seq))
	     (idempotent sol)))
  :hints (("Goal" :in-theory (disable idempotent))))

;;; If the system represented by an indices system has a solution, then
;;; it is subsumed by the substitution represented by the indices
;;; substitution obtaned by a complet legal sequence of transformations:


(defthm mgs-seq-q-most-general-solution
  (let* ((S (tbs-as-system S-dag g))
	 (last-upl (mgs-seq-q S-dag g unif-seq))
	 (sol (solved-as-system (second last-upl) (third last-upl))))
    (implies (and (well-formed-dag-system S-dag g)
		  (solution sigma S)
		  (mgs-seq-q-p S-dag g unif-seq))
	     (subs-subst sol sigma))))


;;; ===============================================================


