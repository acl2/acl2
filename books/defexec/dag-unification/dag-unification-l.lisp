;;; ============================================================================
;;; dag-unification-l.lisp
;;; Título: A dag based unification algorithm
;;; ============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "dag-unification-l")

|#



(in-package "ACL2")

(include-book "dag-unification-rules")

(include-book "terms-as-dag")


;;; ============================================================================
;;;
;;; 0) Introducción
;;;
;;; ============================================================================

;;; In this book ({\tt dag-unification-l.lisp}), we define and verify
;;; a unification algorithm based on term dags. This algorithm stores
;;; the terms to be unified as directed acyclic graphs and apply the
;;; rules of transformation of Martelli--Montanari until a solution is
;;; found or unsolvability is detected. The main properties of this
;;; algorithm are proved, showing that it computes a most general
;;; unifier of the input terms, whenever they are unifiable.

;;; In the book {\tt dag-unification-rules.lisp}, we proved how some
;;; sequences of transformation rules can be applied to a directed
;;; acyclic graph that stores a unification problem, obtaining a most
;;; general solution of the problem whenever this problem is
;;; solvable. We also showed that this transformation relation is
;;; noetherian, so we can design an algorithm that exhaustively applies
;;; the rules. In the book {\tt terms-as-dag.lisp} we also defined and
;;; verified a function to store unification problems as directed
;;; acyclic graphs.

;;; Combining the results of these books, we can define and verify a
;;; unification algorithm: given two terms, build the initial
;;; unification problem and iteratively apply the transformation rules
;;; until a most general unifier (or unsolvability) is found.

;;; In the book {\tt dag-unification-st.lisp}, we will define a very
;;; similar algorithm to the one defined here, where the graph is stored
;;; using a single--threaded object ({\em stobjs}) instead of a
;;; list. Thus, we can do destructive updates, making unification much
;;; more efficient. Due to the logical properties of stobjs, we can
;;; easily translate the main properties obtained in this book to the
;;; properties of the stobj version of the algorithm.

;;; Note that some of the functions need some very expensive conditions
;;; (checking that we are dealing with directed acyclic graphs) in order
;;; to ensure termination of the functions. Thus, the algorithm will not
;;; be practical for execution. In the book {\tt
;;; dag-unification-st-program.lisp} we describe how we partially
;;; overcome that drawback.


;;; The following books are used, and contain information that is
;;; relevant to understand the contents of this book:

;;; *)
;;; {\tt dag-unification-rules.lisp}, where the properties of the
;;; transformation rules of Martelli--Montanari acting on term dags are
;;; proved.

;;; *)
;;; {\tt terms-as-dag.lisp}, where an algorithm to store first--order
;;; terms as dags is defined and verified.

;;; -)


;;; ============================================================================
;;;
;;; 1) Applying one step of transformation
;;;
;;; ============================================================================


;;; We define a function that given an indices system, and indices
;;; substitution and term graph, apply one step of transformation (as
;;; described by the set of rules of Martelli-Montanari)

;;; The following macros are useful for a better readability:


(defmacro dag-variable-p (x)
  `(equal (cdr ,x) t))

(defmacro dag-args (x)
  `(cdr ,x))

(defmacro dag-symbol (x)
  `(car ,x))

(defmacro dag-bound-p (x)
  `(integerp ,x))


;;; The following function receives as input a unification
;;; problem. Recall (see {\tt dag-unification-rules.lisp}) that a
;;; unification problem is a three--element list with an indices system
;;; (representing the system of equations to be solved), an indices
;;; substitution (representing the substitution partially computed) and
;;; a term graph storing the unification problem.

;;; Depending on the first equation of the list of equations to be
;;; solved (after "dereferencing" the pointers), one the rules is
;;; applied, obtaining a new unification problem (or @nil@, if
;;; unsolvability is detected):

(defun dag-transform-mm-l (upl)
  (let* ((S (first upl))
	 (U (second upl))
	 (g (third upl))
	 (ecu (car S))
	 (t1 (dag-deref-l (car ecu) g))
	 (t2 (dag-deref-l (cdr ecu) g))
	 (R (cdr S))
	 (p1 (dagi-l t1 g))
	 (p2 (dagi-l t2 g)))
    (cond
     ((= t1 t2) (list R U g))
     ((dag-variable-p p1)
      (if (occur-check-l t t1 t2 g)
	  nil
	(let ((g (update-dagi-l t1 t2 g)))
	  (list R (cons (cons (dag-symbol p1) t2) U) g))))
     ((dag-variable-p p2)
      (list (cons (cons t2 t1) R) U g))
     ((not (eql (dag-symbol p1)
		(dag-symbol p2)))
      nil)
     (t (mv-let (pair-args bool)
		(pair-args (dag-args p1) (dag-args p2))
		(if bool
		    (list (append pair-args R) U g)
		  nil))))))

;;; The above function can be seen as applying a particular operator
;;; (see {\tt dag-unification-rules.lisp}). The following function
;;; computes that operator.

(defun dag-transform-mm-l-op (upl)
   (let* ((S (first upl))
	  (g (third upl))
	  (ecu (car S))
	  (t1 (dag-deref-l (car ecu) g))
	  (t2 (dag-deref-l (cdr ecu) g))
	  (p1 (dagi-l t1 g))
	  (p2 (dagi-l t2 g)))
     (cond
      ((= t1 t2) '(delete 0))
      ((dag-variable-p p1)
       (if (occur-check-l t t1 t2 g)
	   '(occur-check 0)
	 '(eliminate 0)))
      ((dag-variable-p p2) '(orient 0))
      ((not (eql (dag-symbol p1)
		 (dag-symbol p2)))
       '(clash1 0))
      (t (mv-let (pair-args bool)
		 (pair-args (dag-args p1) (dag-args p2))
		 (declare (ignore pair-args))
		 (if bool
		     '(decompose 0)
		   '(clash2 0)))))))


;;; The following two theorems show that the application {\tt
;;; dag-transform-mm-l} obtains the same unification problem than the
;;; application of the operator computed by {\tt
;;; dag-transform-mm-l-op}.

(defthm transform-mm-l-applies-a-legal-operator
  (implies (not (normal-form-syst upl))
	   (unif-legal-l upl (dag-transform-mm-l-op upl))))


(defthm transform-mm-l-applies-an-operator
  (implies (not (normal-form-syst upl))
	   (equal (dag-transform-mm-l upl)
		  (unif-reduce-one-step-l
		   upl (dag-transform-mm-l-op upl)))))

(in-theory (disable dag-transform-mm-l
		    unif-reduce-one-step-l
		    unif-reduce-one-step-s))

(local (in-theory (disable dag-transform-mm-l-op)))

(in-theory (disable unification-measure upl-as-pair-of-systems))

;;;;(local (in-theory (disable bounded-well-formed-upl)))

;;; The noetherian property of the transformation relation (proved in
;;; {\tt dag-unification-rules.lisp} can be used now to prove the
;;; following theorem, showing that a well--founded measure decreases
;;; with every application of {\tt dag-transform-mm-l}.

;;; Although this lemma is proved again for the termination proof of the
;;; following function, we prove it here explicitly, because it will be
;;; used for the termination proof of the stobj based algorithm in the
;;; book {\tt dag-unification-st.lisp}.

(defthm unification-measure-decreases-l
    (implies (and (well-formed-upl upl)
		  (not (normal-form-syst upl)))
	     (o<
	      (unification-measure
	       (upl-as-pair-of-systems (dag-transform-mm-l upl)))
	      (unification-measure (upl-as-pair-of-systems upl)))))


;;; Another theorem that will be useful later, for guard verification of
;;; the stobj based algorithm in the book {\tt dag-unification-st.lisp}.

(defthm well-formed-upl-preserved-by-dag-transform-mm-l
  (implies (and (well-formed-upl upl)
		(not (normal-form-syst upl)))
	   (well-formed-upl (dag-transform-mm-l upl))))


;;; ============================================================================
;;;
;;; 2) Applying sequences of transformations
;;;
;;; ============================================================================


;;; The above lemma justifies the admission of the following
;;; function {\tt solve-upl-l}, a function that iteratively applies
;;; {\tt dag-transform-mm-l}, until the system of equations to
;;; be solved is empty (or until unsolvability is detected):

(defun solve-upl-l (upl)
  (declare (xargs :measure
		  (unification-measure
		   (upl-as-pair-of-systems upl))))
  (if (well-formed-upl upl)
      (if (normal-form-syst upl)
	  upl
	(solve-upl-l (dag-transform-mm-l upl)))
    nil))

;;; Again, this iterative application can be seen as the application of
;;; a sequence of operators starting in the initial unification
;;; problem. This sequence is computed by the following unification
;;; problem:

(local
 (defun solve-upl-l-op (upl)
   (declare (xargs :measure
		   (unification-measure
		    (upl-as-pair-of-systems upl))))
   (if (well-formed-upl upl)
       (if (normal-form-syst upl)
	   nil
	 (cons (dag-transform-mm-l-op upl)
	       (solve-upl-l-op (dag-transform-mm-l upl))))
     'undef)))


;;; This theorem shows that the {\tt solve-upl-l} computes the same than
;;; the sequence of operators.

(local
 (defthm solve-upl-l-unif-seq-l-p-normal-form
   (implies (well-formed-upl upl)
	    (and (unif-seq-l-p upl (solve-upl-l-op upl))
		 (normal-form-syst
		  (unif-seq-l-last upl (solve-upl-l-op upl)))
		 (equal (solve-upl-l upl)
			(unif-seq-l-last upl (solve-upl-l-op upl)))))))


;; This theorem shows that solve-upl-l preserves well-formedness:

(local
 (defthm well-formed-upl-preserved-by-solve-upl-l
   (implies (well-formed-upl upl)
	    (well-formed-upl (solve-upl-l upl)))))





;;; A particular case, when the initial unification problem contains an
;;; indices system and the empty substitution. This function can be seen
;;; as a function to compute the most general solution of the system
;;; associated with an indices system. As above, we can see this
;;; function as applying a sequence of operators:

(defun dag-mgs-l (S g)
  (solve-upl-l (list S nil g)))

(local
 (defun dag-mgs-l-op (S g)
   (solve-upl-l-op (list S nil g))))



(local
 (defthm dag-mgs-l-op-unif-seq-l-p-normal-form
   (implies (well-formed-dag-system S g)
	    (and (mgs-seq-l-p S g (dag-mgs-l-op S g))
		 (equal (dag-mgs-l S g)
			(mgs-seq-l S g (dag-mgs-l-op S g)))))
   :hints (("Goal" :in-theory (enable
			       mgs-seq-l
			       mgs-seq-l-p)))))



;;; Well-formedness of dag-mgs-l

(local
 (defthm dag-mgs-l-preserves-well-formedness
   (implies (well-formed-dag-system S g)
	    (well-formed-upl (dag-mgs-l S g)))
   :hints (("Goal" :use
	    (:instance well-formed-upl-preserved-by-solve-upl-l
		       (upl (list S nil g)))))
   :rule-classes nil))



(local (in-theory (disable dag-mgs-l-op)))
(in-theory (disable dag-mgs-l))

(local
 (in-theory (disable mgs-seq-l-mgs-seq-computed-substitution)))






;;; Since we have shown that {\tt dag-mgs-l} can be seen as applying a
;;; sequence of operators corresponding to the transformation relation
;;; of Martelli--Montanari, and from the properties proved in {\tt
;;; dag-unification-rules.lisp} about sequences of transformations
;;; applied to unification problems, we can now easily prove the main
;;; properties of this algorithm, establishing that it computes a most
;;; general solution of the system of equations pointed by the input
;;; indices system:

(defthm dag-mgs-l-completeness
  (let ((S (tbs-as-system S-dag g)))
    (implies (and (well-formed-dag-system S-dag g)
		  (solution sigma S))
	     (dag-mgs-l S-dag g))))


(defthm dag-mgs-l-soundness
  (let* ((S (tbs-as-system S-dag g))
	 (dag-mgs-l (dag-mgs-l S-dag g))
	 (sol (solved-as-system (second dag-mgs-l) (third dag-mgs-l))))
    (implies (and (well-formed-dag-system S-dag g)
		  dag-mgs-l)
	     (solution sol S))))



(defthm dag-mgs-l-idempotent
  (let* ((dag-mgs-l (dag-mgs-l S-dag g))
	 (sol (solved-as-system (second dag-mgs-l) (third dag-mgs-l))))
    (implies (well-formed-dag-system S-dag g)
	     (idempotent sol)))
  :hints (("Goal" :in-theory (disable idempotent))))

(defthm dag-mgs-l-most-general-solution
  (let* ((S (tbs-as-system S-dag g))
	 (dag-mgs-l (dag-mgs-l S-dag g))
	 (sol (solved-as-system (second dag-mgs-l) (third dag-mgs-l))))
    (implies (and (well-formed-dag-system S-dag g)
		  (solution sigma S))
	     (subs-subst sol sigma))))

;;; ============================================================================
;;;
;;; 3) Unification of two terms
;;;
;;; ============================================================================

;;; We can combine the above algorithm {\tt dag-mgs-l} with the function
;;; {\tt unif-two-terms-problem} defined and verified in the book {\tt
;;; term-as-dag.lisp}. In this way, we receive two terms (in the
;;; standard prefix/list representation) and a graph and we can store
;;; the terms in the graph and apply the unification algorithm on term
;;; dags.

(defun dag-mgu-l (t1 t2 g)
  (let ((g (unif-two-terms-problem-l t1 t2 g)))
    (dag-mgs-l
     (initial-to-be-solved-l g) g)))



(in-theory (disable
		    tbs-as-system
		    initial-to-be-solved-l
		    unif-two-terms-problem-l))


(local (in-theory (disable dag-mgs-l-op-unif-seq-l-p-normal-form)))

;;; The following auxiliary lemmas are needed to prove the main
;;; properties of {\tt dag-mgu-l}. They are an easy consequence of the
;;; properties of {\tt unif-two-terms-problem-l} and {\tt dag-mgs l}:

(local
 (defthm dag-mgu-l-completeness-almost
   (let* ((g-t1-t2 (unif-two-terms-problem-l t1 t2 g))
	  (S-dag-t1-t2 (initial-to-be-solved-l g-t1-t2)))
     (implies
      (and (empty-graph-p g) (term-p t1) (term-p t2)
	   (solution sigma (tbs-as-system S-dag-t1-t2 g-t1-t2)))
      (dag-mgu-l t1 t2 g)))
   :hints (("Goal" :in-theory (disable unif-two-terms-problem-l-stores-the-problem)))
   :rule-classes nil))


(local
 (defthm dag-mgu-l-soundness-almost
   (let* ((g-t1-t2 (unif-two-terms-problem-l t1 t2 g))
	  (S-dag-t1-t2 (initial-to-be-solved-l g-t1-t2))
	  (S (tbs-as-system S-dag-t1-t2 g-t1-t2))
	  (dag-mgu-l (dag-mgu-l t1 t2 g))
	  (sol (solved-as-system (second dag-mgu-l) (third dag-mgu-l))))
     (implies (and (empty-graph-p g) (term-p t1) (term-p t2)
		   dag-mgu-l)
	      (solution sol S)))
   :rule-classes nil))



(local
 (defthm dag-mgu-l-most-general-solution-almost
   (let* ((g-t1-t2 (unif-two-terms-problem-l t1 t2 g))
	  (S-dag-t1-t2 (initial-to-be-solved-l g-t1-t2))
	  (S (tbs-as-system S-dag-t1-t2 g-t1-t2))
	  (dag-mgu-l (dag-mgu-l t1 t2 g))
	  (sol (solved-as-system (second dag-mgu-l) (third dag-mgu-l))))
     (implies (and (empty-graph-p g) (term-p t1) (term-p t2)
		   (solution sigma S))
	      (subs-subst sol sigma)))
    :rule-classes nil))


;;; Finally, the following theorems establish the main properties of
;;; {\tt dag-mgu-l}, showing that {\tt dag-mgu-l} computes the most
;;; general unifier of two terms, whenever it exists.


(defthm dag-mgu-l-completeness
  (implies
   (and (empty-graph-p g) (term-p t1) (term-p t2)
	(equal (instance t1 sigma)
	       (instance t2 sigma)))
     (dag-mgu-l t1 t2 g))
  :hints (("Goal" :use dag-mgu-l-completeness-almost)))




(defthm dag-mgu-l-soundness
  (let* ((dag-mgu-l (dag-mgu-l t1 t2 g))
	 (sol (solved-as-system (second dag-mgu-l) (third dag-mgu-l))))
    (implies (and (empty-graph-p g) (term-p t1) (term-p t2)
		  dag-mgu-l)
	     (equal (instance t1 sol) (instance t2 sol))))
    :hints (("Goal" :use dag-mgu-l-soundness-almost)))




(defthm dag-mgu-l-most-general-solution
  (let* ((dag-mgu-l (dag-mgu-l t1 t2 g))
	 (sol (solved-as-system (second dag-mgu-l) (third dag-mgu-l))))
    (implies (and (empty-graph-p g) (term-p t1) (term-p t2)
		  (equal (instance t1 sigma)
			 (instance t2 sigma)))
	     (subs-subst sol sigma)))
    :hints (("Goal" :use dag-mgu-l-most-general-solution-almost)))



(defthm dag-mgu-l-idempotent
  (let* ((dag-mgu-l (dag-mgu-l t1 t2 g))
	 (sol (solved-as-system (second dag-mgu-l) (third dag-mgu-l))))
    (implies (and (empty-graph-p g) (term-p t1) (term-p t2))
	     (idempotent sol))))



;;; ===============================================================


;;; FALTA AQUI UN TEOREMA NO LOCAL SOBRE LA BUENA FORMACION DE LO QUE
;;; DEVUELVE DAG-MGU-L: bounde-nat-susbtitution-p y
;;; well-formed-term-dag-p (i.e term-graphp-p, dag-p y no-duplicates variables)

(defthm dag-mgu-l-bounded-nat-substitution-p
  (implies
   (and (empty-graph-p g)
	(term-p t1)
	(term-p t2))
   (and (bounded-nat-substitution-p (second (dag-mgu-l t1 t2 g))
				    (len (third (dag-mgu-l t1 t2 g))))
	(well-formed-term-dag-p (third (dag-mgu-l t1 t2 g)))))
  :hints (("Goal" :in-theory (enable dag-mgu-l well-formed-upl)
	   :use (:instance dag-mgs-l-preserves-well-formedness
			   (S (initial-to-be-solved-l (unif-two-terms-problem-l t1 t2 g)))
			   (g (unif-two-terms-problem-l t1 t2 g))))))