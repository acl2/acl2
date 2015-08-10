;; ============================================================================
;;; q-dag-unification.lisp
;;; Título: A quadratic dag based unification algorithm
;;; ============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "q-dag-unification")

|#


(in-package "ACL2")

(include-book "q-dag-unification-rules")
(include-book "terms-as-dag")


;;;============================================================================
;;;
;;; 0) Introducción
;;;
;;;============================================================================

;;; The rules defined in the book q-dag-unification-rules can be applied
;;; with a certain strategy in order to obtain a quadratic unification
;;; algorithm. For that purpose, we need to specific improvements:
;;; * Apply the identification rule just after the unification of two
;;;   subterms has been achieved. Moreover, this step shouldn't check
;;;   its applicability condition (in order to not to be of exponential
;;;   complexity), but it should be applied only when it is applicable.
;;; * When an occur-check is applied (in both the Eliminate and
;;; Occur-Check rules), we should avoid repeated visits to the same
;;; subterms.

;;; In order to get these improvements, we will introduce what we call
;;; "extended unification problems". These are ordinary dag unification
;;; problems extended in the following way:

;;; - Interleaved with the indices equations, some "identification
;;; marks" may appear. In this way the system of equations can be seen a
;;; stack: when the Decompose rule is applied we previously stack an
;;; identification mark of the nodes that are being unified in that
;;; moment, as well as the equations introduced by the Decompose
;;; rule. In this way, when the unification of the arguments succeeds,
;;; the identification mark is at the top of the stack and this allows
;;; us to apply the identification safely.
;;;
;;; - On the other hand, in order to optimize the "occur-check", we add
;;; a "stamp" list of integers: the number in position i of this list
;;; represents the last time node i of the term dag was visited for
;;; occur check. We also use a time counter that will be
;;; incremented every time the unification procedure calls to the occur
;;; check function. Before visiting a subgraph to check the occurrence
;;; of a variable, we check if its {stamp information is equal to
;;; time. If that is the case we simply return nil, without
;;; traversing the subgraph; otherwise we traverse the subgraph,
;;; updating the stamp information if the variable does not occur
;;; in the subgraph.

;;; Therefore, an extended unification problem consits of:

;;; * An indices system of equations (possibly extended with
;;; identification marks) to be solved.
;;; * An indices substitution (the unifier oartially computed)
;;; * A dag.
;;; * A stamp list.
;;; * A time counter.

;;; Nevertheless, this unification problem has to meet several
;;; properties expressing the specific form of extended unification
;;; problems that the algorithm will manage.

;;; These conditions should express:

;;; - Well-formednes of the graph, the system and the substitution (as
;;;   usual).
;;; - Acyclicness (as usual).
;;; - A condition (invariant during the unification proccess), that
;;;   roughly speaking expresses that the identification marks are well
;;;   placed inside the indices system.
;;; - Another condition that ensures that the improved occur check
;;;   computes the same result than occur-check-d

;;; In this book:

;;; * We will define a function that acting on extended unification
;;; problems applies a reduction step (with a specific control) of
;;; the rules of transformation of the relation defined in the book
;;; q-dag-unification-rule (but without introducing exponential
;;; complexity)

;;; * We will define functions formally epressing the above
;;; "well-formedness" conditions.

;;; * We will prove that, in fact,  under the above conditions the
;;; transformation step given corresponds to a transformotion step
;;; w.r.t. the rule of q-dag-unification-rule

;;; * We will prove that the above conditions are preserved in every
;;; transformation step.

;;; * We will prove that the exhaustive application of the transformation
;;;   steps terminates.

;;; * We will define the rest of the functions of this quadratic
;;; unification algorithm

;;; * And we will translate the properties proved in the book
;;; q-dag-unification-rules to conclude that its a sound and complete
;;; unification algorithm


;;; NOTE: Some of the lemmas proved in this book are needed for guard
;;; verification. In each of them, this is commented.

;;;============================================================================
;;;
;;; 1) Definition of one transformation step in the quadratic unif. algorithm
;;;
;;;============================================================================


;;; For the sake of readability:

(defmacro dag-variable-p (x)
  `(equal (cdr ,x) t))

(defmacro dag-args (x)
  `(cdr ,x))

(defmacro dag-symbol (x)
  `(car ,x))

(defmacro dag-bound-p (x)
  `(integerp ,x))


;;; Improved occur check

(defun occur-check-q (flg x h g stamp time)
  (declare (xargs :measure (measure-rec-dag flg h g)))
  (if (dag-p g)
      (if flg
	  (let ((p (nth h g)))
	    (if (integerp p)
		(occur-check-q flg x p g stamp time)
	      (let ((args (cdr p)))
		(cond ((equal args t) (mv (= x h) stamp))
		      ((= (nth h stamp) time) (mv nil stamp))
		      (t (mv-let (bool stamp)
				 (occur-check-q nil x args g stamp time)
			     (if bool
				 (mv bool stamp)
			       (mv nil (update-nth h time stamp)))))))))
	(if (endp h)
	    (mv nil stamp)
	  (mv-let (bool stamp)
		  (occur-check-q t x (car h) g stamp time)
		  (if bool
		      (mv bool stamp)
		    (occur-check-q nil x (cdr h) g stamp time)))))
    (mv 'undef stamp)))

;;; Transformation step on extended unification problems



(defun dag-transform-mm-q (ext-upl)
  (let* ((ext-S (first ext-upl))
	 (ecu (first ext-S))
	 (R (rest ext-S))
	 (U (second ext-upl))
	 (g (third ext-upl))
	 (stamp (fourth ext-upl))
	 (time (fifth ext-upl)))

    (if (equal (first ecu) 'id)
	(let ((g (update-dagi-l (second ecu) (third ecu) g)))  ;;; IDENTIFICATION
	  (list R U g stamp time))
      (let ((t1 (dag-deref (car ecu) g))
	    (t2 (dag-deref (cdr ecu) g)))
	(if (= t1 t2)
	    (list R U g stamp time)                            ;;; DELETE
	  (let ((p1 (dagi-l t1 g))
		(p2 (dagi-l t2 g)))
	    (cond
	     ((dag-variable-p p1)
	      (mv-let (oc stamp)
		      (occur-check-q t t1 t2 g stamp time)
		      (if oc
			  nil                                 ;;; OCCUR-CHECK
			(let ((g (update-dagi-l t1 t2 g)))
			  (list R (cons (cons (dag-symbol p1) t2) U) g
				stamp (1+ time))))))          ;;; ELIMINATE
	     ((dag-variable-p p2)
	      (list (cons (cons t2 t1) R) U g stamp time))    ;;; ORIENT
	     ((not (eql (dag-symbol p1) (dag-symbol p2)))
	      nil)                                            ;;; CLASH1
	     (t (mv-let (pair-args bool)
			(pair-args (dag-args p1) (dag-args p2))
			(if bool
			    (list (append pair-args
					  (cons (list 'id t1 t2) R))
				  U g stamp time)             ;;; DECOMPOSE
			  nil))))))))))                       ;;; CLASH2



;;;============================================================================
;;;
;;; 2) Well-formedness conditions on extended unification problems
;;;
;;;============================================================================


;;; Well-formedness conditions of the system, the graph and the substitution
;;; -------------------------------------------------------------------------

(defun bounded-nat-pairs-true-listp-with-ids (ext-S n)
  (declare (xargs
	    :guard (natp n)))
  (if (atom ext-S)
      (equal ext-S nil)
    (let ((ecu (car ext-S)))
      (and
       (consp ecu)
       (or
	(and
	 (consp (cdr ecu))
	 (consp (cddr ecu))
	 (equal (first ecu) 'id)
	     (natp (second ecu)) (< (second ecu) n)
	     (natp (third ecu)) (< (third ecu) n))
	(and (natp (car ecu)) (< (car ecu) n)
	     (natp (cdr ecu)) (< (cdr ecu) n)))
       (bounded-nat-pairs-true-listp-with-ids (cdr ext-S) n)))))


(defun bounded-well-formed-extended-upl (ext-upl n)
  (and (bounded-nat-pairs-true-listp-with-ids (first ext-upl) n)
       (bounded-nat-substitution-p (second ext-upl) n)
       (bounded-well-formed-term-dag-p (third ext-upl) n)))


(defun well-formed-extended-upl (ext-upl)
  (declare (xargs :guard (and (consp ext-upl)
			      (consp (cdr ext-upl))
			      (consp (cddr ext-upl))
			      (true-listp (third ext-upl)))))
  (let ((n (len (third ext-upl))))
    (and (bounded-nat-pairs-true-listp-with-ids (first ext-upl) n)
	 (bounded-nat-substitution-p (second ext-upl) n)
	 (well-formed-term-dag-p (third ext-upl)))))

;;; Relation between well-formed-extended-upl and bounded-well-formed-extended-upl

(local
 (defthm well-formed-extended-upl-def
   (equal (well-formed-extended-upl ext-upl)
	  (bounded-well-formed-extended-upl ext-upl (len (third
							  ext-upl))))
   :rule-classes :definition))

(in-theory (disable well-formed-extended-upl))

;;; Unification invariant, ensuring "safe" identifications
;;; ------------------------------------------------------
;;; The main function is ext-upl-id-invariant below. Very long
;;; definition!!

(defun until-first-id (ext-S)
  (declare (xargs
	    :guard (alistp ext-S)))
  (cond ((endp ext-S) nil)
	((equal (first (car ext-S)) 'id)
	 (list (car ext-S)))
	(t (cons (car ext-S) (until-first-id (cdr ext-S))))))


(defun after-first-id (ext-S)
  (declare (xargs
	    :guard (alistp ext-S)))
  (cond ((endp ext-S) ext-S)
	((equal (first (car ext-S)) 'id)
	 (cdr ext-S))
	(t (after-first-id (cdr ext-S)))))

(defun split-extended-system-in-id-stacks (ext-S)
  (declare (xargs
	    :guard (alistp ext-S)))
  (if (endp ext-S)
      nil
    (let* ((ufid (until-first-id ext-S))
	   (lt (car (last ufid))))
      (if (equal (first lt) 'id)
	  (cons ufid
		(split-extended-system-in-id-stacks
		 (after-first-id ext-S)))
	(split-extended-system-in-id-stacks
		 (after-first-id ext-S))))))


(defun equation-equals-equality (p q lhs rhs)
  (declare (xargs
	    :guard t))
  (and (equal p lhs) (equal q rhs)))

(defun equation-justify-equality (p q lhs rhs g)
  (declare (xargs
	    :guard (and (natp p) (natp q)
			      (< p (len g))
			      (< q (len g))
			      (true-listp g)
			      (term-graph-p g))))
  (let ((t1 (dag-deref p g))
	(t2 (dag-deref q g)))
    (and (equal t1 lhs) (equal t2 rhs))))


(defun equations-already-solved (l1 l2 g)
  (declare (xargs
	    :guard
		  (and (bounded-nat-true-listp l1 (len g))
		       (bounded-nat-true-listp l2 (len g))
		       (true-listp g)
		       (term-graph-p g))))
  (cond ((endp l1) (equal l1 l2))
	((endp l2) nil)
	(t (and (equal (dag-as-term t (car l1) g)
		       (dag-as-term t (car l2) g))
		(equations-already-solved (cdr l1) (cdr l2) g)))))


(defun first-id-stack-invariant-aux-with-equations
  (rargs1 rargs2 requations g)
  (declare (xargs
	    :guard
	    (and (bounded-nat-true-listp rargs1 (len g))
		 (bounded-nat-true-listp rargs2 (len g))
		 (bounded-nat-pairs-true-listp requations (len g))
		 (consp requations)
		 (true-listp g)
		 (term-graph-p g))))

  (and (consp rargs1)
       (consp rargs2)
       (if (endp (cdr requations))
	   (and  (or (equation-equals-equality
		      (car rargs1) (car rargs2)
		      (car (first requations))
		      (cdr (first requations)))
		     (and
		      (term-dag-non-variable-p (cdr (first requations))
					       g)
		      (not (term-dag-is-p (car (first requations)) g))
;;; la anterior condición es redundante, pero necesaria para la guarda
		      (term-dag-variable-p (car (first requations)) g)
		      (equation-justify-equality
		       (car rargs1) (car rargs2)
		       (cdr (first requations))
		       (car (first requations))
		       g)))
		 (equations-already-solved (cdr rargs1) (cdr rargs2) g))
	 (and (equation-equals-equality (car rargs1) (car rargs2)
					(car (first requations))
					(cdr (first requations)))
	      (first-id-stack-invariant-aux-with-equations (cdr rargs1)
							   (cdr rargs2)
							   (cdr requations)
							   g)))))

;;; These two functions are onley for the guard definition
(defun id-terna-p (id-equ n)
  (declare (xargs
	    :guard (natp n)))
  (and (consp id-equ)
       (consp (cdr id-equ))
       (consp (cddr id-equ))
       (natp (second id-equ))
       (natp (third id-equ))
       (< (second id-equ) n)
       (< (third id-equ) n)))

(defun id-stack-p (l n)
  (declare (xargs :guard (natp n)))
  (and (consp l)
       (true-listp l)
       (let* ((rid-stack (revlist l))
	      (id-equ (car rid-stack))
	      (requations (cdr rid-stack)))
	 (and (id-terna-p id-equ n)
	      (bounded-nat-pairs-true-listp requations n)))))

;; Two lemmas needed for guard verification
(local
 (defthm bounded-nat-true-listp-revlist
   (implies (bounded-nat-true-listp l n)
 	    (bounded-nat-true-listp (revlist l) n))))

(local
 (defthm nat-true-listp-true-listp
   (implies (nat-true-listp l)
 	    (true-listp l))))


(defun first-id-stack-invariant (id-stack g)
  (declare (xargs
	    :guard
	    (and
	     (true-listp g)
	     (term-graph-p g)
	     (id-stack-p id-stack (len g)))))
  (let* ((rid-stack (revlist id-stack))
	 (id-equ (car rid-stack))
	 (requations (cdr rid-stack))
	 (idc (first id-equ)))
    (and
     (equal idc 'id)
     (let* ((id1 (second id-equ)) ;;; Este let* está aquí por la
				  ;;; verificación de guardas
	    (id2 (third id-equ))
	    (p1 (dagi-l id1 g))
	    (p2 (dagi-l id2 g)))
       (and (natp id1) (natp id2)
	    (not (equal id1 id2))
	    (term-dag-non-variable-p id1 g)
	    (term-dag-non-variable-p id2 g)
	    (equal (dag-symbol p1) (dag-symbol p2))
	    (if (endp requations)
		(equations-already-solved
		 (dag-args p1) (dag-args p2) g)
	      (first-id-stack-invariant-aux-with-equations
	       (revlist (dag-args p1)) (revlist (dag-args p2))
	       requations g)))))))


(defun remaining-id-stacks-invariant-aux (rargs1 rargs2 requations
						 id-equ g)
  (declare (xargs
	    :guard
	    (and
	     (bounded-nat-true-listp rargs1 (len g))
	     (bounded-nat-true-listp rargs2 (len g))
	     (bounded-nat-pairs-true-listp requations (len g))
	     (id-terna-p id-equ (len g))
	     (true-listp g)
	     (term-graph-p g))))
  (and (consp rargs1)
       (consp rargs2)
       (if (endp requations)
	   (and (equation-justify-equality
		 (car rargs1) (car rargs2)
		 (second id-equ) (third id-equ) g)
		(equations-already-solved (cdr rargs1) (cdr rargs2) g))
	 (and (equation-equals-equality (car rargs1) (car rargs2)
					(car (first requations))
					(cdr (first requations)))
	      (remaining-id-stacks-invariant-aux
	       (cdr rargs1) (cdr rargs2) (cdr requations) id-equ g)))))



(defun remaining-id-stacks-invariant (id-equ requations next-id-equ  g)
  (declare (xargs
	    :guard
	    (and
	     (bounded-nat-pairs-true-listp requations (len g))
             (id-terna-p id-equ (len g)) (id-terna-p next-id-equ (len
								  g))
	     (true-listp g)
	     (term-graph-p g))))
  (let* ((idc (first next-id-equ))
	 (id1 (second next-id-equ))
	 (id2 (third next-id-equ)))
    (and (equal idc 'id)
	 (natp id1) (natp id2)
	 (not (equal id1 id2))
	 (term-dag-non-variable-p id1 g)
	 (term-dag-non-variable-p id2 g)
	 (equal (term-dag-symbol id1 g) (term-dag-symbol id2 g))
	 (remaining-id-stacks-invariant-aux
	  (revlist (term-dag-args id1 g)) (revlist (term-dag-args id2 g))
	  requations id-equ g))))


;;; For the guard definition:
(defun id-stack-list-p (idsl n)
  (declare (xargs :guard (natp n)))
  (if (atom idsl)
      (equal idsl nil)
    (and (id-stack-p (first idsl) n)
	 (id-stack-list-p (rest idsl) n))))



(defun iter-remaining-id-stacks-invariant (id-equ id-stack-list g)
  (declare (xargs
	    :guard
	    (and (id-terna-p id-equ (len g))
		 (id-stack-list-p id-stack-list (len g))
		 (true-listp g)
		 (term-graph-p g))))
  (if (endp id-stack-list)
      t
    (let* ((first-id-stack (car id-stack-list))
	   (rfirst-id-stack (revlist first-id-stack))
	   (next-id-equ (car rfirst-id-stack))
	   (requations (cdr rfirst-id-stack)))
      (and (remaining-id-stacks-invariant id-equ requations next-id-equ g)
	   (iter-remaining-id-stacks-invariant next-id-equ (cdr id-stack-list) g)))))


;;; Guard verification
(local
 (defthm bounded-nat-pairs-true-listp-with-ids-alistp
   (implies (bounded-nat-pairs-true-listp-with-ids ext-S n)
 	    (alistp ext-S))))

;;; Guard verification
(local
 (defthm after-first-id-without-ids
   (implies (not (equal (caar (last (until-first-id ext-s))) 'id))
	    (not (consp (after-first-id ext-S))))))

;; Guard verification
(local
 (defthm rest-split-extended-system-in-id-stacks
   (equal (rest (split-extended-system-in-id-stacks ext-s))
	  (split-extended-system-in-id-stacks (after-first-id ext-s)))))


;; Guard verification
(local
 (defthm first-split-extended-system-in-id-stacks
   (equal (first (split-extended-system-in-id-stacks ext-S))
	  (if (equal
	       (first
		(car (last (until-first-id ext-S))))
	       'id)
	      (until-first-id ext-S)
	    nil))))

;; Guard
(local
 (defthm bounded-nat-pairs-true-listp-with-ids-until-first-id-1
   (implies (and (bounded-nat-pairs-true-listp-with-ids ext-s n)
		 (consp ext-S))
	    (bounded-nat-pairs-true-listp (cdr (revlist (until-first-id ext-S)))
					  n))))

;; Guard
(local
 (defthm id-terna-p-first-revlist-until-first-id
   (implies (and (bounded-nat-pairs-true-listp-with-ids ext-S n)
		 (equal (caar (last (until-first-id ext-S))) 'id))
	    (id-terna-p (car (revlist (until-first-id ext-S))) n))))


;; Guard
(local
 (defthm bounded-nat-pairs-true-listp-with-ids-after-first-id
   (implies (bounded-nat-pairs-true-listp-with-ids ext-S n)
	    (bounded-nat-pairs-true-listp-with-ids (after-first-id ext-S) n))))


;; Guard
(local
 (defthm bounded-nat-pairs-true-listp-with-ids-split-id-stack-list-p
   (implies (bounded-nat-pairs-true-listp-with-ids ext-S n)
	    (id-stack-list-p
	     (split-extended-system-in-id-stacks ext-S) n))))


(defun id-invariant (ext-S g)
  (declare (xargs
	    :guard
	    (and (bounded-nat-pairs-true-listp-with-ids ext-S (len
							       g))
		 (true-listp g)
		 (term-graph-p g))
	    :guard-hints (("Goal" :in-theory (disable id-terna-p)))))
  (let* ((id-stacks-list (split-extended-system-in-id-stacks ext-S))
	 (first-id-stack (car id-stacks-list))
	 (rest-id-stacks (cdr id-stacks-list))
	 (last-elt (first (revlist first-id-stack))))
    (or (endp id-stacks-list)
	(and (first-id-stack-invariant first-id-stack g)
	     (iter-remaining-id-stacks-invariant last-elt rest-id-stacks g)))))

(defun ext-upl-id-invariant (ext-upl)
  (declare (xargs :guard (and (consp ext-upl)
			      (consp (cdr ext-upl))
			      (consp (cddr ext-upl))
			      (bounded-nat-pairs-true-listp-with-ids
			       (first ext-upl) (len (third ext-upl)))
			      (true-listp (third ext-upl))
			      (term-graph-p (third ext-upl)))))
  (id-invariant (first ext-upl) (third ext-upl)))


;;; Invariant allowing the "safe" use of the improved occur check
;;; -------------------------------------------------------------


(defun all-marks-integers-less-than-time (stamp time)
  (declare (xargs :guard (integerp time)))
  (if (atom stamp)
      t
    (and (integerp (car stamp))
	 (< (car stamp) time)
	 (all-marks-integers-less-than-time (cdr stamp) time))))


(defun ext-upl-occur-check-invariant (ext-upl)
  (declare (xargs :guard
		  (or (not ext-upl) (>= (len ext-upl) 5))))
  (or (not ext-upl)
      (and
       (equal (len (third ext-upl)) (len (fourth ext-upl)))
       (integerp (fifth ext-upl))
       (all-marks-integers-less-than-time (fourth ext-upl)
					  (fifth ext-upl)))))


;;; Finally, all the conditions in one function
;;; -------------------------------------------

(defun unification-invariant-q (ext-upl)
  (declare (xargs :guard
		  (and (>= (len ext-upl) 5)
		       (true-listp (third ext-upl)))))
  (and (well-formed-extended-upl ext-upl)
       (ext-upl-id-invariant ext-upl)
       (ext-upl-occur-check-invariant ext-upl)))

;;;============================================================================
;;;
;;; 3) Dag-transform-mm-q and the dag unification rules
;;;
;;;============================================================================


;;; We prove in this section that under the above invariants and
;;; conditions, the function dag-transfrom-mm-q can be seen as the
;;; application of an appliable operator


;;; The witness operator is computed by the following function:

(local
 (defun dag-transform-mm-q-op (ext-upl)
   (let* ((ext-S (first ext-upl))
	  (g (third ext-upl))
	  (ecu (car ext-S)))
     (if (equal (first ecu) 'id)
	 (list 'identify (second ecu) (third ecu))
       (let ((t1 (dag-deref (car ecu) g))
	     (t2 (dag-deref (cdr ecu) g)))
	 (if (= t1 t2)
	     '(delete 0)
	   (let ((p1 (dagi-l t1 g))
		 (p2 (dagi-l t2 g)))
	     (cond ((dag-variable-p p1)
		    (if (occur-check-d t t1 t2 g)
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
				'(clash2 0))))))))))))

;;; Let us now prove that this operator is a legal operator such that
;;; when applied to an upl is the same (in some sense that we precise
;;; below) as the result obtained by dag-transform-mm-q



;;; STEP I:

;;; First, we remove from the extended unification problem all the
;;; things that make it "extended", in order to obtain an ordinary
;;; unification problem

(defun remove-ids (ext-S)
  (cond ((endp ext-S) ext-S)
	((equal (first (car ext-S)) 'id)
	 (remove-ids (cdr ext-S)))
	(t (cons (car ext-S) (remove-ids (cdr ext-S))))))
					;)

(defun ext-upl-to-upl (ext-upl)
  (and ext-upl
       (list (remove-ids (first ext-upl))
	     (second ext-upl)
	     (third ext-upl))))

;;; STEP II:


;;; Second, we show that the improved occur-check-d is consistent with
;;; occur-check-q

(local
 (defun consistent-marking (x time g stamp indices)
   (if (endp indices)
       t
     (let ((i (car indices)))
       (if (= (nth i stamp) time)
	   (and (not (occur-check-d t x i g))
		(consistent-marking x time g stamp (cdr indices)))
	 (consistent-marking x time g stamp (cdr indices)))))))



(local
 (encapsulate
  ()

  (local
   (defthm member-indices-consistent-marking
     (implies (and (consistent-marking x time g stamp indices)
		   (member h indices)
		   (= (nth h stamp) time))
	      (not (occur-check-d t x h g)))))

  (local
   (defthm member-list-of-n
     (implies (natp n)
	      (iff (member x (list-of-n n))
		   (bounded-natp x n)))
     :hints (("Goal" :in-theory (enable list-of-n)))))

  (local
   (defthm consistent-marking-all-nodes
     (implies (and (bounded-natp h (len g))
		   (consistent-marking x time g stamp (list-of-n (len g)))
		   (= (nth h stamp) time))
	      (not (occur-check-d t x h g)))))

  (local
   (defthm consistent-marking-all-nodes-corollary
     (implies (and (bounded-natp h (len g))
		   (consistent-marking x time g stamp (list-of-n (len g)))
		   (= (nth h stamp) time)
		   (term-dag-non-variable-p h g))
	      (not (occur-check-d nil x (term-dag-args h g) g)))
     :hints (("Goal" :use consistent-marking-all-nodes
	      :in-theory (disable member-indices-consistent-marking
				  consistent-marking-all-nodes)))))

  (local
   (defthm consistent-marking-updated
     (implies (and (consistent-marking x time g stamp indices)
		   (nat-true-listp indices)
		   (natp h)
		   (not (occur-check-d t x h g)))
	      (consistent-marking x time g (update-nth h time stamp) indices))))

  (local
   (defthm nat-true-listp-list-of-n
     (implies (natp n)
	      (nat-true-listp (list-of-n n)))
     :hints (("Goal" :in-theory (enable list-of-n)))))

  (defthm occur-check-d-occur-check-q-main-lemma
    (implies (and (dag-p g)
		  (term-graph-p g)
		  (if flg
		      (bounded-natp h (len g))
		    (bounded-nat-true-listp h (len g)))
		  (consistent-marking
		   x time g stamp (list-of-n (len g))))
	     (and (equal (first (occur-check-q
				 flg x h g stamp time))
			 (occur-check-d flg x h g))
		  (consistent-marking
		   x time g
		   (second (occur-check-q flg x h g stamp time))
		   (list-of-n (len g))))))))


(local
 (encapsulate
  ()

  (local
   (defun all-marks-different-from-time (l time)
     (if (endp l)
	 t
       (and (not (equal (car l) time))
	    (all-marks-different-from-time (cdr l) time)))))

  (local
   (defthm all-marks-different-from-time-consistent-marking-lemma
     (implies (and (all-marks-different-from-time stamp time)
		   (natp i) (< i (len stamp)))
	      (not (equal (nth i stamp) time)))))

  (local
   (defthm all-marks-different-from-time-consistent-marking-lemma-2
     (implies (and (natp i)
		   (< i (len stamp)))
	      (not (all-marks-different-from-time stamp (nth i stamp))))))

  (local
   (defthm all-marks-different-from-time-consistent-marking
     (implies (and (all-marks-different-from-time stamp time)
		   (subsetp indices (list-of-n (len stamp))))
	      (consistent-marking x time g stamp indices))))

  (local
   (defthm marks-less-implies-marks-different
     (implies (all-marks-integers-less-than-time stamp time)
	      (all-marks-different-from-time stamp time))))

  (defthm occur-check-d-occur-check-q
    (implies (and (dag-p g)
		  (term-graph-p g)
		  (natp h) (< h (len g))
		  (equal (len g) (len stamp))
		  (all-marks-integers-less-than-time stamp time))
	     (equal (first (occur-check-q t x h g stamp time))
		    (occur-check-d t x h g))))))


;;; STEP III

;;; Under the invariant and well-formedness conditions the operator is
;;; legal and its application returns "the same" upl computed by
;;; dag-transform-mm-q

(local
 (encapsulate
  ()
  (local
   (defthm equations-already-solved-main-lemma-lemma
     (implies  (equations-already-solved
		args1 args2 g)
	       (equal (equal (dag-as-term nil args1 g)
			     (dag-as-term nil args2 g))
		      t))))

  (defthm equations-already-solved-main-lemma
    (implies (and
	      (term-dag-non-variable-p h1 g)
	      (term-dag-non-variable-p h2 g)
	      (equal (dag-symbol (dagi-l h1 g))
		     (dag-symbol (dagi-l h2 g)))
	      (equations-already-solved
	       (dag-args (dagi-l h1 g))
	       (dag-args (dagi-l h2 g))
	       g))
	     (equal (equal (dag-as-term t h1 g)
			   (dag-as-term t h2 g))
		    t))
    :hints (("Goal" :expand ((dag-as-term t h1 g)))))))

;;; We temporarily enable the following definitions

(local (in-theory (enable unif-legal-q
			  unif-reduce-one-step-q
			  unif-legal-d
			  unif-reduce-one-step-d)))


;;; Applicability of the witness operator:

(local
 (encapsulate
  ()

  (local
   (defthm identify-transform-mm-q-applies-a-legal-operator
     (implies (and
	       (unification-invariant-q ext-upl)
	       (not (normal-form-syst ext-upl))
	       (equal (first (first (first ext-upl))) 'id))
	      (unif-legal-q (ext-upl-to-upl ext-upl)
			    (list 'identify
				  (second (first (first ext-upl)))
				  (third (first (first ext-upl))))))))

  (local
   (defthm remove-ids-when-the-first-is-not-an-id
     (implies (not (equal (first (car ext-S)) 'id))
	      (and (iff (consp (remove-ids ext-S))
			(consp ext-S))
		   (equal (car (remove-ids ext-S))
			  (car ext-S))))))



  (defthm transform-mm-q-applies-a-legal-operator
    (implies (and (unification-invariant-q ext-upl)
		  (not (normal-form-syst ext-upl)))
	     (unif-legal-q (ext-upl-to-upl ext-upl)
			   (dag-transform-mm-q-op ext-upl))))))



;;; Application of the witness operator:

(local
 (defthm not-id-dag-deref-bounded-term-graph-p
   (implies (and (natp h)
		 (bounded-term-graph-p g n))
	    (not (equal (dag-deref h g) 'id)))))

(local
 (encapsulate
  ()



  (local
   (defthm remove-ids-append
     (equal (remove-ids (append ext-S1 ext-S2))
	    (append (remove-ids ext-S1) (remove-ids ext-S2)))))

  (local
   (defthm pair-args-remove-ids
     (implies (and (nat-true-listp l1)
		   (nat-true-listp l2))
	      (equal (remove-ids (car (pair-args l1 l2)))
		     (car (pair-args l1 l2))))))



  (defthm transform-mm-q-applies-an-operator
    (implies (and (well-formed-extended-upl ext-upl)
		  (ext-upl-occur-check-invariant ext-upl))
	     (equal (ext-upl-to-upl
		     (dag-transform-mm-q ext-upl))
		    (unif-reduce-one-step-q
		     (ext-upl-to-upl ext-upl)
		     (dag-transform-mm-q-op ext-upl)))))))

; Change by Matt K. for ACL2 2.9.3: the change to len-update-nth made the
; proof of len-third-dag-transform-mm-q fail, so we restore the old version.
(local (defthm len-update-nth-old
         (implies (< (nfix n) (len x))
                  (equal (len (update-nth n val x))
                         (len x)))))
(local (in-theory (disable len-update-nth)))

;;; The following lemma comes here because we need dag-transform-mm-q
;;; enabled
(local
 (defthm len-third-dag-transform-mm-q
   (implies (and (well-formed-extended-upl ext-upl)
		 (not (normal-form-syst ext-upl))
		 (dag-transform-mm-q ext-upl))
	    (equal (len (third (dag-transform-mm-q ext-upl)))
		   (len (third ext-upl))))))





;;; We disable again the following functions
(local (in-theory (disable
		   unif-legal-q
		   unif-reduce-one-step-q
		   unif-legal-d
		   unif-reduce-one-step-d)))

;;; This is no longer neccesary
(local
 (in-theory (disable dag-transform-mm-q-op)))


;;;============================================================================
;;;
;;; 4) Well-formedness conditions are an invariant of the computation proccess
;;;
;;;============================================================================

;;; Now we have to show that the conditions needed to ensure that the
;;; function dag-transform-mm-q computes a reduction step are an
;;; invariant during the whole unification proccess.

;;; This conditions are of four types:

;;; - Those concerning well-formedness, related to the fact that the
;;;   transformation step is applying an operator. These are
;;;   (bounded-nat-substitution-p (second ext-upl) n)
;;;   (bounded-well-formed-term-dag-p (third ext-upl) n))) (including
;;;   bounded-term-graph-p, dag-p and non-duplicated variables). In some
;;;   sense, we have proved these properties already.

;;; - The property about well-formedness of the extended system:
;;;   bounded-nat-pairs-true-listp-with-ids.

;;; - The hardest one: the property about the correct placement of the
;;;   identification marks in the extended system, ext-upl-id-invariant.

;;; - The invariant needed for the improved occur check.




;;; 4.0 Fist, some properties of ext-up-to-upl
;;; ------------------------------------------


(local
 (encapsulate
  ()

  (local
   (defthm ext-upl-to-upl-second-upl
     (equal (second (ext-upl-to-upl ext-upl))
	    (second ext-upl))))

  (local
   (defthm ext-upl-to-upl-third-upl
     (equal (third (ext-upl-to-upl ext-upl))
	    (third ext-upl))))

  (local
   (defthm remove-ids-bounded-nat-true-listp-lemma
     (implies (bounded-nat-pairs-true-listp-with-ids ext-s n)
	      (bounded-nat-pairs-true-listp (remove-ids ext-s) n))))

  (local
   (defthm remove-ids-bounded-nat-true-listp
     (implies (bounded-nat-pairs-true-listp-with-ids (first ext-upl) n)
	      (bounded-nat-pairs-true-listp (first (ext-upl-to-upl ext-upl)) n))))

  (defthm ext-upl-to-upl-well-formed-upl
    (implies (well-formed-extended-upl ext-upl)
	     (well-formed-upl (ext-upl-to-upl ext-upl)))
    :hints (("Goal" :in-theory (enable well-formed-upl-def))))))


;;; 4.1 Well-formedness properties of upls
;;; --------------------------------------

;;; In order to prove these properties, we can use the fact that the
;;; transformation step is equal (in some sense) to the application of
;;; an opertor. We have already proved (in the book
;;; dag-unification-rules) that these well-formedness properties are
;;; preserved by the application of these operators. So, we simply
;;; disable dag-transform-mm-q and use the already proved properties.

(local
 (in-theory
  (disable dag-transform-mm-q)))

(local
 (encapsulate
  ()

  (local
   (defthm transform-mm-q-preserves-well-formed-upl-ext-upl-to-upl
     (implies (and (unification-invariant-q ext-upl)
		   (not (normal-form-syst ext-upl)))
	      (well-formed-upl
	       (ext-upl-to-upl (dag-transform-mm-q ext-upl))))
     :hints (("Goal"
	      :in-theory (disable ext-upl-to-upl
				  well-formed-upl-def
				  well-formed-extended-upl-def)
	      :use
	      (:instance unif-reduce-one-step-q-preserves-well-formed-upl
			 (upl (ext-upl-to-upl ext-upl))
			 (op (dag-transform-mm-q-op ext-upl)))))))


;;; This entails the two lemmas we want to prove:

  (local (in-theory (disable transform-mm-q-applies-an-operator)))
  (local (in-theory (enable well-formed-upl-def)))


  (defthm transform-mm-q-preserves-bounded-nat-substitution-p
    (implies (and (unification-invariant-q ext-upl)
		  (not (normal-form-syst ext-upl)))
	     (bounded-nat-substitution-p
	      (second (dag-transform-mm-q ext-upl))
	      (len (third (dag-transform-mm-q ext-upl)))))
    :hints (("Goal"
	     :use
	     transform-mm-q-preserves-well-formed-upl-ext-upl-to-upl)))


  (defthm transform-mm-q-preserves-well-formed-term-dag-p
    (implies (and (unification-invariant-q ext-upl)
		  (not (normal-form-syst ext-upl)))
	     (bounded-well-formed-term-dag-p
	      (third (dag-transform-mm-q ext-upl))
	      (len (third (dag-transform-mm-q ext-upl)))))
    :hints (("Goal"
	     :use
	     transform-mm-q-preserves-well-formed-upl-ext-upl-to-upl)))))


;;; We now enable dag-transform-mm-q, since from now on, the theorems we
;;; want to prove has to be deduced directly from its definition


(local (in-theory (enable dag-transform-mm-q)))



;;; 4.2 Well-formedness properties of extended systems
;;; --------------------------------------------------


(local
 (encapsulate
  ()

  (local
   (defthm not-consp-dag-deref-bounded-term-graph-p
     (implies (and (natp h)
		   (bounded-term-graph-p g n)
		   (dag-p g))
	      (not (consp (dag-deref h g))))
     :rule-classes :type-prescription))

   (local
    (defthm bounded-nat-pairs-true-listp-with-ids-append
      (implies (true-listp l1)
	       (iff (bounded-nat-pairs-true-listp-with-ids (append l1 l2) n)
		    (and (bounded-nat-pairs-true-listp-with-ids l1 n)
			 (bounded-nat-pairs-true-listp-with-ids l2 n))))))


;;; Repetido (esta en dag-unification-rules-bis.lisp)
   (local
    (defthm bounded-nat-listp-pair-args
      (implies (and (bounded-nat-listp l1 m) (bounded-nat-listp l2 m))
	       (bounded-nat-pairs-true-listp (car (pair-args l1 l2)) m))))

   (local
    (defthm
      bounded-nat-pairs-true-listp-with-ids-bounded-nat-pairs-true-listp
      (implies (bounded-nat-pairs-true-listp l n)
	       (bounded-nat-pairs-true-listp-with-ids l n))))



   (defthm transform-mm-q-preserves-bounded-nat-pairs-true-listp-with-ids
     (implies (and (not (normal-form-syst ext-upl))
		   (well-formed-extended-upl ext-upl))
	      (bounded-nat-pairs-true-listp-with-ids
	       (first (dag-transform-mm-q ext-upl))
	       (len (third (dag-transform-mm-q ext-upl))))))))


;;; Now we can prove that well-formed-extended-upl is preserevd in each
;;; transformation step given by dag-transform-mm-q:


(defthm transform-mm-q-preserves-well-formed-extended-upl
  (implies (and (unification-invariant-q ext-upl)
		(not (normal-form-syst ext-upl)))
	   (well-formed-extended-upl
	    (dag-transform-mm-q ext-upl)))
  :hints (("Goal" :in-theory (disable dag-transform-mm-q
				      ext-upl-id-invariant
				      bounded-well-formed-term-dag-p))))



;; And now the hardest part:

;;; 4.3 ext-upl-id-invariant is preserved by dag-transform-mm-q
;;; -----------------------------------------------------------

;;; The main theorem we want to prove in this subsection is
;;; transform-mm-q-preserves-ext-upl-id-invariant above. The proof of
;;; this theorem is a very long case distinction, according to the
;;; definition of dag-transform-mm-q and the diferent properties
;;; embodied by ext-upl-id-invariant. In the comments below, we wil
;;; specify (roughly) which for which subgoals are needed the previous
;;; lemmas poved

;;; Lemmas used by several Subgoals:

(local
 (defthm consp-until-first-id
   (iff (consp (until-first-id l))
	(consp l))))


(local
 (defthm second-pair-args-revlist
   (implies (second (pair-args l1 l2))
	    (second (pair-args (revlist l1) (revlist l2))))))


(local
 (defun nat-pairs-true-listp (l)
   (if (atom l)
       (equal l nil)
     (and (consp (car l))
	  (natp (caar l))
	  (natp (cdar l))
	  (nat-pairs-true-listp (cdr l))))))


(local
 (defthm nat-true-listp-true-listp
   (implies (nat-true-listp l) (true-listp l))))

(local
 (defthm nat-true-listp-nat-pairs-true-listp-pair-args
   (implies (and (nat-true-listp l1)
		 (nat-true-listp l2))
	    (nat-pairs-true-listp (first (pair-args l1 l2))))))


(local
 (defthm pair-args-append
   (implies
    (and (true-listp l1) (true-listp l2)
	 (true-listp l3) (true-listp l4)
	 (second (pair-args l1 l2))
	 (second (pair-args l3 l4)))
    (and
     (second (pair-args (append l1 l3) (append l2 l4)))
     (equal (first (pair-args (append l1 l3) (append l2 l4)))
	    (append (first (pair-args l1 l2)) (first (pair-args l3
								l4))))))))

(local
 (defthm first-pair-args-revlist
   (implies (second (pair-args l1 l2))
	    (equal (revlist (first (pair-args l1 l2)))
		   (first (pair-args (revlist l1) (revlist l2)))))))

(local
 (defthm consp-pair-args
   (implies (second (pair-args l1 l2))
	    (iff (consp (first (pair-args l1 l2)))
		 (and (consp l1) (consp l2))))))

(local
 (defthm consp-cdr-append-list
   (iff (consp (cdr (append l (list x))))
	(consp l))))

(local
 (defthm car-append
   (implies (consp l1)
	    (equal (car (append l1 l2))
		   (car l1)))))




;;; Lemmas used by Subgoal 20:


(local
 (defthm until-first-id-nat-pairs-true-listp
   (implies (nat-pairs-true-listp S)
	    (equal (until-first-id
		    (append S (list (list 'id i1 i2))))
		   (append S (list (list 'id i1 i2)))))))

(local
 (defthm after-first-id-nat-pairs-true-listp
   (implies (nat-pairs-true-listp S)
	    (equal (after-first-id
		    (append S (list (list 'id i1 i2))))
		   nil))))


(local
 (defthm first-id-stack-invariant-aux-with-equations-simple-case
   (implies (and (consp l1) (second (pair-args l1 l2)))
	    (first-id-stack-invariant-aux-with-equations
	     l1 l2
	     (first (pair-args l1 l2)) g))))



;;; Lemmas used by Subgoal 15:

;;; Note the rewrite rule, maybe not the most natural formulation of the
;;; lemma, but in this way we avoid problems with th free variable.

(local
 (defthm first-id-stack-invariant-aux-with-equations-delete-rule
   (implies
    (and (consp eqs)
	 (not (first-id-stack-invariant-aux-with-equations
	       l1 l2 eqs g))
	 (equal (dag-deref h1 g) (dag-deref h2 g)))

    (not (first-id-stack-invariant-aux-with-equations
	  l1 l2 (append eqs (list (cons h1 h2))) g)))
   :hints (("Goal" :induct
	    (first-id-stack-invariant-aux-with-equations
	     l1 l2 eqs g)))))


;;; Lemmas used by 15.2:


(local
 (defthm equations-already-solved-revlist
   (implies (and (true-listp l1)(true-listp l2))
	    (iff
	     (equations-already-solved (revlist l1) (revlist l2) g)
	     (equations-already-solved l1 l2 g)))))


(local
 (encapsulate
  ()
  (local
   (defthm equations-already-solved-delete-rule
     (implies
      (and
       (consp l1) (consp l2)
       (equations-already-solved (cdr l1) (cdr l2) g)
       (equal (dag-deref (car l1) g) (dag-deref (car l2) g)))
      (equations-already-solved l1 l2 g))
     :rule-classes nil))

  (defthm equations-already-solved-delete-rule-corollary
    (implies
     (and
      (consp l1) (consp l2) (true-listp l1) (true-listp l2)
      (not (equations-already-solved l1 l2 g))
      (equations-already-solved (cdr (revlist l1)) (cdr (revlist l2)) g))
     (not (equal (dag-deref (car (revlist l1)) g) (dag-deref (car (revlist
								   l2))
							     g))))
    :hints (("Goal" :use (equations-already-solved-revlist
			  (:instance
			   equations-already-solved-delete-rule
			   (l1 (revlist l1)) (l2 (revlist l2)))))))))




;;; Lemmas used by Subgoal 14

(local
 (encapsulate
  ()
  (local
   (defun induct-first-id-stack-invariant-orient-rule
     (l1 l2 eqs)
     (if (endp eqs)
	 (list l1 l2 eqs)
       (induct-first-id-stack-invariant-orient-rule
	(cdr l1) (cdr l2) (cdr eqs)))))

  (defthm first-id-stack-invariant-orient-rule
    (implies
     (and
      (dag-p g)
      (not (term-dag-variable-p (dag-deref h1 g) g))
      (term-dag-variable-p (dag-deref h2 g) g)
      (first-id-stack-invariant-aux-with-equations
       l1 l2 (append eqs (list (cons h1 h2))) g))
     (first-id-stack-invariant-aux-with-equations
      l1 l2 (append eqs (list (cons (dag-deref h2 g)
				    (dag-deref h1 g)))) g))
    :hints (("Goal" :induct
	     (induct-first-id-stack-invariant-orient-rule l1 l2 eqs))))


  (defthm first-id-stack-invariant-orient-rule-corollary
    (implies
     (and
      (dag-p g)
      (consp eqs)
      (not (term-dag-variable-p (dag-deref h1 g) g))
      (term-dag-variable-p (dag-deref h2 g) g)
      (first-id-stack-invariant-aux-with-equations
       l1 l2 (cdr (append eqs (list (cons h1 h2)))) g))
     (first-id-stack-invariant-aux-with-equations
      l1 l2 (cdr (append eqs (list (cons (dag-deref h2 g)
					 (dag-deref h1 g))))) g))
    :hints (("Goal" :use
	     ((:instance first-id-stack-invariant-orient-rule
			 (eqs (cdr eqs)))))))))


;;; Lemmas used by Subgoal 12

(local
 (defthm until-first-id-nat-pairs-true-listp-2
   (implies (nat-pairs-true-listp S)
	    (equal (until-first-id
		    (append S (cons (list 'id i1 i2) rest)))
		   (append S (list (list 'id i1 i2)))))))

(local
 (defthm after-first-id-nat-pairs-true-listp-2
   (implies (nat-pairs-true-listp S)
	    (equal (after-first-id
		    (append S (cons (list 'id i1 i2) rest)))
		   rest))))

(local
 (defthm remaining-id-stacks-invariant-aux-decompose-rule
   (implies
    (and (dag-p g)
	 (not (term-dag-variable-p h1 g))
	 (first-id-stack-invariant-aux-with-equations
	  l1 l2 (append eqs (list (cons h1 h2))) g))
    (remaining-id-stacks-invariant-aux
     l1 l2 eqs (list 'id (dag-deref h1 g) (dag-deref h2 g)) g))
   :hints (("Goal" :induct
	    (remaining-id-stacks-invariant-aux
	     l1 l2 eqs (list 'id (dag-deref h1 g)
			     (dag-deref h2 g)) g)
	    :in-theory (disable dag-deref)))))

(local
 (encapsulate
  ()
  (local
   (defthm term-dag-variable-p-dag-deref
     (implies (and (dag-p g) (not (term-dag-variable-p (dag-deref h g) g)))
	      (not (term-dag-variable-p h g)))))

 (defthm remaining-id-stacks-invariant-aux-decompose-rule-corollary
   (implies
    (and (dag-p g)
	 (not (term-dag-variable-p (dag-deref h1 g) g))
	 (first-id-stack-invariant-aux-with-equations
	  l1 l2 (append eqs (list (cons h1 h2))) g))
    (remaining-id-stacks-invariant-aux
     l1 l2 eqs (list 'id (dag-deref h1 g) (dag-deref h2 g)) g)))))


;;; Lemmas used by Subgoal 9


(local
 (defthm updating-eliminate-rule-does-not-affect-nth
   (implies (and
	     (term-dag-variable-p h1 g)
	     (not (term-dag-variable-p h2 g)))
	    (equal (nth h2 (update-nth h1 i g))
		   (nth h2 g)))))

(local
 (defthm equations-already-solved-eliminate-rule
   (implies (and (bounded-term-graph-p g n)
		 (nat-true-listp l1)
		 (nat-true-listp l2)
		 (dag-p g)
		 (no-duplicatesp (list-of-term-dag-variables g))
		 (not (occur-check-d t x h0 g))
		 (natp x) (natp h0)
		 (term-dag-variable-p x g)
		 (equations-already-solved l1 l2 g))
	    (equations-already-solved l1 l2 (update-nth x h0 g)))))



(local
 (defthm dag-deref-when-updating-variables-nodes
   (implies (and
	     (dag-p g)
	     (bounded-term-graph-p g n)
	     (natp x) (natp h0)
	     (not (occur-check-d t x h0 g))
	     (term-dag-variable-p x g)
	     (not (term-dag-variable-p (dag-deref h g) g)))
	    (equal (dag-deref h (update-nth x h0 g))
		   (dag-deref h g)))))

(local
 (defthm remaining-id-stacks-invariant-aux-preserved-eliminate-rule
   (implies (and (bounded-term-graph-p g n)
		 (nat-true-listp rargs1)
		 (nat-true-listp rargs2)
		 (dag-p g)
		 (no-duplicatesp (list-of-term-dag-variables g))
		 (not (occur-check-d t h1 h2 g))
		 (natp h1) (natp h2)
		 (term-dag-variable-p h1 g)
		 (not (term-dag-variable-p (second id-equ) g))
		 (not (term-dag-variable-p (third id-equ) g))
		 (remaining-id-stacks-invariant-aux
		  rargs1 rargs2 eqs id-equ g))
	    (remaining-id-stacks-invariant-aux
	     rargs1 rargs2 eqs id-equ (update-nth h1 h2 g)))))

(local
 (defthm nat-true-listp-revlist
   (implies (nat-true-listp l)
	    (nat-true-listp (revlist l)))))


(local
 (defthm bounded-nat-true-listp-revlist
   (implies (bounded-nat-true-listp l n)
	    (bounded-nat-true-listp (revlist l) n))))

(local
 (defthm iter-remaining-id-stacks-invariant-preserved-eliminate-rule
   (implies
    (and
     (bounded-term-graph-p g n)
     (dag-p g)
     (no-duplicatesp (list-of-term-dag-variables g))
     (not (occur-check-d t h1 h2 g))
     (natp h1) (natp h2)
     (term-dag-variable-p h1 g)
     (not (term-dag-variable-p (second id-equ) g))
     (not (term-dag-variable-p (third id-equ) g))
     (iter-remaining-id-stacks-invariant
      id-equ id-stacks g))
    (iter-remaining-id-stacks-invariant
     id-equ id-stacks (update-nth h1 h2 g)))))



(local
 (defthm eliminate-rule-lemma-1
   (implies (and (dag-p g)
		 (term-dag-variable-p (dag-deref h g) g))
	    (equal (dag-as-term t h g) (term-dag-symbol (dag-deref h g) g)))))
(local
 (encapsulate
  ()
  (local
   (defthm eliminate-rule-lemma-2
     (implies (and (dag-p g)
		   (no-duplicatesp (list-of-term-dag-variables g))
		   (bounded-term-graph-p g n)
		   (term-dag-variable-p h1 g)
		   (not (occur-check-d t h1 h2 g))
		   (natp h1) (natp h2))
	      (equal (instance (dag-as-term t h2 g)
			       (list (cons (term-dag-symbol h1 g) term)))
		     (dag-as-term t h2 g)))
     :hints (("Goal" :in-theory (enable occur-check-p-occur-check-d)
	      :use ((:instance substitution-does-not-change-term
			       (sigma (list (cons (term-dag-symbol h1 g)
						  term)))
			       (flg t) (term (dag-as-term t h2 g))))))
     :rule-classes nil))


  (defthm eliminate-rule-lemma-2-corollary
    (implies (and (dag-p g)
		  (no-duplicatesp (list-of-term-dag-variables g))
		  (bounded-term-graph-p g n)
		  (term-dag-variable-p (dag-deref h1 g) g)
		  (not (occur-check-d t (dag-deref h1 g)
				      (dag-deref h2 g) g))
		  (natp h1) (natp h2))
	     (equal (instance (dag-as-term t h2 g)
			      (list (cons (term-dag-symbol (dag-deref h1 g) g) term)))
		    (dag-as-term t (dag-deref h2 g) g)))
    :hints (("Goal" :use
	     ((:instance eliminate-rule-lemma-2
			 (h1 (dag-deref h1 g)) (h2 (dag-deref h2 g))))
	     :in-theory (enable dag-as-term-dag-deref))))))




(local
 (encapsulate
  ()
  (local
   (defthm equations-already-solved-eliminate-rule-last-equation-of-the-stack-main-lemma
     (implies
      (and
       (bounded-term-graph-p g n)
       (dag-p g)
       (no-duplicatesp (list-of-term-dag-variables g))
       (nat-true-listp l1) (consp l1)
       (nat-true-listp l2) (consp l2)
       (not (occur-check-d t (dag-deref (car l1) g) (dag-deref (car l2) g) g))
       (term-dag-variable-p (dag-deref (car l1) g)  g)
       (equations-already-solved
	(cdr l1) (cdr l2) g))
      (equations-already-solved
       l1 l2
       (update-nth (dag-deref (car l1) g)
		   (dag-deref (car l2) g) g)))
     :rule-classes nil))


  (defthm
    equations-already-solved-eliminate-rule-last-equation-of-the-stack
    (implies
     (and
      (term-graph-p g)
      (dag-p g)
      (no-duplicatesp (list-of-term-dag-variables g))
      (nat-true-listp l1) (consp l1)
      (nat-true-listp l2) (consp l2)
      (not (occur-check-d t (dag-deref (car (revlist l1)) g) (dag-deref
							      (car
							       (revlist l2)) g) g))
      (term-dag-variable-p (dag-deref (car (revlist l1)) g)  g)
      (equations-already-solved
       (cdr (revlist l1)) (cdr (revlist l2)) g))
     (equations-already-solved
      l1 l2
      (update-nth (dag-deref (car (revlist l1)) g)
		  (dag-deref (car (revlist l2)) g) g)))
    :hints (("Goal" :use
	     (:instance
	      equations-already-solved-eliminate-rule-last-equation-of-the-stack-main-lemma
	      (l1 (revlist l1)) (l2 (revlist l2)) (n (len g))))))))

(local
 (defthm equations-already-solved-symmetric
   (iff (equations-already-solved l1 l2 g)
	(equations-already-solved l2 l1 g))))

(local
 (defthm
   equations-already-solved-eliminate-rule-last-equation-of-the-stack-symetric
   (implies
    (and
     (term-graph-p g)
     (dag-p g)
     (no-duplicatesp (list-of-term-dag-variables g))
     (nat-true-listp l1) (consp l1)
     (nat-true-listp l2) (consp l2)
     (not (occur-check-d t (dag-deref (car (revlist l2)) g) (dag-deref
							     (car
							      (revlist l1)) g) g))
     (term-dag-variable-p (dag-deref (car (revlist l2)) g)  g)
     (equations-already-solved
      (cdr (revlist l1)) (cdr (revlist l2)) g))
    (equations-already-solved
     l1 l2
     (update-nth (dag-deref (car (revlist l2)) g)
		 (dag-deref (car (revlist l1)) g) g)))
   :hints (("Goal" :use
	    (:instance
	     equations-already-solved-eliminate-rule-last-equation-of-the-stack
	     (l1 l2) (l2 l1))
	    :in-theory (disable equations-already-solved-eliminate-rule-last-equation-of-the-stack)))))

(local (in-theory (disable equations-already-solved-symmetric)))


;;; Lemmas used by Subgoal 9

(local
 (defthm first-id-stack-invariant-aux-with-equations-eliminate-rule
   (implies (and
	     (dag-p g)
	     (no-duplicatesp (list-of-term-dag-variables g))
	     (bounded-term-graph-p g n)
	     (consp eqs)
	     (term-dag-variable-p (dag-deref h1 g) g)
	     (not (occur-check-d t
				 (dag-deref h1 g)
				 (dag-deref h2 g) g))
	     (natp h1) (natp h2)
	     (nat-true-listp l1)
	     (nat-true-listp l2)
	     (first-id-stack-invariant-aux-with-equations
	      l1 l2 (append eqs (list (cons h1 h2))) g))
	    (first-id-stack-invariant-aux-with-equations
	     l1 l2 eqs (update-nth (dag-deref h1 g)
				   (dag-deref h2 g) g)))
   :hints (("Goal"
	    :in-theory (disable nth-update-nth) ;;; Este disable quita
					;;; muchisimos casos
	    :induct
	    (first-id-stack-invariant-aux-with-equations
	     l1 l2 eqs g)))))



;;; Lemmas used by Subgoal 8

;;; This subgoal is the most difficult part. It deals with the
;;; preservation of iter-remaining-id-stacks-invariant by the
;;; Elimination rule (that is, by updates of the graph). In particular,
;;; our goal is to prove lemma
;;; iter-remaining-id-stacks-invariant-preserved-by-identification
;;; below. Very hard....



(local
 (defthm ids-implies-consp-split-extended-system-in-id-stacks
   (implies (equal (first (car (revlist (until-first-id ext-s))))
		   'id)
	    (consp (split-extended-system-in-id-stacks ext-s)))))

(local
 (defthm consp-split-extended-system-in-id-stacks
   (implies (consp (split-extended-system-in-id-stacks ext-S))
	    (equal
	     (first
	      (car (last (until-first-id ext-S))))
	     'id))))



;;; The function remaining-id-stacks-invariant-path builds a path in the
;;; dag, obtained from the extended indices system of equations.

(local
 (defun dag-deref-path (h g)
   (declare (xargs :measure (measure-rec-dag t h g)))
   (if (dag-p g)
       (let ((p (dagi-l h g)))
	 (if (integerp p)
	     (cons h (dag-deref-path p g))
	   (list h)))
     'undef)))


(local
 (defun remaining-id-stacks-invariant-path
   (id rargs requations g)
   (if (endp requations)
       (cons id (dag-deref-path (car rargs) g))
     (remaining-id-stacks-invariant-path
      id (cdr rargs) (cdr requations) g))))


;;; With the function above we can build two paths, from the components
;;; of remaining-id-stacks-invariant

;;; Before disabling it, let us see the main properties of this
;;; function.


;;; First, two properties of dag-deref.

(local
 (defthm consp-first-and-last-of-dag-deref-path
   (implies (dag-p g)
	    (let ((d-d-path (dag-deref-path h g)))
	      (and (consp d-d-path)
		   (true-listp d-d-path)
		   (equal (car d-d-path) h)
		   (equal (car (last d-d-path)) (dag-deref h g)))))))

(local
 (defthm path-p-dag-deref-path
   (implies (and (bounded-term-graph-p g n)
		 (dag-p g)
		 (natp h))
	    (path-p (dag-deref-path h g) g))))
;;; -------

(local
 (defthm member-map-nfix-natp
   (implies (nat-true-listp l)
	    (equal (map-nfix l) l))))

;;; Given the components of a remaining-id-stacks-invaraint-aux, two
;;; paths in the graph can be built, as the following results stablish.

(local
 (defthm remaining-id-stacks-invariant-path-path-p-main-lemma-lhs
   (implies (and
	     (remaining-id-stacks-invariant-aux
	      rargs1 rargs2 requations id-equ g)
	     (dag-p g)
	     (bounded-term-graph-p g n)
	     (natp id-lhs)
	     (nat-true-listp rargs1) ;;; esto es redundante pero ayuda
	     (term-dag-non-variable-p id-lhs g)
	     (subsetp rargs1 (term-dag-args id-lhs g)))
	    (path-p (remaining-id-stacks-invariant-path
		     id-lhs rargs1 requations g) g))))


(local
 (defthm remaining-id-stacks-invariant-path-path-p-main-lemma-rhs
   (implies (and
	     (remaining-id-stacks-invariant-aux
	      rargs1 rargs2 requations id-equ g)
	     (dag-p g)
	     (bounded-term-graph-p g n)
	     (natp id-rhs)
	     (nat-true-listp rargs2) ;;; esto es redundante pero ayuda
	     (term-dag-non-variable-p id-rhs g)
	     (subsetp rargs2 (term-dag-args id-rhs g)))
	    (path-p (remaining-id-stacks-invariant-path
		     id-rhs rargs2 requations g) g))))



;;  It is a true-listp

(local
 (defthm remaining-id-stacks-invariant-path-true-listp
   (implies (dag-p g)
	    (true-listp (remaining-id-stacks-invariant-path
			 id rargs requations g)))))



;;; With at least two elements

(local
 (defthm remaining-id-stacks-invariant-path-at-least-two-elements
   (implies (dag-p g)
	    (> (len (remaining-id-stacks-invariant-path
		     id rargs requations g))
	       1))
   :rule-classes :linear))



;;; The first of this elements is the first argument
(local
 (defthm remaining-id-stacks-invariant-path-first-element
   (implies (dag-p g)
	    (equal (car (remaining-id-stacks-invariant-path
			 id rargs requations g))
		   id))))

;;; The last one depends on wether we take the left path or the right
;;; path:

(local
 (defthm remaining-id-stacks-invariant-path-last-element-lhs
   (implies (and (dag-p g)
		 (remaining-id-stacks-invariant-aux
		  rargs1 rargs2 requations id-equ g))
	    (equal (car (last (remaining-id-stacks-invariant-path
			       id-lhs rargs1 requations g)))
		   (second id-equ)))))


(local
 (defthm remaining-id-stacks-invariant-path-last-element-rhs
   (implies (and (dag-p g)
		 (remaining-id-stacks-invariant-aux
		  rargs1 rargs2 requations id-equ g))
	    (equal (car (last (remaining-id-stacks-invariant-path
			       id-rhs rargs2 requations g)))
		   (third id-equ)))))

;;; Now we disable remaining-id-stacks-invariant-path
(local (in-theory (disable remaining-id-stacks-invariant-path)))

;;; And we use this function to build two paths from the arguments of a
;;; remaining-id-stacks-invariant

(local
 (defun remaining-id-stacks-invariant-path-lhs
   (id-equ requations next-id-equ g)
   (declare (ignore id-equ))
   (let ((id1 (second next-id-equ)))
     (remaining-id-stacks-invariant-path
      id1 (revlist (term-dag-args id1 g)) requations g))))


(local
 (defun remaining-id-stacks-invariant-path-rhs
   (id-equ requations next-id-equ g)
   (declare (ignore id-equ))
   (let ((id2 (third next-id-equ)))
     (remaining-id-stacks-invariant-path
      id2 (revlist (term-dag-args id2 g)) requations g))))

;;; And now we prove the main properties of these functions. That is,
;;; under the hypothesis remaining-id-stacks-invariant, the following
;;; holds fro both paths:
;;;     - They are paths in the graph g
;;;     - True listps
;;;     - With length bigger than 1
;;;     - Its first element is the second element of next-id-equ (for
;;;     lhs) y and the third of next-id-equ (for rhs), respectively
;;;     - Its last last element is the second of id-equ (for lhs) or the
;;;     third of id-equ (for lhs).

(local
 (defthm subsetp-revlist
   (subsetp (revlist l) l)))

;;; Paths
(local
 (defthm remaining-id-stacks-invariant-path-lhs-path-p
   (implies (and (term-graph-p g)
		 (dag-p g)
		 (remaining-id-stacks-invariant
		  id-equ requations next-id-equ g))
	    (path-p
	     (remaining-id-stacks-invariant-path-lhs
	      id-equ requations next-id-equ g) g))))

(local
 (defthm remaining-id-stacks-invariant-path-rhs-path-p
   (implies (and (term-graph-p g)
		 (dag-p g)
		 (remaining-id-stacks-invariant
		  id-equ requations next-id-equ g))
	    (path-p
	     (remaining-id-stacks-invariant-path-rhs
	      id-equ requations next-id-equ g) g))))

;;; True lists p

(local
 (defthm remaining-id-stacks-invariant-path-lhs-true-listp
   (implies (dag-p g)
	    (true-listp
	     (remaining-id-stacks-invariant-path-lhs
	      id-equ requations next-id-equ g)))))

(local
 (defthm remaining-id-stacks-invariant-path-rhs-true-listp
   (implies (dag-p g)
	    (true-listp
	     (remaining-id-stacks-invariant-path-rhs
	      id-equ requations next-id-equ g)))))



;;; Length >1


(local
 (defthm remaining-id-stacks-invariant-path-lhs-at-least-two-elements
   (implies (dag-p g)
	    (> (len
		(remaining-id-stacks-invariant-path-lhs
		 id-equ requations next-id-equ g))
	       1))
   :rule-classes :linear))


(local
 (defthm remaining-id-stacks-invariant-path-rhs-at-least-two-elements
   (implies (dag-p g)
	    (> (len
		(remaining-id-stacks-invariant-path-rhs
		 id-equ requations next-id-equ g))
	       1))
   :rule-classes :linear))


;;; Firts element of these paths

(local
 (defthm remaining-id-stacks-invariant-path-lhs-first-element
   (implies (dag-p g)
	    (equal(first
		   (remaining-id-stacks-invariant-path-lhs
		    id-equ requations next-id-equ g))
		  (second next-id-equ)))))



(local
 (defthm remaining-id-stacks-invariant-path-rhs-first-element
   (implies (dag-p g)
	    (equal(first
		   (remaining-id-stacks-invariant-path-rhs
		    id-equ requations next-id-equ g))
		  (third next-id-equ)))))

;;; The last element of these paths:

(local
 (defthm remaining-id-stacks-invariant-path-lhs-last-element
   (implies (and (dag-p g)
		 (remaining-id-stacks-invariant
		  id-equ requations next-id-equ g))
	    (equal (car
		    (last
		     (remaining-id-stacks-invariant-path-lhs
		      id-equ requations next-id-equ g)))
		   (second id-equ)))))


(local
 (defthm remaining-id-stacks-invariant-path-rhs-last-element
   (implies (and (dag-p g)
		 (remaining-id-stacks-invariant
		  id-equ requations next-id-equ g))
	    (equal (car
		    (last
		     (remaining-id-stacks-invariant-path-rhs
		      id-equ requations next-id-equ g)))
		   (third id-equ)))))


;;; Now, the main properties are proved (I hope). So we disable:
(local (in-theory (disable remaining-id-stacks-invariant-path-lhs
		    remaining-id-stacks-invariant-path-rhs)))


;;; No we define two other functions, similar to the previously defined,
;;; but starting in a already given path. This will be used to prove
;;; that, when doing an identification,
;;; iter-remaining-id-stacks-invariant  is preserved.


(local
 (defun remaining-id-stacks-invariant-path-append-lhs
   (p id-equ requations next-id-equ g)
   (append (remaining-id-stacks-invariant-path-lhs
	    id-equ requations next-id-equ g)
	   (cdr p))))


(local
 (defun remaining-id-stacks-invariant-path-append-rhs
   (p id-equ requations next-id-equ g)
   (append (remaining-id-stacks-invariant-path-rhs
	    id-equ requations next-id-equ g)
	   (cdr p))))

;;; For these two functions, we prove the same properties than before.

;;; Paths:

(local
 (encapsulate
  ()

  (local
   (defthm path-p-true-listp
     (implies (path-p p g)
	      (true-listp p))))

  (local
   (defthm path-p-append-cdr
     (implies (and (path-p p1 g)
		   (path-p p2 g)
		   (equal (car (last p1))
			  (car p2)))
	      (path-p (append p1 (cdr p2)) g))
     :hints (("Goal" :in-theory (enable path-p-append)))))


  (defthm remaining-id-stacks-invariant-path-append-lhs-path-p
    (implies (and (term-graph-p g)
		  (dag-p g)
		  (remaining-id-stacks-invariant
		   id-equ requations next-id-equ g)
		  (path-p p g)
		  (equal (car p) (second id-equ)))
	     (path-p
	      (remaining-id-stacks-invariant-path-append-lhs
	       p id-equ requations next-id-equ g) g)))


  (defthm remaining-id-stacks-invariant-path-append-rhs-path-p
    (implies (and (term-graph-p g)
		  (dag-p g)
		  (remaining-id-stacks-invariant
		   id-equ requations next-id-equ g)
		  (path-p p g)
		  (equal (car p) (third id-equ)))
	     (path-p
	      (remaining-id-stacks-invariant-path-append-rhs
	       p id-equ requations next-id-equ g) g)))))


;;; Length > 1

(local
 (encapsulate
  ()

  (local
   (defthm len-append
     (equal (len (append p1 p2))
	    (+ (len p1) (len p2)))))


  (defthm remaining-id-stacks-invariant-path-append-lhs-at-least-two-elements
    (implies (dag-p g)
	     (> (len
		 (remaining-id-stacks-invariant-path-append-lhs
		  p id-equ requations next-id-equ g))
		1))
    :rule-classes :linear)


  (defthm remaining-id-stacks-invariant-path-append-rhs-at-least-two-elements
    (implies (dag-p g)
	     (> (len
		 (remaining-id-stacks-invariant-path-append-rhs
		  p id-equ requations next-id-equ g))
		1))
    :rule-classes :linear)))


;;; The first element:


(local
 (defthm remaining-id-stacks-invariant-path-append-lhs-first-element
   (implies (dag-p g)
	    (equal
	     (car (remaining-id-stacks-invariant-path-append-lhs
		   p id-equ requations next-id-equ g))
	     (second next-id-equ)))))


(local
 (defthm remaining-id-stacks-invariant-path-append-rhs-first-element
   (implies (dag-p g)
	    (equal
	     (car (remaining-id-stacks-invariant-path-append-rhs
		   p id-equ requations next-id-equ g))
	     (third next-id-equ)))))



;;; The last element

(local
 (encapsulate
  ()
  (local
   (defthm car-last-append-not-consp
     (implies (not (consp l))
	      (equal (car (last (append m l)))
		     (car (last m))))))

  (defthm remaining-id-stacks-invariant-path-append-lhs-last-element
    (implies (and (dag-p g)
		  (remaining-id-stacks-invariant
		   id-equ requations next-id-equ g)
		  (consp p)
		  (equal (car p) (second id-equ)))
	     (equal (car
		     (last
		      (remaining-id-stacks-invariant-path-append-lhs
		       p id-equ requations next-id-equ g)))
		    (car (last p)))))


  (defthm remaining-id-stacks-invariant-path-append-rhs-last-element
    (implies (and (dag-p g)
		  (remaining-id-stacks-invariant
		   id-equ requations next-id-equ g)
		  (consp p)
		  (equal (car p) (third id-equ)))
	     (equal (car
		     (last
		      (remaining-id-stacks-invariant-path-append-rhs
		       p id-equ requations next-id-equ g)))
		    (car (last p)))))))


;;; And now we disable the function:

(local (in-theory (disable remaining-id-stacks-invariant-path-append-lhs
		    remaining-id-stacks-invariant-path-append-rhs)))





;;; Now, with this, we can prove that the left hand side is not equal to
;;; the updated:


;;; Reason one for proving thta two nodes are not equal: exists a
;;; path from one to the other, and the graph is acyclic.

(local
 (encapsulate
  ()
  (local
   (defthm member-car-last
     (implies (consp l)
	      (member (car (last l)) l))))


  (defthm no-duplicatesp-dag-p
    (implies (and (dag-p g)
		  (path-p p g)
		  (> (len p) 1))
	     (not (equal (car (last p)) (car p))))
    :hints (("Goal" :use dag-p-completeness)))))



(local
 (defthm remaining-id-stacks-invariant-nth-update-nth-lhs
   (let ((next-id-equ (car (revlist id-stack)))
	 (requations (cdr (revlist id-stack))))
     (implies (and (term-graph-p g)
		   (dag-p g)
		   (remaining-id-stacks-invariant
		    id-equ requations next-id-equ g)
		   (natp (second id-equ)))
	      (equal (nth (second next-id-equ) (update-nth (second id-equ) val g))
		     (nth (second next-id-equ) g))))
   :hints (("Goal" ;;;:in-theory (enable nth-update-nth)
	    :use	((:instance no-duplicatesp-dag-p
				    (p (remaining-id-stacks-invariant-path-lhs
					id-equ
					(cdr (revlist id-stack))
					(car (revlist id-stack))
					g))))))))

;;; NOTE: this lemma could be more general (without the let), but
;;; instantiating is this way, we avoid problems with free variables.

;;; Reason two for being different nodes:

(local
 (defthm identify-preserves-dag-p-main-lemma-corollary
   (implies (and (dag-p g)
		 (bounded-term-graph-p g n)
		 (path-p p g)
		 (natp i)
		 (term-dag-non-variable-p i g)
		 (natp (car (last p)))
		 (term-dag-non-variable-p (car (last p)) g)
		 (not (equal i (car (last p))))
		 (equal (dag-as-term t i g)
			(dag-as-term t (car (last p)) g)))
	    (not (equal (car p) i)))
   :hints (("Goal" :use
	    (:instance identify-preserves-dag-p-main-lemma
		       (j i) (i (car (last p))))))
   :rule-classes nil))



(local
 (defthm remaining-id-stacks-invariant-nth-update-nth-rhs
   (let ((next-id-equ (car (revlist id-stack)))
	 (requations (cdr (revlist id-stack))))
     (implies (and (term-graph-p g)
		   (dag-p g)
		   (natp (second id-equ))
		   (term-dag-non-variable-p (second id-equ) g)
		   (natp (third id-equ))
		   (term-dag-non-variable-p (third id-equ) g)
		   (not (equal (second id-equ) (third id-equ)))
		   (equal (dag-as-term t (second id-equ) g)
			  (dag-as-term t (third id-equ) g))
		   (remaining-id-stacks-invariant
		    id-equ requations next-id-equ g))
	      (equal (nth (third next-id-equ) (update-nth (second id-equ) val g))
		     (nth (third next-id-equ) g))))
   :hints (("Goal" ;;:in-theory (enable nth-update-nth)
	    :use
	    ((:instance identify-preserves-dag-p-main-lemma-corollary
			(n (len g))
			(i (second id-equ))
			(p (remaining-id-stacks-invariant-path-rhs
			    id-equ
			    (cdr (revlist id-stack))
			    (car (revlist id-stack))
			    g))))))))
;;; NOTE: again this lemma could be more general (without the let), but
;;; instantiating is this way, we avoid problems with free variables.


;;; Inorder to prove that iter-remaining... is preserved by update-nth
;;; (theorem
;;; iter-remaining-id-stacks-invariant-preserved-by-identification-main-lemma)
;;; we need to use again that none of the involved ids are equal to the
;;; updated node. For that, we again prove the same two reasons than
;;; above, but now  taking into account that the path is an append of a
;;; certain p1 (or p2) with the path obtained from the fact that we have
;;; a remaining-path-invariant.

(local
 (defthm consp-len-bigger-than-1
   (iff (> (len l) 1)
	(and (consp l) (consp (cdr l))))))



(local
 (defthm remaining-id-stacks-invariant-path-append-lhs-consp
   (implies (dag-p g)
	    (and (consp
		  (remaining-id-stacks-invariant-path-append-lhs
		   p id-equ requations next-id-equ g))
		 (consp
		  (cdr
		   (remaining-id-stacks-invariant-path-append-lhs
		    p id-equ requations next-id-equ g)))))
   :hints (("Goal" :use remaining-id-stacks-invariant-path-append-lhs-at-least-two-elements))))


(local
 (defthm remaining-id-stacks-invariant-path-append-rhs-consp
  (implies (dag-p g)
	   (and (consp
		 (remaining-id-stacks-invariant-path-append-rhs
		  p id-equ requations next-id-equ g))
		(consp
		 (cdr
		  (remaining-id-stacks-invariant-path-append-rhs
		   p id-equ requations next-id-equ g)))))
  :hints (("Goal" :use remaining-id-stacks-invariant-path-append-rhs-at-least-two-elements))))




(local
 (defthm remaining-id-stacks-invariant-nth-update-nth-append-lhs
   (let ((next-id-equ (car (revlist id-stack)))
	 (requations (cdr (revlist id-stack))))
     (implies (and
	       (equal (car p) (second id-equ)) ;;; puesto aqui porque es
					;;; la unica variable libre y en
					;;; el siguiente sitio donde
					;;; aparece es no-recursivo
	       (term-graph-p g)
	       (dag-p g)
	       (remaining-id-stacks-invariant
		id-equ requations next-id-equ g)
	       (path-p p g)
	       (equal (car p) (second id-equ))
	       (natp (car (last p))))
	      (equal (nth (second next-id-equ) (update-nth (car (last p)) val g))
		     (nth (second next-id-equ) g))))
   :hints (("Goal" ;;:in-theory (enable nth-update-nth)
	    :use	((:instance no-duplicatesp-dag-p
				    (p
				     (remaining-id-stacks-invariant-path-append-lhs
				      p
				      id-equ
				      (cdr (revlist id-stack))
				      (car (revlist id-stack))
				      g))))))))

;;; NOTE: again this lemma could be more general (without the let), but
;;; instantiating is this way, we avoid problems with free variables.

(local
 (defthm remaining-id-stacks-invariant-nth-update-nth-append-rhs
   (let ((next-id-equ (car (revlist id-stack)))
	 (requations (cdr (revlist id-stack))))
     (implies (and
	       (equal (car p) (third id-equ)) ;;; Lo mismo que antes
	       (term-graph-p g)
	       (dag-p g)
	       (remaining-id-stacks-invariant
		id-equ requations next-id-equ g)
	       (path-p p g)
	       (consp p)
	       (natp (car (last p)))
	       (natp i)
	       (term-dag-non-variable-p i g)
	       (term-dag-non-variable-p (car (last p)) g)
	       (not (equal i (car (last p))))
	       (equal (dag-as-term t i g)
		      (dag-as-term t (car (last p)) g)))
	      (equal (nth (third next-id-equ) (update-nth i (car (last p)) g))
		     (nth (third next-id-equ) g))))
   :hints (("Goal" ;;:in-theory (enable nth-update-nth)
	    :use
	    ((:instance identify-preserves-dag-p-main-lemma-corollary
			(n (len g))
			(p (remaining-id-stacks-invariant-path-append-rhs
			    p
			    id-equ
			    (cdr (revlist id-stack))
			    (car (revlist id-stack))
			    g))))))))

;;; NOTE: again this lemma could be more general (without the let), but
;;; instantiating is this way, we avoid problems with free variables.




;;; In this moment, it remains to be proved:
;;; - iter-remaining-id-stacks-invariant (this can be proved using a
;;;   trick: the invariant implies that ther is a path from the updated
;;;   node and the first id of the ids stacks).
;;; - If just after the identified id ther is another id, then
;;;   equations-already-solved of its arguments is verified (this is
;;;   easy).
;;; - If there are remaining equations, then
;;; first-id-stack-invariant-with-equations (this is also easy).

;;; Let us first prove iter-remaining-id-stacks-invariant:

(local
 (defun induct-iter-remaining-id-stacks-invariant (p1 p2 id-equ
						      id-stack-list g)
   (if (endp id-stack-list)
       (append p1 p2)
     (let* ((first-id-stack (car id-stack-list))
	    (rfirst-id-stack (revlist first-id-stack))
	    (next-id-equ (car rfirst-id-stack))
	    (requations (cdr rfirst-id-stack)))
       (and (remaining-id-stacks-invariant id-equ requations next-id-equ g)
	    (induct-iter-remaining-id-stacks-invariant
	     (remaining-id-stacks-invariant-path-append-lhs
	      p1 id-equ requations next-id-equ g)
	     (remaining-id-stacks-invariant-path-append-rhs
	      p2 id-equ requations next-id-equ g)
	     next-id-equ (cdr id-stack-list) g))))))




(local
 (defthm identify-preserves-dag-p-corollary
   (implies (and (dag-p g)
		 (bounded-term-graph-p g n)
		 (natp i) (natp j)
		 (not (equal i j))
		 (term-dag-non-variable-p i g)
		 (term-dag-non-variable-p j g)
		 (equal (dag-as-term t i g)
			(dag-as-term t j g)))
	    (dag-p (update-nth i j g)))))

(local
 (encapsulate
  ()

  (local
   (defthm dag-deref-preserved-by-identification-lemma-1
     (implies (and (dag-p g)
		   (natp i)
		   (term-dag-non-variable-p i g)
		   (not (equal i (dag-deref h g))))
	      (not (equal i h)))
     :rule-classes nil))

  (local
   (defthm dag-deref-preserved-by-identification-lemma-2
     (implies (and (dag-p g)
		   (bounded-term-graph-p g n)
		   (natp i)
		   (term-dag-non-variable-p i g)
		   (natp j)
		   (term-dag-non-variable-p j g)
		   (not (equal i j))
		   (equal (dag-as-term t i g)
			  (dag-as-term t j g))
		   (natp h)
		   (not (equal i (dag-deref h g)))
		   (not (equal i h)))
	      (equal (dag-deref h g) (dag-deref h (update-nth i j g))))
    ;;;:hints (("Goal" :in-theory (enable nth-update-nth)))
     :rule-classes nil))


  (defthm dag-deref-preserved-by-identification-main-lemma
    (implies (and (dag-p g)
		  (bounded-term-graph-p g n)
		  (natp i)
		  (term-dag-non-variable-p i g)
		  (natp j)
		  (term-dag-non-variable-p j g)
		  (not (equal i j))
		  (equal (dag-as-term t i g)
			 (dag-as-term t j g))
		  (natp h)
		  (not (equal i (dag-deref h g))))
	     (equal (dag-deref h (update-nth i j g)) (dag-deref h g)))
    :hints (("Goal" :use (dag-deref-preserved-by-identification-lemma-1
			  dag-deref-preserved-by-identification-lemma-2))))))


(local
 (defthm equations-already-solved-preserved-by-identification
   (implies (and (dag-p g)
		 (bounded-term-graph-p g n)
		 (natp i)
		 (term-dag-non-variable-p i g)
		 (natp j)
		 (term-dag-non-variable-p j g)
		 (not (equal i j))
		 (equal (dag-as-term t i g)
			(dag-as-term t j g))
		 (nat-true-listp l1)
		 (nat-true-listp l2)
		 (equations-already-solved l1 l2 g))
	    (equations-already-solved l1 l2 (update-nth i j g)))))


(local
 (defthm
   remaining-id-stacks-invariant-aux-preserved-by-identification-main-lemma
   (implies (and (dag-p g)
		 (bounded-term-graph-p g n)
		 (natp i)
		 (term-dag-non-variable-p i g)
		 (not (equal i (second id-equ)))
		 (not (equal i (third id-equ)))
		 (natp j)
		 (term-dag-non-variable-p j g)
		 (not (equal i j))
		 (equal (dag-as-term t i g)
			(dag-as-term t j g))
		 (nat-true-listp rargs1)
		 (nat-true-listp rargs2)
		 (remaining-id-stacks-invariant-aux
		  rargs1 rargs2 requations id-equ g))
	    (remaining-id-stacks-invariant-aux
	     rargs1 rargs2 requations id-equ (update-nth i j g)))))


;;; How long it takes!!!
(local
 (defthm
   remainng-id-stacks-invariant-aux-preserved-by-identification-main-lemma-corollary
   (implies (and (dag-p g)
		 (term-graph-p g)
		 (path-p p1 g)
		 (> (len p1) 1)
		 (equal (car p1) (second id-equ))
		 (natp (second id-equ)) ;;; sobra?
		 (term-dag-non-variable-p (second id-equ) g) ;; sobra?
		 (natp (car (last p1))) ;;; sobra???
		 (term-dag-non-variable-p (car (last p1)) g)

		 (path-p p2 g)
		 (> (len p2) 1)
		 (natp (car (last p2))) ;;; sobra??
		 (term-dag-non-variable-p (car (last p2)) g)
		 (equal (car p2) (third id-equ))
		 (natp (third id-equ))
		 (term-dag-non-variable-p (third id-equ) g)
		 (not (equal (car (last p1)) (car (last p2))))
		 (equal (dag-as-term t (car (last p1)) g)
			(dag-as-term t (car (last p2)) g))
		 (nat-true-listp rargs1)
		 (nat-true-listp rargs2)
		 (remaining-id-stacks-invariant-aux
		  rargs1 rargs2 requations id-equ g))
	    (remaining-id-stacks-invariant-aux
	     rargs1 rargs2 requations id-equ
	     (update-nth (car (last p1)) (car (last p2)) g)))
   :hints (("Goal"
	    :use
	    ((:instance
	      remaining-id-stacks-invariant-aux-preserved-by-identification-main-lemma
	      (i (car (last p1))) (j (car (last p2))))
	     (:instance no-duplicatesp-dag-p
			(p p1))
	     (:instance identify-preserves-dag-p-main-lemma-corollary
			(p p2)
			(i (car (last p1)))
			(n (len g))))
	    :do-not-induct t))))


;;; Suddenly, and after proving the above theorem, this takes too time!!!  Why???
(local
 (defthm
   iter-remaining-id-stacks-invariant-preserved-by-identification-main-lemma
   (implies (and (dag-p g)
		 (term-graph-p g)
		 (path-p p1 g)
		 (> (len p1) 1)
		 (equal (car p1) (second id-equ))
		 (natp (second id-equ))
		 (term-dag-non-variable-p (second id-equ) g)
		 (natp (car (last p1))) ;;; sobra???
		 (term-dag-non-variable-p (car (last p1)) g)

		 (path-p p2 g)
		 (> (len p2) 1)
		 (natp (car (last p2))) ;;; sobra??
		 (term-dag-non-variable-p (car (last p2)) g)
		 (equal (car p2) (third id-equ))
		 (natp (third id-equ))
		 (term-dag-non-variable-p (third id-equ) g)
		 (not (equal (car (last p1)) (car (last p2))))
		 (equal (dag-as-term t (car (last p1)) g)
			(dag-as-term t (car (last p2)) g))
		 (iter-remaining-id-stacks-invariant
		  id-equ id-stack-list g))
	    (iter-remaining-id-stacks-invariant
	     id-equ id-stack-list (update-nth (car (last p1)) (car (last p2)) g)))
   :hints (("Goal" :induct
	    (induct-iter-remaining-id-stacks-invariant
	     p1 p2 id-equ id-stack-list g)
	    :in-theory (disable  last nth-update-nth)))))
;;; NOTE: again this lemma could be more general (without the let), but
;;; instantiating is this way, we avoid problems with free variables.


(local
 (defthm remaining-id-stacks-invariant-path-lhs-consp
   (implies (dag-p g)
	    (and (consp
		  (remaining-id-stacks-invariant-path-lhs
		   id-equ requations next-id-equ g))
		 (consp
		  (cdr
		   (remaining-id-stacks-invariant-path-lhs
		    id-equ requations next-id-equ g)))))
   :hints (("Goal" :use remaining-id-stacks-invariant-path-lhs-at-least-two-elements))))


(local
 (defthm remaining-id-stacks-invariant-path-rhs-consp
   (implies (dag-p g)
	    (and (consp
		  (remaining-id-stacks-invariant-path-rhs
		   id-equ requations next-id-equ g))
		 (consp
		  (cdr
		   (remaining-id-stacks-invariant-path-rhs
		    id-equ requations next-id-equ g)))))
   :hints (("Goal" :use remaining-id-stacks-invariant-path-rhs-at-least-two-elements))))



(local
 (defthm
   iter-remaining-id-stacks-invariant-preserved-by-identification
   (let ((id-equ (car (revlist id-stack)))
	 (requations (cdr (revlist id-stack))))
     (implies (and (dag-p g)
		   (term-graph-p g)
		   (natp (second id-eq0)) ;;; sobra???
		   (term-dag-non-variable-p (second id-eq0) g)

		   (natp (third id-eq0)) ;;; sobra??
		   (term-dag-non-variable-p (third id-eq0) g)

		   (not (equal (second id-eq0) (third id-eq0)))
		   (equal (dag-as-term t (second id-eq0) g)
			  (dag-as-term t (third id-eq0) g))

		   (remaining-id-stacks-invariant
		    id-eq0 requations id-equ g)
		   (iter-remaining-id-stacks-invariant
		    id-equ id-stack-list g))
	      (iter-remaining-id-stacks-invariant
	       id-equ id-stack-list (update-nth (second id-eq0) (third id-eq0) g))))
   :hints (("Goal"
	    :use
	    (:instance
	     iter-remaining-id-stacks-invariant-preserved-by-identification-main-lemma
	     (id-equ (car (revlist id-stack)))
	     (p1 (remaining-id-stacks-invariant-path-lhs
		  id-eq0  (cdr (revlist id-stack)) (car (revlist id-stack)) g))
	     (p2 (remaining-id-stacks-invariant-path-rhs
		  id-eq0 (cdr (revlist id-stack)) (car (revlist id-stack)) g)))))))
;;; NOTE: again this lemma could be more general (without the let), but
;;; instantiating is this way, we avoid problems with free variables.


;;; Two subgoals remain, related to the first "id-stack"

;;; Two cases may occur:

;;; 1) The equation next to the id is another id: in this case we have to
;;; prove that their arguments are already solved.
;;; 2) The equation next to the id is not an id: in this case we have to
;;; prove  first-id-stack-with-equations....

;;; Case 1)

(local
 (encapsulate
  ()

  (local
   (defthm equations-already-solved-preserved-by-identification-first-stack-lemma-1
     (implies (and (dag-p g)
		   (term-graph-p g)
		   (natp i)
		   (term-dag-non-variable-p i g)
		   (natp j)
		   (term-dag-non-variable-p j g)
		   (not (equal i j))
		   (equal (dag-as-term t i g)
			  (dag-as-term t j g))
		   (nat-true-listp l1)
		   (nat-true-listp l2)
		   (equations-already-solved (revlist l1) (revlist l2) g))
	      (equations-already-solved l1 l2 (update-nth i j g)))
     :rule-classes nil))

  (local
   (defthm equations-already-solved-preserved-by-identification-first-stack-lemma-2
     (implies (and (dag-p g)
		   (term-graph-p g)
		   (equal (dag-as-term t i g)
			  (dag-as-term t j g))
		   (equal (dag-deref (car m1) g) i)
		   (equal (dag-deref (car m2) g) j)
		   (nat-true-listp m1) (consp m1)
		   (nat-true-listp m2) (consp m2)
		   (equations-already-solved (cdr m1) (cdr m2) g))
	      (equations-already-solved m1 m2 g))
     :hints (("Goal" :in-theory (enable dag-as-term-dag-deref)))
     :rule-classes nil))



  (defthm equations-already-solved-preserved-by-identification-first-stack
    (implies (and (dag-p g)
		  (term-graph-p g)
		  (natp i)
		  (term-dag-non-variable-p i g)
		  (natp j)
		  (term-dag-non-variable-p j g)
		  (not (equal i j))
		  (equal (dag-as-term t i g)
			 (dag-as-term t j g))
		  (equal (dag-deref (car (revlist l1)) g) i)
		  (equal (dag-deref (car (revlist l2)) g) j)
		  (nat-true-listp l1) (consp l1)
		  (nat-true-listp l2) (consp l2)
		  (equations-already-solved (cdr (revlist l1))
					    (cdr (revlist l2)) g))
	     (equations-already-solved l1 l2 (update-nth i j g)))
    :hints (("Goal" :use
	     (equations-already-solved-preserved-by-identification-first-stack-lemma-1
	      (:instance
	       equations-already-solved-preserved-by-identification-first-stack-lemma-2
	       (m1 (revlist l1)) (m2 (revlist l2))))
	     :in-theory (disable
			 equations-already-solved-revlist))))))


;;; Case 2)

(local
 (defthm
   remaining-id-stacks-invariant-aux-first-id-stack-invariant-aux-with-equations-first-id-stack
   (implies (and (dag-p g)
		 (term-graph-p g)
		 (natp (second id-equ))
		 (term-dag-non-variable-p (second id-equ) g)
		 (natp (third id-equ))
		 (term-dag-non-variable-p (third id-equ) g)
		 (not (equal (second id-equ) (third id-equ)))
		 (equal (dag-as-term t (second id-equ) g)
			(dag-as-term t (third id-equ) g))
		 (nat-true-listp l1)
		 (nat-true-listp l2)
		 (consp requations)
		 (remaining-id-stacks-invariant-aux
		  l1 l2 requations id-equ g))
	    (first-id-stack-invariant-aux-with-equations
	     l1 l2 requations (update-nth (second id-equ) (third id-equ)
					  g)))
   :hints (("Subgoal *1/1"
	    :use ((:instance  dag-as-term-dag-deref
			      (h (cadr l1)))
		  (:instance  dag-as-term-dag-deref
			      (h (cadr l2))))))))



(local
  (defthm rewrite-rule-to-expand-iter-remaining-id-stacks-invariant
    (implies
     (consp id-stack-list)
     (equal (iter-remaining-id-stacks-invariant
	     id-equ id-stack-list g)
	    (let* ((first-id-stack (car id-stack-list))
		   (rfirst-id-stack (revlist first-id-stack))
		   (next-id-equ (car rfirst-id-stack))
		   (requations (cdr rfirst-id-stack)))
	      (and (remaining-id-stacks-invariant id-equ requations next-id-equ g)
		   (iter-remaining-id-stacks-invariant next-id-equ (cdr id-stack-list) g)))))))



;;; =====================================
;;; =====================================
;;; =====================================
;;; =====================================
;;; AND FINALLY, THE DESIRED  THEOREM!!!!
;;; =====================================
;;; =====================================
;;; =====================================
;;; =====================================



(defthm transform-mm-q-preserves-ext-upl-id-invariant
  (implies (and (not (normal-form-syst ext-upl))
		(well-formed-extended-upl ext-upl)
		(ext-upl-occur-check-invariant ext-upl)
		(ext-upl-id-invariant ext-upl))
	   (ext-upl-id-invariant
	    (dag-transform-mm-q ext-upl)))
  :hints (("Goal" :in-theory (disable nth-update-nth))))


;;; 4.4 The occur-check invariant is preserved
;;; ------------------------------------------


(local
 (defthm occur-check-q-length-stamp
   (implies (and (dag-p g)
		 (term-graph-p g)
		 (equal (len g) (len stamp))
		 (if flg
		     (bounded-natp h (len g))
		   (bounded-nat-true-listp h (len g))))
	    (equal (len (second (occur-check-q
				 flg x h g stamp time)))
		   (len stamp)))))

(local
 (defun all-marks-integers-less-or-equal-than-time
   (stamp time)
   (if (endp stamp)
       t
     (and (integerp (car stamp))
	  (<= (car stamp) time)
	  (all-marks-integers-less-or-equal-than-time
	   (cdr stamp) time)))))

(local
 (defthm all-marks-integers-less-or-equal-than-time-update-nth
   (implies (and (bounded-natp h (len stamp))
		 (integerp time)
		 (all-marks-integers-less-or-equal-than-time
		  stamp time))
	    (all-marks-integers-less-or-equal-than-time
	     (update-nth h time stamp) time))))

(local
 (defthm occur-check-q-all-marks-integers-less-or-equal-than-time
   (implies (and (dag-p g)
		 (term-graph-p g)
		 (integerp time)
		 (equal (len g) (len stamp))
		 (all-marks-integers-less-or-equal-than-time
		  stamp time)
		 (if flg
		     (bounded-natp h (len g))
		   (bounded-nat-true-listp h (len g))))
	    (all-marks-integers-less-or-equal-than-time
	     (second (occur-check-q
		      flg x h g stamp time))
	     time))))

(local
 (defthm all-marks-integers-less-or-equal-less
   (implies (all-marks-integers-less-or-equal-than-time
	     stamp time)
	    (all-marks-integers-less-than-time
	     stamp (1+ time)))))

(local
 (defthm all-marks-integers-less-less-or-equal
   (implies (all-marks-integers-less-than-time
	     stamp time)
	    (all-marks-integers-less-or-equal-than-time
	     stamp time))))



(local
 (defthm transform-mm-q-preserves-ext-upl-occur-check-invariant
   (implies (and
	     (not (normal-form-syst ext-upl))
	     (well-formed-extended-upl ext-upl)
	     (ext-upl-occur-check-invariant ext-upl))
	    (ext-upl-occur-check-invariant
	     (dag-transform-mm-q ext-upl)))))




(in-theory (disable dag-transform-mm-q))



(local (in-theory (disable well-formed-extended-upl-def)))

(in-theory
 (disable
	  ext-upl-id-invariant
	  ext-upl-occur-check-invariant))




;;; ==============================================
;;; COMPILING ALL THE ABOVE IN A BEAUTIFUL THEOREM
;;; ==============================================


(defthm unification-invariant-q-preserved
   (implies (and (not (normal-form-syst ext-upl))
		 (unification-invariant-q ext-upl))
	    (unification-invariant-q
	     (dag-transform-mm-q ext-upl))))

;;; ----------------------------------------------------------------







;;;============================================================================
;;;
;;; 5) Termination of the transformation on extended upls
;;;
;;;============================================================================



;;; In this section, we concentrate on the justification of the
;;; termination. A lexicographic measure will suffice, combining:
;; - The already known measure for non-extended systems
;; (unification-measure)
;; - The number of ids in the extended system



(local
  (defthm q-rules-well-founded-decrease-for-non-identifications
    (implies (and (well-formed-upl upl)
		  (unif-legal-q upl op)
		  (not (equal (first op) 'identify)))
	     (o< (unification-measure
		   (upl-as-pair-of-systems (unif-reduce-one-step-q
					    upl op)))
		  (unification-measure
		   (upl-as-pair-of-systems upl))))
    :hints (("Goal" :in-theory (disable unification-measure)))))



(defun number-of-ids (ext-S)
  (cond ((endp ext-S) 0)
	((equal (first (car ext-S)) 'id)
	 (1+ (number-of-ids (cdr ext-S))))
	(t (number-of-ids (cdr ext-S)))))



(defun unification-measure-q (ext-upl)
  (cons (cons (unification-measure
	       (upl-as-pair-of-systems
		(ext-upl-to-upl
		 ext-upl)))
	      1)
	(number-of-ids (first ext-upl))))



;;; Some previous lemmas...

(local
 (defthm dag-transform-mm-q-op-identification
  (iff (equal (first (dag-transform-mm-q-op ext-upl)) 'identify)
       (equal (first (first (first ext-upl))) 'id))
  :hints (("Goal" :in-theory (enable dag-transform-mm-q-op)))))




(local
 (defthm dag-transform-mm-q-identification-reduce-ids
   (implies (equal (first (first (first ext-upl))) 'id)
	    (< (number-of-ids (first (dag-transform-mm-q ext-upl)))
	       (number-of-ids (first ext-upl))))
  :hints (("Goal" :in-theory (enable dag-transform-mm-q)))))



(local
 (in-theory (disable
	     normal-form-syst
	     ext-upl-to-upl
	     unification-measure)))

(defthm o-p-q-unification-measure
  (o-p (unification-measure-q ext-upl)))

;;; Put in another book!!
(local (defthm o<-irreflexive
	 (not (o< x x))))

(defthm unification-measure-decreases-q
  (implies (and (unification-invariant-q ext-upl)
		(not (normal-form-syst ext-upl)))
	   (o< (unification-measure-q (dag-transform-mm-q
				       ext-upl))
	       (unification-measure-q ext-upl)))
  :hints (("Goal"
	   :cases
	   ((equal (first (dag-transform-mm-q-op ext-upl))
		   'identify)))
	  ("Subgoal 2''"
	   :use
	   (:instance unification-measure-decreases
		      (S-sol (upl-as-pair-of-systems (ext-upl-to-upl
						      ext-upl)))
		      (op (dag-transform-mm-q-op ext-upl))))))


;;; We disable the measure


(in-theory (disable unification-measure-q))


;;;============================================================================
;;;
;;; 6) Iterating transformations
;;;
;;;============================================================================


(defun solve-upl-q (ext-upl)
  (declare (xargs :measure
		  (unification-measure-q ext-upl)))
  (if (unification-invariant-q ext-upl)
      (if (normal-form-syst ext-upl)
	  ext-upl
	(solve-upl-q (dag-transform-mm-q ext-upl)))
    nil))


(local
 (defun solve-upl-q-op (ext-upl)
   (declare (xargs :measure
		   (unification-measure-q ext-upl)))
   (if (unification-invariant-q ext-upl)
       (if (normal-form-syst ext-upl)
	   nil
	 (cons
	  (dag-transform-mm-q-op ext-upl)
	  (solve-upl-q-op (dag-transform-mm-q ext-upl))))
     nil)))


(local
 (defthm normal-form-syst-ext-upl-to-upl
   (implies (normal-form-syst ext-upl)
	    (normal-form-syst (ext-upl-to-upl ext-upl)))
   :hints (("Goal" :in-theory (enable
			       ext-upl-to-upl
			       normal-form-syst)))))
(local
 (defthm solve-upl-q-unif-seq-q-p-normal-form
   (implies (unification-invariant-q ext-upl)
	    (and (unif-seq-q-p (ext-upl-to-upl ext-upl)
			       (solve-upl-q-op ext-upl))
		 (normal-form-syst
		  (unif-seq-q-last (ext-upl-to-upl ext-upl)
				   (solve-upl-q-op ext-upl)))
		 (equal (ext-upl-to-upl (solve-upl-q ext-upl))
			(unif-seq-q-last (ext-upl-to-upl ext-upl)
					 (solve-upl-q-op ext-upl)))))
   :rule-classes nil))

;;; This lemma will be used for guard verification of the functions
;;; using stobjs
(local
 (defthm unification-invariant-q-preserved-by-solve-upl-q
   (implies (unification-invariant-q ext-upl)
	    (unification-invariant-q (solve-upl-q ext-upl)))
   :rule-classes nil))


;;;============================================================================
;;;
;;; 7) Iterating transformations starting form the initial unification prolem
;;;
;;;============================================================================

(defun initial-stamp (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
      (cons -1 (initial-stamp (- n 1)))))


(defun dag-mgs-q (S-dag g)
  (solve-upl-q (list S-dag nil g (initial-stamp (len g)) 0)))


(local
 (defun dag-mgs-q-op (S-dag g)
   (solve-upl-q-op (list S-dag nil g (initial-stamp (len g)) 0))))

;;;
(local
 (defthm bounded-nat-pairs-true-listp-with-and-without-ids
   (implies (bounded-nat-pairs-true-listp S-dag n)
	    (bounded-nat-pairs-true-listp-with-ids S-dag n))))

(local
 (defthm well-formed-upl-well-formed-extended-upl
   (implies (well-formed-upl (list S-dag sol g))
	    (well-formed-extended-upl (list S-dag sol g stamp time)))
   :hints (("Goal" :in-theory
	    (enable well-formed-upl-def
		    well-formed-extended-upl-def)))))

;;;

(local
 (defthm bounded-nat-pairs-true-listp-without-ids
   (implies (bounded-nat-pairs-true-listp S-dag n)
	    (not (equal
		  (first (car (last (until-first-id S-dag))))
		  'id)))))

(local
 (defthm bounded-nat-pairs-true-listp-atom-split-extended-systen
   (implies (bounded-nat-pairs-true-listp S-dag n)
	    (not (consp
		  (split-extended-system-in-id-stacks S-dag))))))


(local
 (defthm ext-upl-id-invariant-initial-ext-upl
   (implies (well-formed-dag-system S-dag g)
	    (ext-upl-id-invariant (list S-dag nil g (initial-stamp (len g)) 0)))
   :hints (("Goal"
	    :in-theory
	    (enable ext-upl-id-invariant
		    well-formed-upl-def)))))

(local
 (defthm ext-upl-occur-check-invariant-initial-ext-upl
   (ext-upl-occur-check-invariant (list S nil g (initial-stamp (len g)) 0))
   :hints (("Goal" :in-theory
	    (enable ext-upl-occur-check-invariant)))))

(local
 (defthm bounded-nat-pairs-true-listp-remove-ids
   (implies (bounded-nat-pairs-true-listp S-dag n)
	    (equal (remove-ids S-dag) S-dag))))

;;; This lemma will be used for guard verification of the stobj based
;;; function.
(local
 (defthm dag-mgs-q-well-formed-output
   (implies (well-formed-dag-system S g)
	    (and (bounded-nat-substitution-p (second (dag-mgs-q S g))
					(len (third (dag-mgs-q S g))))
		 (well-formed-term-dag-p (third (dag-mgs-q S g)))))
   :hints (("Goal"
	    :in-theory (enable well-formed-extended-upl)
	    :use (:instance
			 unification-invariant-q-preserved-by-solve-upl-q
			 (ext-upl (list S nil g (initial-stamp (len g)) 0)))))))




(local (in-theory (enable mgs-seq-q-p
			  mgs-seq-q
			  ext-upl-to-upl
			  well-formed-upl-def)))


;;; The main property of dag-mgs-q: it computes a sequence of
;;; operator-based transformations, until a normal form system is
;;; obtained. This is a key result: it will allow to translate the main
;;; properties proved about the transformation relation.

(local
 (defthm dag-mgs-q-op-unif-seq-q-p-normal-form
   (implies (well-formed-dag-system S-dag g)
	    (and (mgs-seq-q-p S-dag g (dag-mgs-q-op S-dag g))
		 (equal (ext-upl-to-upl (dag-mgs-q S-dag g))
			(mgs-seq-q S-dag g (dag-mgs-q-op S-dag g)))))

   :hints (("Goal"
	    :use
	    (:instance
	     solve-upl-q-unif-seq-q-p-normal-form
	     (ext-upl (list S-dag nil g (initial-stamp (len g)) 0)))))
   :rule-classes nil))



(local (in-theory (disable mgs-seq-q-p
			   mgs-seq-q
			   ext-upl-to-upl
			   well-formed-upl-def)))



;;;============================================================================
;;;
;;; 8) Dag-mgs-q computes a most general solution
;;;
;;;============================================================================


(local (in-theory (enable ext-upl-to-upl)))

(defthm dag-mgs-q-completeness
  (let ((S (tbs-as-system S-dag g)))
    (implies (and (well-formed-dag-system S-dag g)
		  (solution sigma S))
	     (dag-mgs-q S-dag g)))
  :hints (("Goal"
	   :use ((:instance
		  mgs-seq-q-completeness
		  (unif-seq (dag-mgs-q-op S-dag g)))
		 dag-mgs-q-op-unif-seq-q-p-normal-form))))




(defthm dag-mgs-q-soundness
  (let* ((S (tbs-as-system S-dag g))
	 (last-upl (dag-mgs-q S-dag g))
	 (sol (solved-as-system (second last-upl) (third last-upl))))
    (implies (and (well-formed-dag-system S-dag g)
		  last-upl)
	     (solution sol S)))
  :hints (("Goal"
	   :in-theory (disable mgs-seq-q-soundness)
	   :use ((:instance
		  mgs-seq-q-soundness
		  (unif-seq (dag-mgs-q-op S-dag g)))
		  dag-mgs-q-op-unif-seq-q-p-normal-form))))


(defthm dag-mgs-q-idempotent
  (let* ((last-upl (dag-mgs-q S-dag g))
	 (sol (solved-as-system (second last-upl) (third last-upl))))
    (implies (and (well-formed-dag-system S-dag g)
		  last-upl)
	     (idempotent sol)))
  :hints (("Goal"
	   :use ((:instance
		  mgs-seq-q-idempotent
		  (unif-seq (dag-mgs-q-op S-dag g)))
		  dag-mgs-q-op-unif-seq-q-p-normal-form))))



(defthm dag-mgs-q-most-general-solution
  (let* ((S (tbs-as-system S-dag g))
	 (last-upl (dag-mgs-q S-dag g))
	 (sol (solved-as-system (second last-upl) (third last-upl))))
    (implies (and (well-formed-dag-system S-dag g)
		  (solution sigma S))
	     (subs-subst sol sigma)))
  :hints (("Goal"
	   :in-theory (disable mgs-seq-q-most-general-solution )
	   :use ((:instance
		  mgs-seq-q-most-general-solution
		  (unif-seq (dag-mgs-q-op S-dag g)))
		  dag-mgs-q-op-unif-seq-q-p-normal-form))))




(local (in-theory (disable ext-upl-to-upl)))



;;;============================================================================
;;;
;;; 8) Unification of two terms
;;;
;;;============================================================================



(defun dag-mgu-q (t1 t2 g)
  (let ((g (unif-two-terms-problem t1 t2 g)))
    (dag-mgs-q
     (initial-to-be-solved g) g)))

(local
 (in-theory (disable
	     idempotent
	     dag-mgs-q
	     tbs-as-system
	     initial-to-be-solved
	     unif-two-terms-problem)))



;;; "Almost" properties

(local
 (defthm dag-mgu-q-completeness-almost
   (let* ((g-t1-t2 (unif-two-terms-problem t1 t2 g))
	  (S-dag-t1-t2 (initial-to-be-solved g-t1-t2)))
     (implies
      (and (empty-graph-p g) (term-p t1) (term-p t2)
	   (solution sigma (tbs-as-system S-dag-t1-t2 g-t1-t2)))
      (dag-mgu-q t1 t2 g)))
   :hints (("Goal" :in-theory (disable unif-two-terms-problem-stores-the-problem)))
   :rule-classes nil))

(local
 (defthm dag-mgu-q-soundness-almost
   (let* ((g-t1-t2 (unif-two-terms-problem t1 t2 g))
	  (S-dag-t1-t2 (initial-to-be-solved g-t1-t2))
	  (S (tbs-as-system S-dag-t1-t2 g-t1-t2))
	  (dag-mgu-q (dag-mgu-q t1 t2 g))
	  (sol (solved-as-system (second dag-mgu-q) (third dag-mgu-q))))
     (implies (and (empty-graph-p g) (term-p t1) (term-p t2)
		   dag-mgu-q)
	      (solution sol S)))
   :rule-classes nil))



(local
 (defthm dag-mgu-q-most-general-solution-almost
   (let* ((g-t1-t2 (unif-two-terms-problem t1 t2 g))
	  (S-dag-t1-t2 (initial-to-be-solved g-t1-t2))
	  (S (tbs-as-system S-dag-t1-t2 g-t1-t2))
	  (dag-mgu-q (dag-mgu-q t1 t2 g))
	  (sol (solved-as-system (second dag-mgu-q) (third dag-mgu-q))))
     (implies (and (empty-graph-p g) (term-p t1) (term-p t2)
		   (solution sigma S))
	      (subs-subst sol sigma)))
    :rule-classes nil))


;;;; ************************
;;; THE MAIN PROPERTIES
;;;; ************************



;;; Finally, the following theorems establish the main properties of
;;; {\tt dag-mgu-q}, showing that {\tt dag-mgu-q} computes the most
;;; general unifier of two terms, whenever it exists.


(defthm dag-mgu-q-completeness
  (implies
   (and (empty-graph-p g) (term-p t1) (term-p t2)
	(equal (instance t1 sigma)
	       (instance t2 sigma)))
     (dag-mgu-q t1 t2 g))
  :hints (("Goal" :use dag-mgu-q-completeness-almost)))




(defthm dag-mgu-q-soundness
  (let* ((dag-mgu-q (dag-mgu-q t1 t2 g))
	 (sol (solved-as-system (second dag-mgu-q) (third dag-mgu-q))))
    (implies (and (empty-graph-p g) (term-p t1) (term-p t2)
		  dag-mgu-q)
	     (equal (instance t1 sol) (instance t2 sol))))
    :hints (("Goal" :use dag-mgu-q-soundness-almost)))




(defthm dag-mgu-q-most-general-solution
  (let* ((dag-mgu-q (dag-mgu-q t1 t2 g))
	 (sol (solved-as-system (second dag-mgu-q) (third dag-mgu-q))))
    (implies (and (empty-graph-p g) (term-p t1) (term-p t2)
		  (equal (instance t1 sigma)
			 (instance t2 sigma)))
	     (subs-subst sol sigma)))
    :hints (("Goal" :use dag-mgu-q-most-general-solution-almost)))



(defthm dag-mgu-q-idempotent
  (let* ((dag-mgu-q (dag-mgu-q t1 t2 g))
	 (sol (solved-as-system (second dag-mgu-q) (third dag-mgu-q))))
    (implies (and (empty-graph-p g) (term-p t1) (term-p t2)
		  dag-mgu-q)
	     (idempotent sol))))



;;; Needed for guard verification:

(defthm dag-mgu-q-well-formed-output
  (implies (and (term-p t1) (term-p t2)
		(empty-graph-p g))
	   (and (bounded-nat-substitution-p
		 (second (dag-mgu-q t1 t2 g))
		 (len (third (dag-mgu-q t1 t2 g))))
		(well-formed-term-dag-p (third (dag-mgu-q t1 t2 g))))))

;;; Note that we leave this function disabled

(in-theory  (disable unification-invariant-q))
