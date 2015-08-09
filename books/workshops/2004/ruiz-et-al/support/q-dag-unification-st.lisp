;;;============================================================================
;;; q-dag-unification-st.lisp
;;; Título: A quadratic unification algorithm using stobjs
;;;============================================================================

#| To be certified:

(certify-book "q-dag-unification-st")

|#

(in-package "ACL2")

(include-book "q-dag-unification")

;;;============================================================================
;;;
;;; 0) Introducción
;;;
;;;============================================================================

;;;   In this file ({\tt q-dag-unification-st.lisp}), we define a
;;;   quadratic unification
;;;   algorithm using a stobj to store terms represented as dags.

;;;   This program is based on a Pascal implementation given in the book "Term
;;; Rewriting and all that...", F. Baader and T. Nipkow (Cambridge University
;;; Press, 1998) pp. 82-88

;;;============================================================================
;;;
;;; 1) Definition of the @terms-dag@ stobj
;;;
;;;============================================================================

;;;   Definition of the @terms-dag@ stobj, used to store the terms as graphs.
;;; It uses two arrays:

;;; * The dag array stores the terms to be unified, as directed acyclic
;;;   graphs. Each cell in the array corresponds to a node in  the graph.

;;; * The stamp array contains an integer in each array cell, marking the
;;;   time when the  last occur-check for that subterm was
;;;   done. This avoids redundant occur-checks.

;;;   There are two kinds of nodes in the dag array: function nodes and
;;; variable nodes.  Depending on the kind of a node @h@, we will store in {\tt
;;; (dagi h g)} the following information:

;;; *)
;;;   Variable nodes. They can be of two forms:
;;; *.*)
;;;              @N@ (integer numbers): bound variables. They are bound to
;;;              the node @N@ (note that negative numbers are interpreted
;;;              w.r.t. @nth@ as 0). I will call this nodes "IS" nodes.
;;; *.*)
;;;              {\tt (X . T)} : they represent an unbound variable
;;;              @X@. I will call these nodes "VARIABLES".
;;; *.-)
;;; *)
;;;   Non-variable nodes (function nodes): {\tt (F. L)} (where @L@ is
;;;   different from @T@), interpreted as the function symbol @F@ and the
;;;   list @L@ of its neighbors (its arguments). These are "NON-VARIABLE"
;;;   nodes.
;;; -)

(defstobj terms-dag
  (dag :type (array t (0))
       :resizable t)
  (stamp :type (array integer (0))
	 :initially -1
	 :resizable t))

;;;   Some useful macros, improving readability:

;; ;;; They are in q-dag-unification.lisp

;; (defmacro dag-variable-p (x)
;;   `(equal (cdr ,x) t))

;; (defmacro dag-symbol (x)
;;   `(car ,x))

;; (defmacro dag-args (x)
;;   `(cdr ,x))

;; (defmacro dag-bound-p (x)
;;   `(integerp ,x))

;;; The array components of the stobj.

(defmacro terms-dag-dag (td)
  `(nth 0 ,td))

(defmacro terms-dag-stamp (td)
  `(nth 1 ,td))



;;; Note that we cannot define them as functions because of signature
;;; restrictions. And of course a call to these macros cannot be used in
;;; a function definition, for the same reasons. Instead, we can define
;;; functions that "collect" the components of the arrays in lists:


;;;   The following function {\tt dag-component-st} obtains a list with same
;;; components than the array stored by @terms-dag@. Note that it is not
;;; possible to define it in a simpler way:

(defun dag-component-st-aux (n terms-dag)
  (declare (xargs :stobjs terms-dag
		  :measure (nfix (- (dag-length terms-dag) n))
		  :guard (natp n)))
  (if (and (integerp n) (< n (dag-length terms-dag)))
      (cons (dagi n terms-dag)
	    (dag-component-st-aux (+ n 1) terms-dag))
      nil))

(defun dag-component-st (terms-dag)
  (declare (xargs :stobjs terms-dag))
  (dag-component-st-aux 0 terms-dag))

;;;   The following function {\tt stamp-component-st} obtains a list with same
;;; components than the @stamp@ array stored by @terms-dag@. Note that it is
;;; not possible to define it in a simpler way:

(defun stamp-component-st-aux (n terms-dag)
  (declare (xargs :stobjs terms-dag
		  :measure (nfix (- (stamp-length terms-dag) n))
		  :guard (natp n)))
  (if (and (integerp n) (< n (stamp-length terms-dag)))
      (cons (stampi n terms-dag)
	    (stamp-component-st-aux (+ n 1) terms-dag))
      nil))

(defun stamp-component-st (terms-dag)
  (declare (xargs :stobjs terms-dag))
  (stamp-component-st-aux 0 terms-dag))




;;; The point is: we are going to use the properties proved about the
;;; "list" version of this unification algorithm, so we need to state
;;; the relation between the stobj version and the list version. It
;;; turns out that most of the functions (those that will not be
;;; directly executed, and thus their efficiency is not important) can
;;; be defined as the application of the "list" version of the function
;;; on the lists of the array components "extracted" by dag-component-st
;;; and stamp-component-st.


;;;   Due to the restrictions in the use of a stobj, we can not define the
;;; functions {\tt dag-component-st} and {\tt stamp-component-st} simply
;;; as {\tt (nth 0 terms-dag)} and {\tt (nth 1 terms-dag)}. But we
;;; can prove in the logic that it is equal to that expression. The following
;;; lemmas are needed to show that, as established by the theorem {\tt
;;; dag-component-st-main-property} and {\tt
;;; stamp-component-st-main-property}

(local
 (defthm nth-fix-true-list
   (equal (nth n (fix-true-list l))
	  (nth n l))))



(encapsulate
 ()

 (local
  (defun list-components-nth (n l)
    (declare (xargs :measure (nfix (- (len l) n))))
    (if (and (integerp n) (< n (len l)))
	(cons (nth n l) (list-components-nth (+ n 1) l))
      nil)))

 (local
  (defun list-components (n l)
    (if (zp n)
	l
      (list-components (- n 1) (cdr l)))))


 (local
  (defthm list-components-defined-with-nth
    (implies (and (< n (len l)) (consp l))
	     (equal (cons (nth n l) (list-components n (cdr l)))
		    (list-components n l)))))


 (local
  (defthm list-components-nth-list-components-for-true-listp
    (implies (and (true-listp m) (natp n))
	     (equal (list-components-nth n m)
		    (list-components n m)))))

 (local
  (defthm list-components-nth-true-listp
    (equal (list-components-nth n (fix-true-list l))
	   (list-components-nth n l))
    :rule-classes nil))


 (local
  (defthm list-components-nth-main-property
    (equal (list-components-nth 0 l) (fix-true-list l))
    :hints (("Goal" :use (:instance list-components-nth-true-listp (n 0))))))


 (local
  (defthm list-components-nth-dag-component-st-aux
    (equal (dag-component-st-aux n terms-dag)
	   (list-components-nth n (nth 0 terms-dag)))))

 (local
  (defthm list-components-nth-stamp-component-st-aux
    (equal (stamp-component-st-aux n terms-dag)
	   (list-components-nth n (nth 1 terms-dag)))))


 (defthm dag-component-st-main-property
   (equal (dag-component-st terms-dag)
	  (fix-true-list (terms-dag-dag terms-dag))))

 (defthm stamp-component-st-main-property
   (equal (stamp-component-st terms-dag)
	  (fix-true-list (terms-dag-stamp terms-dag)))))



;;;   The theorems {\tt dag-component-st-main-property} and {\tt
;;;   stamp-component-st-main-property} are crucial when we
;;; "export" the results about some functions defined on term dags representing
;;; the dag as a list to analogue functions defined on single--threaded object.

(in-theory (disable dag-component-st stamp-component-st))

(local (in-theory (disable nth)))

;;;============================================================================
;;;
;;; 2) Well--formedness conditions
;;;
;;;============================================================================

;;; In this section we show that every well-formedness condition is
;;; preserved by fix-true-list. This condition is the only property we
;;; need to translate the "list" version of a well-formedness condition,
;;; to a "stobj" version of the same property.


(local
 (defthm bounded-term-graph-p-fix-true-list
   (equal (bounded-term-graph-p
	   (fix-true-list l) n)
	  (bounded-term-graph-p l n))))

;;; LIST-OF-TERM-DAG-VARIABLE MEASURE-REC-DAG DAG-P

(local
 (defthm list-of-term-dag-variables-fix-true-list
   (equal (list-of-term-dag-variables
	   (fix-true-list l))
	  (list-of-term-dag-variables l))))


(local
 (defthm dag-p-aux-fix-true-list
   (equal (dag-p-aux hs rp (fix-true-list l))
	  (dag-p-aux hs rp l))))

(local
 (defthm dag-p-fix-true-list
   (equal (dag-p (fix-true-list l))
	  (dag-p l))
   :hints (("Goal" :in-theory (enable dag-p)))))

(local
 (defthm dag-nodes-aux-fix-true-listp
   (equal (dag-nodes-aux x rp (fix-true-list l))
	  (dag-nodes-aux x rp l))))

(local
 (defthm term-graph-p-fix-true-list
   (equal (term-graph-p (fix-true-list l))
	  (term-graph-p l))))



(local
 (defthm measure-rec-dag-fix-true-list
   (equal (measure-rec-dag flg h (fix-true-list l))
	  (measure-rec-dag flg h l))
   :hints (("Goal" :in-theory (enable measure-rec-dag)))))

(local
 (defthm dag-as-term-fix-true-list
  (equal (dag-as-term flg h (fix-true-list l))
	 (dag-as-term flg h l))))

(local
 (defthm dag-deref-fix-true-list
   (equal (dag-deref h (fix-true-list l))
	  (dag-deref h l))))

(local
 (defthm well-formed-term-dag-p-fix-true-list
   (equal (well-formed-term-dag-p (fix-true-list g))
	  (well-formed-term-dag-p g))))

(local
 (defthm well-formed-extended-upl-fix-true-list
   (and (equal
	 (well-formed-extended-upl
	  (list S U (fix-true-list g) stamp time))
	 (well-formed-extended-upl (list S U g stamp time)))
	(equal
	 (well-formed-extended-upl
	  (list S U g (fix-true-list stamp) time))
	 (well-formed-extended-upl (list S U g stamp time))))
   :hints (("Goal" :in-theory (enable well-formed-extended-upl)))))


(local
 (defthm ext-upl-occur-check-invariant-fix-true-list
   (and (equal (ext-upl-occur-check-invariant
		(list S U (fix-true-list g) stamp time))
	       (ext-upl-occur-check-invariant
		(list S U g stamp time)))
	(equal (ext-upl-occur-check-invariant
		(list S U g (fix-true-list stamp) time))
	       (ext-upl-occur-check-invariant
		(list S U g stamp time))))
   :hints (("Goal" :in-theory (enable ext-upl-occur-check-invariant)))))


(local
 (defthm equations-already-solved-fix-true-list
   (equal (equations-already-solved
	   l1 l2 (fix-true-list g))
	  (equations-already-solved
	   l1 l2 g))))


(local
 (defthm remaining-id-stacks-invariant-aux-fix-true-list
   (equal (remaining-id-stacks-invariant-aux
	   rargs1 rargs2 requations id-equ (fix-true-list g))
	  (remaining-id-stacks-invariant-aux
	   rargs1 rargs2 requations id-equ g))))


(local
 (defthm iter-remaining-id-stacks-invariant-fix-true-list
   (equal (iter-remaining-id-stacks-invariant id-equ id-stack-list
					      (fix-true-list g))
	  (iter-remaining-id-stacks-invariant id-equ id-stack-list g))))

(local (defthm first-id-stack-invariant-aux-with-equations-fix-true-list
	 (equal (first-id-stack-invariant-aux-with-equations
		 rargs1 rargs2 requations (fix-true-list g))
		(first-id-stack-invariant-aux-with-equations
		 rargs1 rargs2 requations g))))
(local
 (defthm ext-upl-id-invariant-fix-true-list
   (and (equal (ext-upl-id-invariant
		(list S U (fix-true-list g) stamp time))
	       (ext-upl-id-invariant
		(list S U g stamp time)))
	(equal (ext-upl-id-invariant
		(list S U g (fix-true-list stamp) time))
	       (ext-upl-id-invariant
		(list S U g stamp time))))
   :hints (("Goal" :in-theory (enable ext-upl-id-invariant)))))



(local
 (defthm unification-invariant-q-fix-true-list
   (and (equal (unification-invariant-q
		(list S U (fix-true-list g) stamp time))
	       (unification-invariant-q
		(list S U g stamp time)))
	(equal (unification-invariant-q
		(list S U g (fix-true-list stamp) time))
	       (unification-invariant-q
		(list S U g stamp time))))
   :hints (("Goal" :in-theory (enable unification-invariant-q)))))




(local (in-theory (enable nth)))

;;;============================================================================
;;;
;;; 3) Definition of the algorithm
;;;
;;;============================================================================


;;;
;;; 3.1 Viewing graphs as first--order terms
;;;

;;;   In this section we define how the graphs stored in @terms-dag@ can be
;;; seen as first--order terms.  Note the
;;; use of "defexec" and "mbe" in order to associate more efficient executable bodies to the
;;; functions.

;;; The term (or list of terms) pointed by an index:



(defexec dag-as-term-st (flg h terms-dag)
  (declare
   (xargs
    :stobjs terms-dag
    :guard (and (if flg (and (natp h) (< h (dag-length terms-dag)))
		  (bounded-nat-true-listp h (dag-length terms-dag)))
		(well-formed-term-dag-p (dag-component-st terms-dag))))
   (exec-xargs
    :measure (measure-rec-dag flg h
					 (dag-component-st
					  terms-dag))))
  (mbe
   :logic
   (dag-as-term flg h (dag-component-st terms-dag))
   :exec
   (if flg
       (let ((p (dagi h terms-dag)))
	 (if (dag-bound-p p)
	     (dag-as-term-st flg p terms-dag)
	   (let ((args (dag-args p))
		 (symb (dag-symbol p)))
	     (if (equal args t)
		 symb
	       (cons symb (dag-as-term-st nil args terms-dag))))))
     (if (endp h)
	 h
       (cons (dag-as-term-st t (car h) terms-dag)
	     (dag-as-term-st nil (cdr h) terms-dag))))))




;;;
;;; 3.2) Dereferencing a pointer:
;;;

(defexec dag-deref-st (h terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (natp h) (< h (dag-length terms-dag))
			      (term-graph-p (dag-component-st terms-dag))
			      (dag-p (dag-component-st terms-dag))))
	   (exec-xargs :measure (measure-rec-dag t h (dag-component-st terms-dag))))
  (mbe
   :logic (dag-deref h (dag-component-st terms-dag))
   :exec
   (let ((p (dagi h terms-dag)))
     (if (dag-bound-p p) (dag-deref-st p terms-dag) h)))
   )


;;;----------------------------------------------------------------------------
;;;
;;; 1.2) Occur check:
;;;
;;;----------------------------------------------------------------------------

(defun all-marks-integers (stamp)
  (declare (xargs :guard (true-listp stamp)))
  (cond ((endp stamp) t)
	(t (and (integerp (car stamp))
		(all-marks-integers (cdr stamp))))))

(local
 (defthm all-marks-integers-fix-true-list
   (equal (all-marks-integers (fix-true-list l))
	  (all-marks-integers l))))


(local
 (defthm all-marks-integers-all-marks-integers-less-than-time
   (implies (all-marks-integers-less-than-time stamp time)
	    (all-marks-integers stamp))))


(defun occur-check-st (flg x h terms-dag time)
  (declare (xargs :measure (measure-rec-dag flg h (terms-dag-dag
						   terms-dag))
		  :hints (("Goal" :in-theory (disable nth)))
		  :stobjs terms-dag
		  :verify-guards nil
		  :guard (and (natp x) (integerp time)
			      (equal (stamp-length terms-dag)
				     (dag-length terms-dag))
			      (if flg
				  (and (natp h) (< h (dag-length terms-dag)))
				  (bounded-nat-true-listp
				   h (dag-length terms-dag)))
			      (all-marks-integers (stamp-component-st terms-dag))
			      (well-formed-term-dag-p (dag-component-st terms-dag)))))
  (mbe
   :logic
   (if (dag-p (dag-component-st terms-dag))
       (if flg
	   (let ((p (dagi h terms-dag)))
	     (if (dag-bound-p p)
		 (occur-check-st flg x p terms-dag time)
		 (let ((args (dag-args p)))
		   (cond ((equal args t) (mv (= x h) terms-dag))
			 ((= (stampi h terms-dag) time) (mv nil terms-dag))
			 (t (mv-let
			     (bool terms-dag)
			     (occur-check-st nil x args terms-dag time)
			     (if bool
				 (mv bool terms-dag)
				 (let ((terms-dag
					(update-stampi h time terms-dag)))
				   (mv nil terms-dag)))))))))
	   (if (endp h)
	       (mv nil terms-dag)
	       (let ((temp (measure-rec-dag flg h (dag-component-st terms-dag))))
		 (mv-let (bool terms-dag)
			 (occur-check-st t x (car h) terms-dag time)
			 (if bool
			     (mv bool terms-dag)
			     (if (o<
				  (measure-rec-dag nil (cdr h) (dag-component-st terms-dag))
				  temp)
				 (occur-check-st nil x (cdr h) terms-dag time)
			       (mv 'undef terms-dag)))))))
     (mv 'undef terms-dag))
   :exec
   (if flg
       (let ((p (dagi h terms-dag)))
	 (if (dag-bound-p p)
	     (occur-check-st flg x p terms-dag time)
	     (let ((args (dag-args p)))
	       (cond ((equal args t) (mv (= x h) terms-dag))
		     ((= (stampi h terms-dag) time) (mv nil terms-dag))
		     (t (mv-let (bool terms-dag)
				(occur-check-st nil x args terms-dag time)
				(if bool
				    (mv bool terms-dag)
				    (let ((terms-dag
					   (update-stampi h time terms-dag)))
				      (mv nil terms-dag)))))))))
       (if (endp h)
	   (mv nil terms-dag)
	   (mv-let (bool terms-dag)
		   (occur-check-st t x (car h) terms-dag time)
		   (if bool
		       (mv bool terms-dag)
		       (occur-check-st nil x (cdr h) terms-dag time)))))))


(encapsulate
 ()

 (local
  (defthm update-nth-1-atom-terms-dag-very-ugly-lemma
    (implies (atom terms-dag)
 	     (not (car (update-nth 1 x terms-dag))))
    :hints (("Goal" :expand (update-nth 1 x terms-dag)))))


 (defthm occur-check-st-does-not-modify-terms-dag-graph
   (equal (terms-dag-dag
	   (second (occur-check-st flg x h terms-dag time)))
	  (terms-dag-dag terms-dag)))

 (local
  (defthm all-marks-integers-update-nth
    (implies (and (all-marks-integers stamp)
		  (integerp time)
		  (natp h)
		  (< h (len stamp)))
	     (all-marks-integers (update-nth h time stamp)))))

  (local
   (defthm all-marks-integers-nth-acl2-numberp
     (implies (and (all-marks-integers stamp)
 		  (natp h)
 		  (< h (len stamp)))
 	     (acl2-numberp (nth h stamp)))
     :hints (("Goal" :in-theory (enable nth)))))

 (local
  (defthm all-marks-integers-and-length-stamp-preserved-by-occur-check-st
    (implies (and
	      (equal (stamp-length terms-dag) (dag-length terms-dag))
	      (if flg
		  (and (natp h) (< h (dag-length terms-dag)))
		(bounded-nat-true-listp
		 h (dag-length terms-dag)))
	      (well-formed-term-dag-p (terms-dag-dag terms-dag))
	      (integerp time)
	      (all-marks-integers (terms-dag-stamp terms-dag)))
	     (and
	      (all-marks-integers (terms-dag-stamp (second (occur-check-st
							    flg x h
							    terms-dag
							    time))))
	      (equal (len (nth 1 (second (occur-check-st
					  flg x h
					  terms-dag
					  time))))
		     (dag-length terms-dag))))
    :hints (("Goal" :in-theory (enable nth-update-nth)))))

 (verify-guards occur-check-st)


 (defthm equal-occur-check-st-occur-check-q
   (and (equal (terms-dag-stamp
		(second (occur-check-st flg x h terms-dag time)))
	       (second (occur-check-q flg x h
				      (terms-dag-dag terms-dag)
				      (terms-dag-stamp terms-dag) time)))
	(equal (first (occur-check-st flg x h terms-dag time))
	       (first (occur-check-q flg x h
				     (terms-dag-dag terms-dag)
				     (terms-dag-stamp terms-dag) time))))
   :hints (("Goal" :in-theory (enable nth-update-nth)
	    :induct (occur-check-st flg x h terms-dag time)))))


(in-theory (disable occur-check-st))

;; #|
;; ;;; They are in q-dag-unification
;; ;;;   A function for pairing arguments of functions:

;; (defun pair-args (l1 l2)
;;   (cond ((endp l1) (if (equal l1 l2) (mv nil t) (mv nil nil)))
;; 	((endp l2) (mv nil nil))
;; 	(t (mv-let (pair-rest bool)
;; 		   (pair-args (cdr l1) (cdr l2))
;; 		   (if bool
;; 		       (mv (cons (cons (car l1) (car l2))
;; 				 pair-rest)
;; 			   t)
;; 		     (mv nil nil))))))
;; |#

;;;----------------------------------------------------------------------------
;;;
;;; 1.3) One step of transformation
;;;
;;;----------------------------------------------------------------------------

;;;   One step of transformation. This implements one step of the well-known
;;; transformation rules of Martelli and Montanari, acting on the dag
;;; representation of the unification problem. Note the use of
;;; "identification marks" of
;;; the form (id h1 h2) meaning that unification of h1 and h2 has already be
;;; solved, so nodes h1 and h2 can be identified and therefore redundant
;;; unifications are avoided.

;; Guards

(encapsulate
 ()

;;; Guards
 (local (defthm dag-deref-natp
	  (implies (and (dag-p g)
			(bounded-term-graph-p g n)
			(natp i) (< i n))
		   (and (<= 0 (dag-deref i g))
			(acl2-numberp (dag-deref i g))
			(integerp (dag-deref i g))))))

;;; Guards
 (local
   (defthm bounded-term-graph-p-consp
     (implies (and (not (consp (nth h g)))
		   (not (term-dag-is-p h g))
		   (nth h g))
	      (not (bounded-term-graph-p g n)))))

;;; Guards
 (local
  (defthm bounded-term-graph-p-eqlable-p-term-dag-symbol
    (implies (bounded-term-graph-p g n)
	     (eqlablep (term-dag-symbol h g)))))

;;; Guards
 (local
  (defthm bounded-term-graph-p-true-listp-term-dag-args
    (implies (and (bounded-term-graph-p g n)
		  (not (term-dag-variable-p h g)))
	     (true-listp (term-dag-args h g)))))



 (defun dag-transform-mm-st (S U terms-dag time)
   (declare (xargs :stobjs terms-dag
		   :guard-hints (("Goal" :in-theory (enable
						     unification-invariant-q
						      well-formed-extended-upl
						      ext-upl-occur-check-invariant)))
		   :guard (and (consp S)
			       (unification-invariant-q
				(list S U
				 (dag-component-st terms-dag)
				 (stamp-component-st terms-dag)
				 time)))))
   (let* ((ecu (car S))
	  (R (cdr S)))
     (if (equal (car ecu) 'id)
	 (let ((terms-dag (update-dagi (second ecu) (third ecu)
				       terms-dag)))
	   (mv R U t terms-dag time))
       (let* ((t1 (dag-deref-st (car ecu) terms-dag))
	      (t2 (dag-deref-st (cdr ecu) terms-dag))
	      (p1 (dagi t1 terms-dag))
	      (p2 (dagi t2 terms-dag)))
	 (cond
	  ((= t1 t2) (mv R U t terms-dag time))
	  ((dag-variable-p p1)
	   (mv-let (oc terms-dag)
		   (occur-check-st t t1 t2 terms-dag time)
		   (if oc
		       (mv nil nil nil terms-dag nil)
		     (let ((terms-dag (update-dagi t1 t2 terms-dag)))
		       (mv R (cons (cons (dag-symbol p1) t2) U) t
			   terms-dag (1+ time))))))
	  ((dag-variable-p p2)
	   (mv (cons (cons t2 t1) R) U t terms-dag time))
	  ((not (eql (dag-symbol p1) (dag-symbol p2)))
	   (mv nil nil nil terms-dag nil))
	  (t (mv-let (pair-args bool)
		     (pair-args (dag-args p1) (dag-args p2))
		     (if bool
			 (mv (append pair-args (cons (list 'id t1 t2) R))
			     U t terms-dag time)
		       (mv nil nil nil terms-dag nil))))))))))


;;; Este disable es importante, puesto que todas las reglas anteriores
;;; (y las que siguen)
;;; llevan nth en su lado izquierdo. Por tanto, sólo habilitaremos nth
;;; en caso de que sea estrictamente necesario.
(local (in-theory (disable nth)))


(local (in-theory (enable dag-transform-mm-q)))

(local
 (defthm  dag-transform-mm-st-first-component
   (equal (first (dag-transform-mm-st S U terms-dag time))
	  (first  (dag-transform-mm-q
		   (list S U (terms-dag-dag terms-dag)
			 (terms-dag-stamp terms-dag)
			 time))))))




(local
 (defthm  dag-transform-mm-st-second-component
   (equal (second (dag-transform-mm-st S U terms-dag time))
	  (second  (dag-transform-mm-q
		   (list S U (terms-dag-dag terms-dag)
			 (terms-dag-stamp terms-dag)
			 time))))))

(local
 (defthm  dag-transform-mm-st-third-component
   (iff (third (dag-transform-mm-st S U terms-dag time))
	 (dag-transform-mm-q
	  (list S U (terms-dag-dag terms-dag)
		(terms-dag-stamp terms-dag)
		time)))))

(local
 (defthm dag-transform-mm-st-fourth-component-dag
   (implies (third (dag-transform-mm-st S U terms-dag time))
	    (equal (terms-dag-dag
		    (fourth
		     (dag-transform-mm-st S U terms-dag time)))
		   (third
		    (dag-transform-mm-q
		     (list S U (terms-dag-dag terms-dag)
			   (terms-dag-stamp terms-dag)
			   time)))))))


(local
 (defthm dag-transform-mm-st-fourth-component-stamp
   (implies (third (dag-transform-mm-st S U terms-dag time))
	    (equal (terms-dag-stamp
		    (fourth
		     (dag-transform-mm-st S U terms-dag time)))
		   (fourth
		    (dag-transform-mm-q
		     (list S U (terms-dag-dag terms-dag)
			   (terms-dag-stamp terms-dag)
			   time)))))))



(local
 (defthm  dag-transform-mm-st-fifth-component
   (equal (fifth (dag-transform-mm-st S U terms-dag time))
	  (fifth  (dag-transform-mm-q
		   (list S U (terms-dag-dag terms-dag)
			 (terms-dag-stamp terms-dag)
			 time))))))


(local
 (defthm dag-transform-mm-q-components
   (implies (dag-transform-mm-q ext-upl)
	    (equal
	     (list (first (dag-transform-mm-q ext-upl))
		   (second (dag-transform-mm-q ext-upl))
		   (third  (dag-transform-mm-q ext-upl))
		   (fourth (dag-transform-mm-q ext-upl))
		   (fifth (dag-transform-mm-q ext-upl)))
	     (dag-transform-mm-q ext-upl)))))


(local (in-theory (disable dag-transform-mm-st dag-transform-mm-q)))




;;;----------------------------------------------------------------------------
;;;
;;; 1.4) Iterative application of transformations
;;;
;;;----------------------------------------------------------------------------



;;; Guards

(local
 (defthm dag-transform-mm-q-preserves-true-listp-system-of-equations
   (implies
    (and (true-listp S)
	 (consp S))

    (true-listp (car (dag-transform-mm-q (list S U g stamo
					       time)))))
   :hints (("Goal" :in-theory (enable dag-transform-mm-q)))))



(defexec solve-upl-st (S U terms-dag time)
  (declare (xargs :stobjs terms-dag
		  :guard (and (true-listp S)
			      (unification-invariant-q
			       (list S U
				     (dag-component-st terms-dag)
				     (stamp-component-st terms-dag)
				     time)))
		  :measure (unification-measure-q
			    (list S U
				  (terms-dag-dag terms-dag)
				  (terms-dag-stamp terms-dag)
				  time)))
	   (exec-xargs
	    :default-value (mv nil nil nil terms-dag nil)))
  (mbe
   :logic
   (if (unification-invariant-q
	(list S U (dag-component-st terms-dag) (stamp-component-st terms-dag) time))
       (if (endp S)
	   (mv S U t terms-dag time)
	   (mv-let (S1 U1 bool terms-dag time1)
		   (dag-transform-mm-st S U terms-dag time)
		   (if bool
		       (solve-upl-st S1 U1 terms-dag time1)
		       (mv S U nil terms-dag time))))
       (mv S U nil terms-dag time))
   :exec
   (if (endp S)
       (mv S U t terms-dag time)
       (mv-let (S1 U1 bool terms-dag time1)
	       (dag-transform-mm-st S U terms-dag time)
	       (if bool
		   (solve-upl-st S1 U1 terms-dag time1)
		   (mv S U nil terms-dag time))))))



(local
 (defthm  solve-upl-st-st-first-component
   (implies (third (solve-upl-st S U terms-dag time))
	    (equal (first (solve-upl-st S U terms-dag time))
		   (first  (solve-upl-q
			    (list S U (terms-dag-dag terms-dag)
				  (terms-dag-stamp terms-dag) time)))))))



(local
 (defthm  solve-upl-st-st-second-component
   (implies (third (solve-upl-st S U terms-dag time))
	    (equal (second (solve-upl-st S U terms-dag time))
		   (second  (solve-upl-q
			     (list S U (terms-dag-dag terms-dag)
				   (terms-dag-stamp terms-dag) time)))))))




(local
 (defthm solve-upl-st-third-component
   (iff (third (solve-upl-st S U terms-dag time))
	(solve-upl-q
	 (list S U (terms-dag-dag terms-dag)
	       (terms-dag-stamp terms-dag) time)))))


(local
 (defthm  solve-upl-st-fourth-component-dag
   (implies (third (solve-upl-st S U terms-dag time))
	    (equal (terms-dag-dag
		    (fourth (solve-upl-st S U terms-dag time)))
		   (third (solve-upl-q
			   (list S U (terms-dag-dag terms-dag)
				 (terms-dag-stamp terms-dag)
				 time)))))))



(local
 (defthm  solve-upl-st-fourth-component-stamp
   (implies (third (solve-upl-st S U terms-dag time))
	    (equal (terms-dag-stamp
		    (fourth (solve-upl-st S U terms-dag time)))
		   (fourth (solve-upl-q
			   (list S U (terms-dag-dag terms-dag)
				 (terms-dag-stamp terms-dag)
				 time)))))))


(local
 (defthm  solve-upl-st-st-fifth-component
   (implies (third (solve-upl-st S U terms-dag time))
	    (equal (fifth (solve-upl-st S U terms-dag time))
		   (fifth  (solve-upl-q
			     (list S U (terms-dag-dag terms-dag)
				   (terms-dag-stamp terms-dag) time)))))))


(local (in-theory (disable solve-upl-st solve-upl-q)))


;;; Let us define the well-formedness condition for the initial indices
;;; systems and terms-dag


(defun initial-stamp-p (stamp n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (equal stamp nil)
    (and
     (consp stamp)
     (equal (car stamp) -1)
     (initial-stamp-p (cdr stamp) (- n 1)))))



(defun well-formed-dag-system-st (S terms-dag)
  (declare (xargs :stobjs terms-dag :guard t))
  (well-formed-upl (list S nil (dag-component-st terms-dag))))

;;; I have removed this:
;       (initial-stamp-p (stamp-component-st terms-dag) (dag-length
;							terms-dag))))


;;;   Starting with the empty substitution:

;;; Guards
(local
 (defthm bounded-nat-pairs-true-listp-true-listp
   (implies (bounded-nat-pairs-true-listp S n)
	    (true-listp S))))

;;; Guards
(local
 (defthm
   bounded-nat-pairs-true-listp-with-ids-bounded-nat-pairs-true-listp
   (implies (bounded-nat-pairs-true-listp l n)
	    (bounded-nat-pairs-true-listp-with-ids l n))))





(local
 (defthm bounded-nat-pairs-true-listp-preserved-by-after-first-id
   (implies  (bounded-nat-pairs-true-listp l n)
	     (bounded-nat-pairs-true-listp (after-first-id l) n))))


(local
 (defthm
   bounded-nat-pairs-true-listp-not-consp-split-extended-system-in-id-stacks
   (implies (bounded-nat-pairs-true-listp s n)
	    (not (consp (split-extended-system-in-id-stacks s))))))


(local
 (defthm all-marks-integers-less-than-time-initial-stamp-p
   (implies (initial-stamp-p (fix-true-list l) n)
	    (all-marks-integers-less-than-time l 0))
   :hints (("Goal" :induct (nth n l)
	    :in-theory (enable nth)))))


(local
 (defthm initial-stamp-p-equal-length
   (implies (and (initial-stamp-p (fix-true-list l) n)
		 (natp n))
	    (equal (equal n (len l)) t))
   :hints (("Goal" :induct (nth n l)
	    :in-theory (enable nth)))))


;;;; An the definition:


(defun dag-mgs-st (S terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (well-formed-dag-system-st S terms-dag)
			      (initial-stamp-p (stamp-component-st terms-dag) (dag-length
							terms-dag)))
		  :guard-hints
		  (("Goal" :in-theory (enable
				       unification-invariant-q
				       well-formed-extended-upl
				       well-formed-upl
				       ext-upl-id-invariant
				       ext-upl-occur-check-invariant)))))
  (mv-let (S1 sol bool terms-dag time1)
	  (solve-upl-st S nil terms-dag 0)
	  (declare (ignore S1 time1))
	  (mv sol bool terms-dag)))


(local (in-theory (enable dag-mgs-q)))

(local
 (defthm initial-stamp-p-initial-stamp-main-property
   (iff (initial-stamp-p l n)
	(equal (initial-stamp n) l))))

(local
 (defthm dag-mgs-st-dag-mgs-q-iff
   (implies (initial-stamp-p (terms-dag-stamp terms-dag)
			     (dag-length terms-dag))
	    (iff (second (dag-mgs-st S terms-dag))
		 (dag-mgs-q S (terms-dag-dag terms-dag))))))

(local
 (defthm dag-mgs-st-dag-mgs-q-first
   (implies (and (second (dag-mgs-st S terms-dag))
		 (initial-stamp-p (terms-dag-stamp terms-dag)
				  (dag-length terms-dag)))
	    (equal (first (dag-mgs-st S terms-dag))
		   (second (dag-mgs-q S (terms-dag-dag terms-dag)))))))

(local
 (defthm dag-mgs-st-dag-mgs-q-third-dag
   (implies (and (second (dag-mgs-st S terms-dag))
		 (initial-stamp-p (terms-dag-stamp terms-dag)
				  (dag-length terms-dag)))
	    (equal (terms-dag-dag (third (dag-mgs-st S terms-dag)))
		   (third (dag-mgs-q S (terms-dag-dag terms-dag)))))))

(local
 (defthm dag-mgs-st-dag-mgs-q-third-stamp
   (implies (and (second (dag-mgs-st S terms-dag))
		 (initial-stamp-p (terms-dag-stamp terms-dag)
				  (dag-length terms-dag)))
	    (equal (terms-dag-stamp (third (dag-mgs-st S terms-dag)))
		   (fourth (dag-mgs-q S (terms-dag-dag terms-dag)))))))

(local (in-theory (disable dag-mgs-st dag-mgs-q)))

;;;----------------------------------------------------------------------------
;;;
;;; 1.5) Properties of dag-mgs-st
;;;
;;;----------------------------------------------------------------------------


(defun tbs-as-system-st (S terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (bounded-nat-pairs-true-listp
			       S (dag-length terms-dag))
			      (well-formed-term-dag-p (dag-component-st terms-dag)))))
  (if (endp S)
      S
    (cons (cons (dag-as-term-st t (caar S) terms-dag)
		(dag-as-term-st t (cdar S) terms-dag))
	  (tbs-as-system-st (cdr S) terms-dag))))

(local
 (defthm equal-tbs-as-system-st-tbs-as-system
   (equal (tbs-as-system-st S terms-dag)
	  (tbs-as-system S (terms-dag-dag terms-dag)))))

(defun solved-as-system-st (sol terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (bounded-nat-substitution-p
			       sol (dag-length terms-dag))
			      (well-formed-term-dag-p (dag-component-st terms-dag)))))
  (if (endp sol)
      sol
      (cons (cons (caar sol) (dag-as-term-st t (cdar sol) terms-dag))
	    (solved-as-system-st (cdr sol) terms-dag))))

(local
 (defthm equal-solved-as-system-st-solved-as-system
   (equal (solved-as-system-st S terms-dag)
	  (solved-as-system S (terms-dag-dag terms-dag)))))

(in-theory (disable tbs-as-system-st solved-as-system-st))


;; Este función es solo para evitarme escribir:

(local
 (defun well-formed-dag-system-st-bis (S td)
   (and (bounded-nat-pairs-true-listp S (len (terms-dag-dag td)))
	(well-formed-term-dag-p (terms-dag-dag td))
	(initial-stamp-p (terms-dag-stamp td) (len (terms-dag-dag td))))))

(local (in-theory (enable well-formed-upl)))

(local
 (defthm dag-mgs-st-completeness
   (let ((S (tbs-as-system-st S-dag terms-dag)))
     (implies (and (well-formed-dag-system-st-bis S-dag terms-dag)
		   (solution sigma S))
	      (second (dag-mgs-st S-dag terms-dag))))))

(local
 (defthm dag-mgs-st-soundness
   (let* ((S (tbs-as-system-st S-dag terms-dag))
	  (dag-mgs-st (dag-mgs-st S-dag terms-dag))
	  (unifiable (second dag-mgs-st))
	  (sol (solved-as-system-st (first dag-mgs-st)
				    (third dag-mgs-st))))
     (implies (and (well-formed-dag-system-st-bis S-dag terms-dag)
		   unifiable)
	      (solution sol S)))))

(local
 (defthm dag-mgs-st-idempotent
   (let* ((dag-mgs-st (dag-mgs-st S-dag terms-dag))
	  (unifiable (second dag-mgs-st))
	  (sol (solved-as-system-st (first dag-mgs-st)
				    (third dag-mgs-st))))
     (implies (and (well-formed-dag-system-st-bis S-dag terms-dag)
		   unifiable)
	      (idempotent sol)))
   :hints (("Goal" :in-theory (disable idempotent)))))

(local
 (defthm dag-mgs-st-most-general-solution
   (let* ((S (tbs-as-system-st S-dag terms-dag))
	  (dag-mgs-st (dag-mgs-st S-dag terms-dag))
	  (sol (solved-as-system-st (first dag-mgs-st)
				    (third dag-mgs-st))))
     (implies (and (well-formed-dag-system-st-bis S-dag terms-dag)
		   (solution sigma S))
	      (subs-subst sol sigma)))))

;;;;(local (in-theory (disable well-formed-upl)))

;;;----------------------------------------------------------------------------
;;;
;;; 1.6) Input processing
;;;
;;;----------------------------------------------------------------------------

;;;   We now define a function that acts as an "user interface", allowing to
;;; write the input terms in the standard prefix list representation.


;;;   Storing term as directed acyclicic graphs in the stobj

(defun term-as-dag-aux-st (flg term terms-dag h variables)
  (declare (xargs :stobjs terms-dag
		  :verify-guards nil
		  :guard (and (term-graph-p (dag-component-st terms-dag))
			      (natp h)
			      (term-p-aux flg term)
			      (<= (+ h (length-term flg term))
				  (dag-length terms-dag))
			      (bounded-nat-substitution-p
			       variables (dag-length terms-dag)))))
  (if flg
      (if (variable-p term)
	  (let* ((bound (assoc term variables))
		 (terms-dag
		  (update-dagi h (if bound (cdr bound) (cons term t))
			       terms-dag))
		 (new-variables
		  (if bound variables (acons term h variables))))
	    (mv terms-dag (1+ h) nil new-variables))
	(mv-let (terms-dag h1 hsl var1)
		(term-as-dag-aux-st
		 nil (cdr term) terms-dag (1+ h) variables)
		(let* ((terms-dag
			(update-dagi h (cons (car term) hsl) terms-dag)))
		  (mv terms-dag h1 nil var1))))
    (if (endp term)
	(mv terms-dag h term variables)
      (mv-let (terms-dag hcar ign varcar)
	      (term-as-dag-aux-st t (car term) terms-dag h variables)
	      (declare (ignore ign))
	      (mv-let (terms-dag hcdr hsl varcdr)
		      (term-as-dag-aux-st
		       nil (cdr term) terms-dag hcar varcar)
		      (mv terms-dag hcdr (cons h hsl) varcdr))))))

;;; Some lemmas:
(local
 (defthm term-as-dag-aux-st-does-not-modify-stamp
   (equal (terms-dag-stamp
	   (first (term-as-dag-aux-st flg term terms-dag h variables)))
	  (terms-dag-stamp terms-dag))
   :hints (("Goal" :in-theory (enable nth)))))


(local
 (defthm term-as-dag-aux-st-consp
   (consp (term-as-dag-aux-st flg term terms-dag h variables))))

(local
 (defthm term-as-dag-aux-st-car-consp
   (implies (consp term)
	    (consp (first (term-as-dag-aux-st flg term terms-dag h var))))))



(local
 (defthm term-as-dag-aux-st-term-as-dag-aux
   (and
    (equal (terms-dag-dag
	    (first (term-as-dag-aux-st flg term terms-dag h variables)))
	   (first (term-as-dag-aux
		   flg term (terms-dag-dag terms-dag) h variables)))
    (equal (second (term-as-dag-aux-st flg term terms-dag h variables))
	   (second (term-as-dag-aux
		    flg term (terms-dag-dag terms-dag) h variables)))
    (equal (third (term-as-dag-aux-st flg term terms-dag h variables))
	   (third (term-as-dag-aux
		   flg term (terms-dag-dag terms-dag) h variables)))
    (equal (fourth (term-as-dag-aux-st flg term terms-dag h variables))
	   (fourth (term-as-dag-aux
		    flg term (terms-dag-dag terms-dag) h variables))))
   ))



;;; Guard verification

(local
 (defthm bounded-nat-substitution-p-assoc-consp
   (implies (and (bounded-nat-substitution-p alist n)
		 (assoc x alist))
	    (consp (assoc x alist)))))

(local
 (defthm bounded-nat-substitution-p-alistp
   (implies (bounded-nat-substitution-p alist n)
	    (alistp alist))))

(verify-guards term-as-dag-aux-st
	       :hints (("Goal" :in-theory (disable term-graph-p))))



(defun term-as-dag-st (term terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (term-graph-p (dag-component-st terms-dag))
			      (term-p term)
			      (<= (length-term t term)
				  (dag-length terms-dag)))))
  (mv-let (terms-dag h hs var)
	  (term-as-dag-aux-st t term terms-dag 0 nil)
	  (declare (ignore h hs var))
	  terms-dag))
(local
 (defthm term-as-dag-st-term-as-dag-main-property
   (equal (terms-dag-dag (term-as-dag-st term terms-dag))
	  (term-as-dag term (terms-dag-dag terms-dag)))
   :hints (("Goal" :in-theory (enable term-as-dag)))))


(local
 (defthm term-as-dag-st-does-not-modify-stamp
   (equal (terms-dag-stamp (term-as-dag-st term terms-dag))
	  (terms-dag-stamp terms-dag))))


(local (in-theory (disable term-as-dag-st)))




;;; Cambiarlo de sitio!!
(local
 (defthm empty-graph-p-fix-true-list
   (equal (empty-graph-p (fix-true-list l))
	  (empty-graph-p l))))


;;;    Building a unification problem for two given terms:




(local
 (defthm len-resize-list
   (implies (and (integerp n) (> n 0))
	    (equal (len (resize-list lst n v)) n))
   :hints (("Goal" :induct (resize-list lst n v)))))

(defun unif-two-terms-problem-st (t1 t2 terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (term-p t1) (term-p t2)
			      (empty-graph-p (dag-component-st terms-dag)))))
  (let* ((size (+ (length-term t t1) (length-term t t2) 1))
	 (terms-dag (resize-dag size terms-dag))
	 (terms-dag (resize-stamp size terms-dag)))
    (term-as-dag-st (list 'equ t1 t2) terms-dag)))

(local
 (defthm resize-list-initial-stamp
   (implies (atom l)
	    (equal (resize-list l n -1)
		   (initial-stamp n)))))



(local
 (defthm len-terms-dag-dag-term-as-dag
   (implies (and (<= (length-term t term) (len g))
		 (term-p-aux t term)
		 (term-graph-p g))
	    (equal (len (term-as-dag term g))
		   (len g)))
   :hints (("Goal" :in-theory (enable term-as-dag)))))

(local
 (defthm bounded-term-graph-p-resize-list
   (implies (atom l)
	    (bounded-term-graph-p (resize-list l n nil) m))))



(local
 (defthm unif-two-terms-problem-st-unif-two-terms-problem-stamp
   (implies (and (term-p t1) (term-p t2)
		 (empty-graph-p (terms-dag-dag terms-dag))
		 (atom (terms-dag-stamp terms-dag)))
	    (equal (terms-dag-stamp (unif-two-terms-problem-st t1 t2 terms-dag))
		   (initial-stamp (dag-length (unif-two-terms-problem-st
					       t1 t2 terms-dag)))))
   :hints (("Goal" :in-theory (disable resize-list initial-stamp)))))


(local
 (defthm unif-two-terms-problem-st-unif-two-terms-problem-dag
   (equal (terms-dag-dag (unif-two-terms-problem-st t1 t2 terms-dag))
	  (unif-two-terms-problem t1 t2 (terms-dag-dag terms-dag )))
   :hints (("Goal" :in-theory (enable  unif-two-terms-problem nth)))))



(in-theory (disable unif-two-terms-problem-st))



;;;     the initial system to be solved:

(defun initial-to-be-solved-st (terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (< 0 (dag-length terms-dag))
			      (consp (dagi 0 terms-dag))
			      (consp (cdr (dagi 0 terms-dag)))
			      (consp (cddr (dagi 0 terms-dag))))))
  (list (cons (first (cdr (dagi 0 terms-dag)))
	      (second (cdr (dagi 0 terms-dag))))))



(local
  (defthm initial-to-be-solved-st-initial-to-be-solved
    (equal (initial-to-be-solved-st terms-dag)
 	  (initial-to-be-solved (terms-dag-dag terms-dag)))))

(local (in-theory (disable initial-to-be-solved-st)))



;;;----------------------------------------------------------------------------
;;;
;;; 1.7) The unification algorithm (with input stobj)
;;;
;;;----------------------------------------------------------------------------

;;;   Now we can compose the "interface" program with the unification program
;;; and the "output" program.

;;;   Applying the transformations to the graph initially built with two given
;;; terms:


;;; I don't know why, but the following theorem has an important
;;; slowdown, partially fixed disabling the rules about mv-nth..:

;;; guard verification
(local
 (defthm several-properties-term-as-dag-l-on-initial-problem
   (and (consp (first (term-as-dag (list 'equ t1 t2) g)))
	(consp (cdr (first (term-as-dag (list 'equ t1 t2) g))))
	(consp (cddr (first (term-as-dag (list 'equ t1 t2) g)))))
   :hints (("Goal" :in-theory (e/d (term-as-dag)
				   (mv-nth-0-first
				    mv-nth-1-second
				    mv-nth-2-third
				    mv-nth-3-fourth)
				   )))))


;;; Guards
(local
 (defthm unif-two-terms-problem-several-properties
   (and (consp (unif-two-terms-problem t1 t2 g))
	(consp (first (unif-two-terms-problem t1 t2 g)))
	(consp (cdr (first (unif-two-terms-problem t1 t2 g))))
	(consp (cddr (first (unif-two-terms-problem t1 t2 g)))))))

;;; Cambiarlo de sitio!!!
(local
 (defthm well-formed-upl-fix-true-list
   (equal (well-formed-upl (list S U (fix-true-list g)))
	  (well-formed-upl (list S U g)))))


;;; Guards
(local
 (defthm atom-fix-true-list
   (iff (fix-true-list l) (consp l))))

(local
 (defthm initial-stamp-fix-true-list
   (equal (fix-true-list (initial-stamp n))
	  (initial-stamp n))))

(defun dag-mgu-st (t1 t2 terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard-hints (("Goal"
				 :in-theory (e/d (nth)
						 (initial-to-be-solved
						  well-formed-upl
						  unif-two-terms-problem))))
		  :guard (and (term-p t1) (term-p t2)
			      (empty-graph-p (dag-component-st
					      terms-dag))
			      (null (stamp-component-st terms-dag)))))
  (let ((terms-dag (unif-two-terms-problem-st t1 t2 terms-dag)))
    (dag-mgs-st (initial-to-be-solved-st terms-dag) terms-dag)))

(local
 (defthm dag-mgu-st-dag-mgu-q-iff
   (implies (and (empty-graph-p  (terms-dag-dag terms-dag))
		 (atom (terms-dag-stamp terms-dag))
		 (term-p t1) (term-p t2))
	    (iff (second (dag-mgu-st t1 t2 terms-dag))
		 (dag-mgu-q t1 t2 (terms-dag-dag terms-dag))))))

(local
 (defthm dag-mgu-st-dag-mgu-q-sol
   (implies (and (empty-graph-p (terms-dag-dag terms-dag))
		 (atom (terms-dag-stamp terms-dag))
		 (term-p t1) (term-p t2)
		 (second (dag-mgu-st t1 t2 terms-dag)))
	    (equal (first (dag-mgu-st t1 t2 terms-dag))
		   (second (dag-mgu-q t1 t2 (terms-dag-dag terms-dag)))))))

(local
 (defthm dag-mgu-st-dag-mgu-q-graph
   (implies (and (empty-graph-p (terms-dag-dag terms-dag))
		 (atom (terms-dag-stamp terms-dag))
		 (term-p t1) (term-p t2)
		 (second (dag-mgu-st t1 t2 terms-dag)))
	    (equal (terms-dag-dag (third (dag-mgu-st t1 t2 terms-dag)))
		   (third (dag-mgu-q t1 t2 (terms-dag-dag terms-dag)))))))

(local (in-theory (disable dag-mgu-st dag-mgu-q)))

;;;----------------------------------------------------------------------------
;;;
;;; 1.8) Properties of dag-mgu-st
;;;
;;;----------------------------------------------------------------------------

(local
 (defthm dag-mgu-st-completeness
   (implies (and (equal (instance t1 sigma)
			(instance t2 sigma))
		 (term-p t1) (term-p t2)
		 (empty-graph-p (terms-dag-dag terms-dag))
		 (atom (terms-dag-stamp terms-dag)))
	    (second (dag-mgu-st t1 t2 terms-dag)))))

(local
 (defthm dag-mgu-st-soundness
   (let* ((dag-mgu-st (dag-mgu-st t1 t2 terms-dag))
	  (sol (solved-as-system-st (first dag-mgu-st)
				    (third dag-mgu-st))))
     (implies (and (empty-graph-p (terms-dag-dag terms-dag))
		   (atom (terms-dag-stamp terms-dag))
		   (term-p t1) (term-p t2)
		   (second dag-mgu-st))
	      (equal (instance t1 sol) (instance t2 sol))))))

(local
 (defthm dag-mgu-st-most-general-solution
   (let* ((dag-mgu-st (dag-mgu-st t1 t2 terms-dag))
	  (sol (solved-as-system-st (first dag-mgu-st)
				    (third dag-mgu-st))))
     (implies (and (empty-graph-p (terms-dag-dag terms-dag))
		   (atom (terms-dag-stamp terms-dag))
		   (term-p t1) (term-p t2)
		   (equal (instance t1 sigma)
			  (instance t2 sigma)))
	      (subs-subst sol sigma)))))

(local
 (defthm dag-mgu-st-idempotent
   (let* ((dag-mgu-st (dag-mgu-st t1 t2 terms-dag))
	  (sol (solved-as-system-st (first dag-mgu-st)
				    (third dag-mgu-st))))
     (implies (and (empty-graph-p (terms-dag-dag terms-dag))
		   (atom (terms-dag-stamp terms-dag))
		   (term-p t1) (term-p t2)
		   (second dag-mgu-st))
	      (idempotent sol)))
   :hints (("Goal" :in-theory (disable idempotent)))))

;;;----------------------------------------------------------------------------
;;;
;;; 1.9) The unification algorithm (with a local stobj)
;;;
;;;----------------------------------------------------------------------------

(defun dag-mgu-aux-st (t1 t2 terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (term-p t1) (term-p t2)
			      (empty-graph-p (dag-component-st
					      terms-dag))
			      (null (stamp-component-st terms-dag)))
		  :guard-hints (("Goal"
				 :in-theory (e/d (nth)
						 (well-formed-term-dag-p-def))))))

  (mv-let (sol bool terms-dag)
	  (dag-mgu-st t1 t2 terms-dag)
	  (if bool
	      (let ((sol-l (solved-as-system-st sol terms-dag)))
		(mv t sol-l terms-dag))
	      (mv nil nil terms-dag))))


;;;    The unification algorithm, having the stobj as local.

(defun dag-mgu (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (with-local-stobj
   terms-dag
   (mv-let (bool sol terms-dag)
	   (dag-mgu-aux-st t1 t2 terms-dag)
	   (mv bool sol))))

;;;----------------------------------------------------------------------------
;;;
;;; 1.10) Properties of dag-mgu
;;;
;;;----------------------------------------------------------------------------

(local
 (in-theory (disable dag-mgu-st-dag-mgu-q-graph
		     dag-mgu-st-dag-mgu-q-sol
		     dag-mgu-st-dag-mgu-q-iff
		     equal-solved-as-system-st-solved-as-system)))

(defthm dag-mgu-completeness
  (implies (and (equal (instance t1 sigma)
		       (instance t2 sigma))
		(term-p t1) (term-p t2))
	   (first (dag-mgu t1 t2))))

(defthm dag-mgu-soundness
  (let* ((dag-mgu (dag-mgu t1 t2))
	 (unifiable (first dag-mgu))
	 (sol (second dag-mgu)))
    (implies (and (term-p t1) (term-p t2) unifiable)
	     (equal (instance t1 sol) (instance t2 sol)))))

(defthm dag-mgu-most-general-solution
  (let* ((dag-mgu (dag-mgu t1 t2))
	 (sol (second dag-mgu)))
  (implies (and (term-p t1) (term-p t2)
		(equal (instance t1 sigma) (instance t2 sigma)))
	   (subs-subst sol sigma))))

(defthm dag-mgu-idempotent
  (let* ((dag-mgu (dag-mgu t1 t2))
	 (sol (second dag-mgu)))
    (implies (and (term-p t1) (term-p t2))
	     (idempotent sol))))

;;;============================================================================
