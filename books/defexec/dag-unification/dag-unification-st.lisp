;;; ============================================================================
;;; dag-unification-st.lisp
;;; Título: A dag based unification algorithm using stobjs
;;; ============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "dag-unification-st")

|#

(in-package "ACL2")

(include-book "dag-unification-l")
(include-book "terms-dag-stobj")




;;; ============================================================================
;;;
;;; 0) Introducción
;;;
;;; ============================================================================

;;; In this book ({\tt dag-unification-st.lisp}) we present a
;;; unification algorithm on terms represented as directed acyclic
;;; graphs. These graphs are stored in the single threaded object {\tt
;;; terms-dag} (see {\tt terms-dag-stobj.lisp}). We have defined and
;;; verified a similar algorithm in the book {\tt
;;; dag-unification-l.lisp}. However, in that book we used lists to store
;;; term graphs. Now we use one stobj; that is, only one object storing
;;; the graph needs ever exists and updatings are done destructively
;;; instead of copying.


;;; From the logical perspective, a single-threaded object can be seen
;;; as an ordinary ACL2 object. In particular, the single--threaded
;;; object {\tt terms-dag} (see {\tt terms-dag-stobj.lisp}) can be seen
;;; as a unitary list containing an array. From the logical point of
;;; view this array is a list, so we can use the definitions and proved
;;; theorems given in {\tt dag-unification-l.lisp} to define and verify
;;; the same algorithm but now using the single--threaded object. Note
;;; that the algorithm naturally meets the restrictions needed when
;;; programming with stobjs.

;;; Having defined and verified the algorithm that uses lists, the
;;; algorithm that uses the stobj can be easily verified proving the
;;; corresponding "translation" theorems relating the list version to
;;; the stobj version. All these "translation" theorems have all the
;;; same form. Roughly speaking, they show that the list version
;;; of a function acting on the array component of the stobj computes
;;; the same result than the stobj version.

;;; As we pointed in the book {\tt dag-unification-l.lisp}, some of the
;;; functions here need some very expensive conditions (checking that we
;;; are dealing with directed acyclic graphs) in order to ensure their
;;; termination. Thus, the algorithm will not be practical for
;;; execution. To overcome this drawback, we use the "mbe" feature
;;; of ACL2 (see the ACL2 manual, version 2.8).


;;; The structure of this book is very simple. For every function of the
;;; algorithm defined using lists (see {\tt dag-unification-l.lisp}, we
;;; define an analogue function using the stobj and the corresponding
;;; "translation" theorem. These functions are of two types: functions
;;; describing well--formedness conditions ensuring termination and
;;; functions describing the algorithm. To execute the functions of the
;;; second type, we also define an executable body without the expensive
;;; check, using "mbe". We finally prove the main
;;; properties of the algorithm.

;;; The following books are used, and contain information that is
;;; relevant to understand the contents of this book:

;;; *)
;;; {\tt dag-unification-l.lisp}, where the unification algorithm on term
;;; dags using lists is defined and verified

;;; *)
;;; {\tt terms-as-dag.lisp}, where an algorithm to store first--order
;;; terms as dags (represented as a list) is defined and verified.

;;; *)
;;; {\tt terms-dag-stobj.lisp}, where the @terms-dag@ stobj is defined
;;; ans some useful theorems about it are proved.
;;; -)


;;; ============================================================================
;;;
;;; 1) Well--formedness conditions
;;;
;;; ============================================================================


;;; In this section we define conditions on the @terms-dag@ stobj
;;; ensuring termination of the unification algorithm. Note that every
;;; function is accompanied by the corresponding translation theorems,
;;; proving the correspondence between the "list" version and the
;;; "stobj" version.

;;; Definition of term graphs:

(defun term-graph-p-st (terms-dag)
  (declare (xargs :stobjs terms-dag))
  (term-graph-p (dag-component-st terms-dag)))


(local
 (defthm bounded-term-graph-p-fix-true-listp
   (equal (bounded-term-graph-p (fix-true-list g) n)
	  (bounded-term-graph-p g n))))


(local
 (defthm term-graph-p-fix-true-listp
   (equal (term-graph-p (fix-true-list g))
	  (term-graph-p g))))

(local
 (defthm term-graph-p-st-main-property
   (equal (term-graph-p-st terms-dag)
	  (term-graph-p (terms-dag-graph terms-dag)))))


(local
 (defthm quasi-term-graph-p-fix-true-listp
   (equal (quasi-term-graph-p (fix-true-list g))
	  (quasi-term-graph-p g))))


(in-theory (disable term-graph-p-st))

;;; Definition of variables of a term graph:



(defun list-of-term-dag-variables-st (terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (term-graph-p-st terms-dag)))
  (list-of-term-dag-variables
   (dag-component-st terms-dag)))

(local
 (defthm list-of-term-dag-variables-fix-true-listp
   (equal (list-of-term-dag-variables (fix-true-list g))
	  (list-of-term-dag-variables g))))


(local
 (defthm list-of-term-dag-variables-st-main-property
   (equal (list-of-term-dag-variables-st terms-dag)
	  (list-of-term-dag-variables (terms-dag-graph terms-dag)))))


(in-theory (disable list-of-term-dag-variables-st))


;;; Definition of neighbors:


(local
 (defthm quasi-term-graph-p-nth
   (implies (and (quasi-term-graph-p g)
		 (nth h g)
		 (not (consp (nth h g))))
	    (integerp (nth h g)))))


(defun neighbors-st (h terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (term-graph-p-st terms-dag)
			      (natp h)
			      (< h (dag-length terms-dag)))))
  (let ((ng (dagi h terms-dag)))
    (if (integerp ng)
	(list ng)
      (let ((ngs (cdr ng)))
	(if (equal ngs t) nil ngs)))))

(local
 (defthm equal-neighbors-st-neighbors
   (equal (neighbors-st h td)
	  (neighbors h (terms-dag-graph td)))))


;;; Needed for guard verification:
;;; These two are proved in {\tt dag-unification-rules.lisp}

;; (local
;;  (defthm bounded-term-graph-p-nth-property-1
;;    (implies (and (bounded-term-graph-p g n)
;; 		 (integerp (nth h g)))
;; 	    (<= 0 (nth h g)))
;;    :rule-classes :linear))


;; (local
;;  (defthm bounded-term-graph-p-nth-property-2
;;    (implies (and (bounded-term-graph-p g n)
;; 		 (integerp (nth h g)))
;; 	    (< (nth h g) n))))


(local
 (defthm bounded-term-graph-p-contents
   (implies (and (bounded-term-graph-p g n)
		 (not (term-dag-variable-p h g))
		 (not (term-dag-is-p h g)))
	    (bounded-nat-true-listp (term-dag-args h g) n))))




;;; Definition of directed acyclic graphs:


(defun dag-p-aux-st (hs rev-path terms-dag)
  (declare (xargs :measure (measure-dag-p hs rev-path (terms-dag-graph
						       terms-dag))
		  :hints (("Goal" :in-theory (disable neighbors
						      measure-dag-p
						      nfix)))
		  :stobjs terms-dag
		  :guard (and (bounded-nat-true-listp hs (dag-length terms-dag))
			      (true-listp rev-path)
			      (term-graph-p-st terms-dag))))

  (if (endp hs)
      t
    (let ((hs-car (nfix (car hs))))
      (if (member hs-car rev-path)
 	  nil
 	(and (dag-p-aux-st (neighbors-st (car hs) terms-dag)
 			(cons hs-car rev-path)
 			terms-dag)
 	     (dag-p-aux-st (cdr hs) rev-path terms-dag))))))



(local
 (defthm equal-dag-p-aux-st-dag-p-aux
   (equal (dag-p-aux-st hs rev-path td)
	  (dag-p-aux hs rev-path (terms-dag-graph td)))))

(in-theory (disable dag-p-aux-st))

;;; Guard verification

(local
 (defthm bounded-nat-listp-list-of-n
   (implies (<= m n)
	    (bounded-nat-true-listp (list-of-n m) n))
   :hints (("Goal" :in-theory (enable list-of-n)))))

(defun dag-p-st (terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (term-graph-p-st terms-dag)))
  (dag-p-aux-st (list-of-n (dag-length terms-dag)) nil terms-dag))

(local
 (defthm equal-dag-p-st-dag-p
   (equal (dag-p-st td)
	  (dag-p (terms-dag-graph td)))
   :hints (("Goal" :in-theory (enable dag-p)))))

(in-theory (disable dag-p-st))


;;; Definition of well-formed term dags:


(defun well-formed-term-dag-st-p (terms-dag)
  (declare (xargs :stobjs terms-dag))
  (and (term-graph-p-st terms-dag)
       (dag-p-st terms-dag)
       (no-duplicatesp (list-of-term-dag-variables-st terms-dag))))


(defthm well-formed-term-dag-st-p-main-property
  (equal (well-formed-term-dag-st-p terms-dag)
	 (well-formed-term-dag-p (terms-dag-graph terms-dag))))

(in-theory (disable well-formed-term-dag-st-p))


;;; Well--formed unification problems:

(defun well-formed-upl-st (S sol terms-dag)
  (declare (xargs :stobjs terms-dag))
  (and (bounded-nat-pairs-true-listp S (dag-length terms-dag))
       (bounded-nat-substitution-p sol (dag-length terms-dag))
       (well-formed-term-dag-st-p terms-dag)))

(local
 (defthm well-formed-upl-st-main-property
   (equal (well-formed-upl-st S sol terms-dag)
	  (well-formed-upl (list S sol (terms-dag-graph terms-dag))))
   :hints (("Goal" :in-theory (enable well-formed-upl)))))

(defun well-formed-dag-system-st (S terms-dag)
  (declare (xargs :stobjs terms-dag))
  (well-formed-upl-st S nil terms-dag))


(in-theory (disable well-formed-upl-st))


;;; ============================================================================
;;;
;;; 2) Viewing graphs as first--order terms
;;;
;;; ============================================================================

;;; In this section we define how the graphs stored in @terms-dag@ can
;;; be seen as first--order terms. As in the previous section, every
;;; function is accompanied by the corresponding translation theorems,
;;; proving the correspondence between the "list" version and the
;;; "stobj" version. Note the use of "mbe" in order to associate more
;;; efficient executable bodies to the functions.

;;; The term (or list of terms) pointed by an index:


(defun dag-as-term-st (flg h terms-dag)
  (declare (xargs :stobjs (terms-dag)
		  :measure (measure-rec-dag flg h
					    (terms-dag-graph terms-dag))
		  :hints (("Goal" :in-theory (disable nth)))
		  :guard (and (if flg
				  (and (natp h) (< h (dag-length
						      terms-dag)))
				(bounded-nat-true-listp h (dag-length
							   terms-dag)))
			      (well-formed-term-dag-st-p terms-dag))))

  (mbe
   :logic
   (if (dag-p-st terms-dag)
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
		 (dag-as-term-st nil (cdr h) terms-dag))))
     'undef)
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

(local
 (defthm equal-dag-as-term-st-dag-as-term-l
   (equal (dag-as-term-st flg h terms-dag)
	  (dag-as-term-l flg h (terms-dag-graph terms-dag)))
   :hints (("Goal" :in-theory (disable nth)))))


(in-theory (disable dag-as-term-st))


;;; The system of equations pointed by an indices system:

(defun tbs-as-system-st (S terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (bounded-nat-pairs-true-listp S (dag-length terms-dag))
			      (well-formed-term-dag-st-p terms-dag))))
  (if (endp S)
      S
    (cons (cons (dag-as-term-st t (caar S) terms-dag)
		(dag-as-term-st t (cdar S) terms-dag))
	  (tbs-as-system-st (cdr S) terms-dag))))

(local (in-theory (enable tbs-as-system)))

(local
 (defthm equal-tbs-as-system-st-tbs-as-system
   (equal (tbs-as-system-st S terms-dag)
	  (tbs-as-system S (terms-dag-graph terms-dag)))
   :hints (("Goal" :in-theory (disable nth)))))

(local (in-theory (disable tbs-as-system-st)))

;;; Ths substitution represented by an indices substitution:


(defun solved-as-system-st (sol terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (bounded-nat-substitution-p sol (dag-length terms-dag))
			      (well-formed-term-dag-st-p terms-dag))))
  (if (endp sol)
      sol
    (cons (cons (caar sol)
		(dag-as-term-st t (cdar sol) terms-dag))
	  (solved-as-system-st (cdr sol) terms-dag))))



(local
 (defthm equal-solved-as-system-st-solved-as-system
   (equal (solved-as-system-st S terms-dag)
	  (solved-as-system S (terms-dag-graph terms-dag)))
   :hints (("Goal" :in-theory (disable nth)))))


(in-theory (disable solved-as-system-st))


;;; Unification problems as term dags:

(defun upl-as-pair-of-systems-st (S sol bool terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and
			  (bounded-nat-pairs-true-listp S (dag-length terms-dag))
			  (bounded-nat-substitution-p sol (dag-length terms-dag))
			  (well-formed-term-dag-st-p terms-dag))))
  (if (not bool)
      nil
    (list (tbs-as-system-st S terms-dag)
	  (solved-as-system-st sol terms-dag))))


(local (in-theory (enable upl-as-pair-of-systems)))

(local
 (defthm equal-upl-as-pair-of-systems-st-upl-as-pair-of-systems
   (equal (upl-as-pair-of-systems-st S sol bool terms-dag)
	  (if (not bool)
	      nil
	    (upl-as-pair-of-systems (list S sol (terms-dag-graph
						 terms-dag)))))
   :hints (("Goal" :in-theory (disable nth)))))

(local (in-theory (disable upl-as-pair-of-systems)))

(in-theory (disable upl-as-pair-of-systems-st))


;;; ============================================================================
;;;
;;; 3) The unification algorithm
;;;
;;; ============================================================================

;;; In this section we define the unification algorithm. As in the
;;; previous section, every function is accompanied by the corresponding
;;; translation theorems, proving the correspondence between the "list"
;;; version and the "stobj" version. Note again the use of "mbe".



;;; The function dag-deref finds the end of a instantiation chain:

(defun dag-deref-st (h terms-dag)
  (declare (xargs :measure (measure-rec-dag t h (terms-dag-graph
						 terms-dag))
		  :stobjs terms-dag
		  :guard (and
			  (natp h) (< h (dag-length terms-dag))
			  (term-graph-p-st terms-dag)
			  (dag-p-st terms-dag))))
  (mbe
   :logic
   (if (dag-p-st terms-dag)
       (let ((p (dagi h terms-dag)))
	 (if (dag-bound-p p) (dag-deref-st p terms-dag) h))
     'undef)
   :exec
   (let ((p (dagi h terms-dag)))
     (if (dag-bound-p p) (dag-deref-st p terms-dag) h))))



(local
 (defthm equal-dag-deref-st-deref-l
   (equal (dag-deref-st h terms-dag)
	  (dag-deref-l h (terms-dag-graph terms-dag)))))

(in-theory (disable dag-deref-st))


;;; A function that checks if a variable node x is in the term dag h (or
;;; list of terms, depending on flg):



(defun occur-check-st (flg x h terms-dag)
  (declare (xargs :measure (measure-rec-dag flg h
					    (terms-dag-graph terms-dag))
		  :hints (("Goal" :in-theory (disable nth)))
		  :stobjs terms-dag
		  :guard (and (natp x)
			      (if flg
				  (and (natp h) (< h (dag-length
						      terms-dag)))
				(bounded-nat-true-listp h (dag-length
							   terms-dag)))
			      (well-formed-term-dag-st-p terms-dag))))
  (mbe
   :logic
   (if (dag-p-st terms-dag)
       (if flg
	   (let ((p (dagi h terms-dag)))
	     (if (dag-bound-p p)
		 (occur-check-st flg x p terms-dag)
	       (let ((args (dag-args p)))
		 (if (equal args t)
		     (= x h)
		   (occur-check-st nil x args terms-dag)))))
	 (if (endp h)
	     nil
	   (or (occur-check-st t x (car h) terms-dag)
	       (occur-check-st nil x (cdr h) terms-dag))))
     'undef)
   :exec
   (if flg
       (let ((p (dagi h terms-dag)))
	 (if (dag-bound-p p)
	     (occur-check-st flg x p terms-dag)
	   (let ((args (dag-args p)))
	     (if (equal args t)
		 (= x h)
	       (occur-check-st nil x args terms-dag)))))
     (if (endp h)
	 nil
       (or (occur-check-st t x (car h) terms-dag)
	   (occur-check-st nil x (cdr h) terms-dag))))))

(local
 (defthm equal-occur-check-st-occur-check-st
   (equal (occur-check-st flg x h terms-dag)
	  (occur-check-l flg x h (terms-dag-graph terms-dag)))))

(in-theory (disable occur-check-st))

;;; The following function applies one step of transformation w.r.t. the
;;; set of rules given by Martelli and Montanari (M--M).

;;; It receives as input a system S of equations to be
;;; unified and a substitution U (partially) computed. Depending on the
;;; form of the first equation of S, one of the rules of M-M is
;;; applied. The main point here is that S and U only contain pointers
;;; to the terms stored in dag. In particular, S is a list of pairs of
;;; indexes, and U is a list of indexes pointing to the nodes where the
;;; instantiated variables are stored (i.e. a substitution). The
;;; function returns a multivalue with the following components,
;;; obtained after the application of one step of M-M: the resulting
;;; system of equations to be solved, the resulting substitution, a
;;; boolean value (to detect unsovability) and the stobj @terms-dag@:


;;; Guard verification:

;;; REPETIDOS ¿ LOS DEJO?


(local
 (defthm natp-dag-deref-l-bounded-term-graph-p
   (implies (and (natp h)
		 (bounded-term-graph-p g n)
		 (dag-p g))
	    (and
	     (integerp (dag-deref-l h g))
	     (acl2-numberp (dag-deref-l h g))
	     (<= 0 (dag-deref-l h g))))))
;;; Ese esta en dag-unification-rules pero con natp.


(local
 (defthm bounded-dag-deref-l-bounded-term-graph-p
   (implies (and (natp h)
		 (< h n)
		 (bounded-term-graph-p g n)
		 (dag-p g))
	    (< (dag-deref-l h g) n))))
;;   :rule-classes :linear))


(local
 (defthm dag-deref-l-not-term-dag-is-p
   (implies (dag-p g)
	    (not (term-dag-is-p (dag-deref-l h g) g)))))


(local
 (defthm bounded-term-graph-p-non-integer-contents
   (implies (and (bounded-term-graph-p g n)
		 (not (integerp (nth h g)))
		 (nth h g))
	    (consp (nth h g)))))

(local
 (defthm bounded-term-graph-p-true-listp-of-arguments
   (implies (and (bounded-term-graph-p g n)
		 (not (integerp (nth h g)))
		 (not (dag-variable-p (nth h g))))
	    (bounded-nat-true-listp (cdr (nth h g)) n))))


(local
 (defthm bounded-term-graph-p-eqlablep-function-symbol
   (implies (and (bounded-term-graph-p g n)
		 (not (integerp (nth h g)))
		 (not (dag-variable-p (nth h g))))
	    (eqlablep (car (nth h g))))))



;;; Esto es patatero (variables libres):
(local (defthm bounded-nat-true-listp-true-listp-instance
	 (implies (bounded-nat-true-listp (cdr (nth h g)) (len g))
		  (true-listp (cdr (nth h g))))))

(defun dag-transform-mm-st (S U terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard
		  (and
		   (consp S)
		   (bounded-nat-pairs-true-listp S (dag-length
							terms-dag))
		   (bounded-nat-substitution-p U (dag-length
						  terms-dag))
		   (well-formed-term-dag-st-p terms-dag))))
  (let* ((ecu (car S))
	 (t1 (dag-deref-st (car ecu) terms-dag))
	 (t2 (dag-deref-st (cdr ecu) terms-dag))
	 (R (cdr S))
	 (p1 (dagi t1 terms-dag))
	 (p2 (dagi t2 terms-dag)))
    (cond
     ((= t1 t2) (mv R U t terms-dag))
     ((dag-variable-p p1)
      (if (occur-check-st t t1 t2 terms-dag)
	  (mv nil nil nil terms-dag)
	(let ((terms-dag (update-dagi t1 t2 terms-dag)))
	  (mv R (cons (cons (dag-symbol p1) t2) U) t terms-dag))))
     ((dag-variable-p p2)
      (mv (cons (cons t2 t1) R) U t terms-dag))
     ((not (eql (dag-symbol p1)
		(dag-symbol p2)))
      (mv nil nil nil terms-dag))
     (t (mv-let (pair-args bool)
		(pair-args (dag-args p1) (dag-args p2))
		(if bool
		    (mv (append pair-args R) U t terms-dag)
		  (mv nil nil nil terms-dag)))))))


;;; A strange case for a lemma that will be useful later:
(local
 (defthm well-formed-upl-st-preserved-by-dag-transform-mm-st-caso-raro
   (implies (well-formed-upl-st S U terms-dag)
	    (mv-let (S1 U1 bool1 terms-dag)
		    (dag-transform-mm-st S U terms-dag)
		    (implies (not bool1)
			     (well-formed-upl-st S1 U1 terms-dag))))
   :hints (("Goal" :in-theory (enable well-formed-upl)))))



(local (in-theory (enable dag-transform-mm-l)))
(local (in-theory (disable transform-mm-l-applies-an-operator)))

(local
 (defthm nth-0-car
   (equal (nth 0 l) (car l))))

;;; Note that due to the multivalue, we need four "translation"
;;; theorems:

(local
 (defthm  dag-transform-mm-st-first-component
   (equal (first (dag-transform-mm-st S U terms-dag))
	  (first  (dag-transform-mm-l (list S U (terms-dag-graph
						 terms-dag)))))))

(local
 (defthm  dag-transform-mm-st-second-component
   (equal (second (dag-transform-mm-st S U terms-dag))
	  (second (dag-transform-mm-l (list S U (terms-dag-graph
						 terms-dag)))))))

(local
 (defthm dag-transform-mm-st-third-component
   (iff (third (dag-transform-mm-st S U terms-dag))
	(dag-transform-mm-l (list S U (terms-dag-graph terms-dag))))))


(local
 (defthm dag-transform-mm-st-fourth-component
   (implies (third (dag-transform-mm-st S U terms-dag))
	    (equal (first
		    (fourth
		     (dag-transform-mm-st S U terms-dag)))
		   (third
		    (dag-transform-mm-l
		     (list S U (terms-dag-graph terms-dag))))))))


(in-theory (disable dag-transform-mm-st dag-transform-mm-l))


;;; Now we study iterative application of transformation steps until
;;; failure is detected or there are no more equations to be solved:



;;; First we show that well-formedness conditions are preserved in each
;;; step of transformation. This will be useful for guard verification
;;; and it justifies the use of the more efficient executable body
;;; (without the expensive well-formedness check) instead of the logic
;;; body.

(local
 (defthm well-formed-upl-list
   (equal (well-formed-upl (list (first upl)
				 (second upl)
				 (third upl)))
	  (well-formed-upl upl))
   :hints (("Goal" :in-theory (enable well-formed-upl)))))

(local
 (defthm well-formed-upl-st-preserved-by-dag-transform-mm-st-casi
   (implies (and (well-formed-upl-st S U terms-dag)
		 (consp S))
	    (mv-let (S1 U1 bool1 terms-dag)
		    (dag-transform-mm-st S U terms-dag)
		    (implies bool1
			     (well-formed-upl-st S1 U1 terms-dag))))
   :hints (("Goal" :use (:instance
			 well-formed-upl-preserved-by-dag-transform-mm-l
			 (upl (list S U (first terms-dag))))
	    :in-theory (disable
			well-formed-upl-preserved-by-dag-transform-mm-l)))))

(defthm well-formed-upl-st-preserved-by-dag-transform-mm-st
  (implies (and (well-formed-upl-st S U terms-dag)
		(consp S))
	   (mv-let (S1 U1 bool1 terms-dag)
		   (dag-transform-mm-st S U terms-dag)
		   (declare (ignore bool1))
		   (well-formed-upl-st S1 U1 terms-dag)))
  :hints (("Goal" :use
	   (well-formed-upl-st-preserved-by-dag-transform-mm-st-casi
	    well-formed-upl-st-preserved-by-dag-transform-mm-st-caso-raro))))




;;; Termination theorem of the unification algorithm:

(encapsulate
 ()

 (local
  (defthm upl-as-pair-of-system-list
    (implies upl
	     (equal
	      (upl-as-pair-of-systems
	       (list (first upl) (second upl) (third upl)))
	      (upl-as-pair-of-systems upl)))
    :hints (("Goal" :in-theory (enable upl-as-pair-of-systems)))))

 (defthm unification-measure-decreases-st
   (mv-let (S1 U1 bool1 terms-dag1)
	   (dag-transform-mm-st S U terms-dag)
	   (implies (and (well-formed-upl-st S U terms-dag)
			 (consp S) bool)
		    (o<
		     (unification-measure
		      (upl-as-pair-of-systems-st S1 U1 bool1 terms-dag1))
		     (unification-measure
		      (upl-as-pair-of-systems-st S U bool terms-dag)))))
   :hints (("Goal" :use (:instance
			 unification-measure-decreases-l
			 (upl (list S U (terms-dag-graph terms-dag))))
	    :in-theory
	    (disable
	     unification-measure-decreases-l)))))



;;; Iterative application of the transformation rules:


(defun dag-solve-system-st (S U bool terms-dag)
  (declare
   (xargs
    :stobjs terms-dag
    :measure (unification-measure
	      (upl-as-pair-of-systems-st S U bool terms-dag))
    :hints (("Goal" :use unification-measure-decreases-st))
    :guard (well-formed-upl-st S U terms-dag)
    :guard-hints (("Goal"
		   :in-theory (enable well-formed-upl)
		   :use
		   well-formed-upl-st-preserved-by-dag-transform-mm-st))))

  (mbe
   :logic
   (if (well-formed-upl-st S U terms-dag)
       (if (or (not bool) (endp S))
	   (mv S U bool terms-dag)
	 (mv-let (S1 U1 bool1 terms-dag)
		 (dag-transform-mm-st S U terms-dag)
		 (dag-solve-system-st S1 U1 bool1 terms-dag)))
     (mv nil nil nil terms-dag))
   :exec
   (if (or (not bool) (endp S))
       (mv S U bool terms-dag)
     (mv-let (S1 U1 bool1 terms-dag)
	     (dag-transform-mm-st S U terms-dag)
	     (dag-solve-system-st S1 U1 bool1 terms-dag)))))




;;; Note that the above executable body is not terminating in
;;; general, even if {\tt occur-check} is never applied: the {\tt decompose}
;;; rule is a possible source of non-termination. For example

; (update-dagi 0 '(equ 1 2) terms-dag)
; (update-dagi 1 '(f 1) terms-dag)
; (update-dagi 2 '(f 2) terms-dag)
; (dag-solve-system-program '((1 . 2)) nil t terms-dag) ===> NON TERMINATING!!!

;;; But it is terminating for inputs satisfying the guard.


;;; Lemmas needed for the corresponding "translation" theorems:

(local
 (defun true-listp-of-three-elements (l)
   (and (consp l) (consp (cdr l)) (consp (cddr l)) (equal (cdddr l) nil))))

(local
 (defthm true-listp-of-three-elements-dag-transform-mm-l
   (implies (dag-transform-mm-l upl)
	    (true-listp-of-three-elements (dag-transform-mm-l upl)))
   :hints (("Goal" :in-theory (enable dag-transform-mm-l)))))

(local
 (defthm true-listp-of-three-elements-eliminate-destructors
   (implies (true-listp-of-three-elements l)
	    (equal (list (first l) (second l) (third l))
		   l))))

(local (in-theory (disable true-listp-of-three-elements)))

;;; Translation theorems:

(local
 (defthm  dag-solve-system-st-first-component
   (implies (third (dag-solve-system-st S U bool terms-dag))
	    (equal (first (dag-solve-system-st S U bool terms-dag))
		   (first  (solve-upl-l
			    (and bool (list S U (terms-dag-graph terms-dag)))))))))



(local
 (defthm  dag-solve-system-st-second-component
   (implies (third (dag-solve-system-st S U bool terms-dag))
	    (equal (second (dag-solve-system-st S U bool terms-dag))
		   (second (solve-upl-l
			    (and bool (list S U (terms-dag-graph terms-dag)))))))))


(local
 (defthm  dag-solve-system-st-fourth-component
   (implies (third (dag-solve-system-st S U bool terms-dag))
	    (equal (first
		    (fourth (dag-solve-system-st S U bool terms-dag)))
		   (third (solve-upl-l
			   (and bool (list S U (terms-dag-graph terms-dag)))))))))

(local
 (defthm  dag-solve-system-st-third-component
   (iff (third (dag-solve-system-st S U bool terms-dag))
	(solve-upl-l (and bool (list S U (terms-dag-graph terms-dag)))))))





;;; Solving systems of equations:


(defun dag-mgs-st (S terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (well-formed-dag-system-st S terms-dag)))

  (mv-let (S1 sol bool terms-dag)
	  (dag-solve-system-st S nil t terms-dag)
	  (declare (ignore S1))
	  (mv sol bool terms-dag)))



(local (in-theory (enable dag-mgs-l)))

(local
 (defthm  dag-mgs-st-first-component
   (implies (second (dag-mgs-st S terms-dag))
	    (equal (first (dag-mgs-st S terms-dag))
		   (second (dag-mgs-l S (terms-dag-graph terms-dag)))))))


(local
 (defthm  dag-mgs-st-third-component
   (implies (second (dag-mgs-st S terms-dag))
	    (equal (first (third (dag-mgs-st S terms-dag)))
		   (third (dag-mgs-l S (terms-dag-graph terms-dag)))))))

(local
 (defthm  dag-mgs-st-second-component
   (iff (second (dag-mgs-st S terms-dag))
	(dag-mgs-l S (terms-dag-graph terms-dag)))))

(local (in-theory (disable dag-mgs-l)))

(in-theory (disable dag-mgs-st))





;;; Empty graphs:

(defun empty-graph-p-st (terms-dag)
  (declare (xargs :stobjs terms-dag))
  (empty-graph-p (dag-component-st terms-dag)))


(local
 (defthm nth-fix-true-list
   (equal (nth n (fix-true-list l))
	  (nth n l))))


(local
 (defthm empty-graph-p-fix-true-listp
   (equal (empty-graph-p-aux hs (fix-true-list g))
	  (empty-graph-p-aux hs g))))

(local
 (defthm empty-graph-p-st-main-property
   (equal (empty-graph-p-st terms-dag)
	  (empty-graph-p (terms-dag-graph terms-dag)))
   :hints (("Goal" :in-theory (enable empty-graph-p)))))


(in-theory (disable empty-graph-p-st))







;;; A function to store a term (or list of terms) in a dag:


(defun term-as-dag-aux (flg term terms-dag h variables)
  (declare (xargs :stobjs terms-dag
		  :guard (and (term-graph-p-st terms-dag)
			      (natp h)
			      (term-p-aux flg term)
			      (<= (+ h (length-term flg term))
				  (dag-length terms-dag))
			      (bounded-nat-substitution-p variables
							  (dag-length terms-dag)))
		  :verify-guards nil))
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
		(term-as-dag-aux
		 nil (cdr term) terms-dag (1+ h) variables)
		(let* ((terms-dag
			(update-dagi h (cons (car term) hsl) terms-dag)))
		  (mv terms-dag h1 nil var1))))
    (if (endp term)
	(mv terms-dag h term variables)
      (mv-let (terms-dag hcar ign varcar)
	      (term-as-dag-aux t (car term) terms-dag h variables)
	      (declare (ignore ign))
	      (mv-let (terms-dag hcdr hsl varcdr)
		      (term-as-dag-aux
		       nil (cdr term) terms-dag hcar varcar)
		      (mv terms-dag hcdr (cons h hsl) varcdr))))))


(defun term-as-dag (term terms-dag)
  (declare (xargs :stobjs (terms-dag)
		  :guard (and
			  (term-graph-p-st terms-dag)
			  (term-p term)
			  (<= (length-term t term)
			      (dag-length terms-dag)))
                  :verify-guards nil))
  (mv-let (terms-dag h hs var)
	  (term-as-dag-aux t term terms-dag 0 nil)
	  (declare (ignore h hs var))
	  terms-dag))


(local
 (defthm term-as-dag-aux-l-term-as-dag-aux
   (and
    (equal (first
	    (first
	     (term-as-dag-aux flg term terms-dag h variables)))
	   (first
	    (term-as-dag-aux-l
	     flg term (terms-dag-graph terms-dag) h variables)))
    (equal (second (term-as-dag-aux flg term terms-dag h variables))
	   (second (term-as-dag-aux-l
		    flg term (terms-dag-graph terms-dag) h variables)))
    (equal (third (term-as-dag-aux flg term terms-dag h variables))
	   (third (term-as-dag-aux-l
		   flg term (terms-dag-graph terms-dag) h variables)))
    (equal (fourth (term-as-dag-aux flg term terms-dag h variables))
	   (fourth (term-as-dag-aux-l
		    flg term (terms-dag-graph terms-dag) h variables))))))



(local
 (defthm term-as-dag-l-term-as-dag
   (equal (first (term-as-dag term terms-dag))
	  (term-as-dag-l term (terms-dag-graph terms-dag)))
   :hints (("Goal" :in-theory (enable term-as-dag-l)))))

(local (in-theory (disable term-as-dag-aux term-as-dag)))


;;; Guard verification:

(local
 (defthm bounded-nat-substitution-p-assoc-consp
   (implies (and (bounded-nat-substitution-p alist n)
		 (assoc x alist))
	    (consp (assoc x alist)))))



(local
 (defthm bounded-nat-substitution-p-alistp
   (implies (bounded-nat-substitution-p alist n)
	    (alistp alist))))

(verify-guards term-as-dag-aux
	       :hints (("Goal" :in-theory (disable term-graph-p))))


(verify-guards term-as-dag)


;;; Needed for guard verification of the following function:

(local
 (defthm empty-graph-p-rec-resize-list
   (implies (empty-graph-p-rec g)
	    (empty-graph-p-rec (resize-list g n nil)))))

(local
 (defthm len-resize-list
   (implies (natp n)
	    (equal (len (resize-list g n x)) n))))



;;; Most general unifier of two terms:

(local (in-theory (disable resize-list)))

(defun unif-two-terms-problem-st (t1 t2 terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (term-p t1) (term-p t2)
			      (empty-graph-p-st terms-dag))))
  (let* ((size (+ (length-term t t1) (length-term t t2) 1))
	 (terms-dag (resize-dag size terms-dag)))
    (term-as-dag (list 'equ t1 t2) terms-dag)))

;;; Note that this function do not need an alternative "executable"
;;; body:

(local
 (defthm unif-two-terms-problem-st-unif-two-terms-problem-l
   (equal (first (unif-two-terms-problem-st t1 t2 terms-dag))
	  (unif-two-terms-problem-l
	   t1 t2 (terms-dag-graph terms-dag)))
   :hints (("Goal" :in-theory (enable unif-two-terms-problem-l)))) )

(in-theory (disable unif-two-terms-problem-st))



;;; Examples:

; (unif-two-terms-problem-st
;    '(f x (g (a) y)) '(f x (g y x)) terms-dag)
; (show-dag 0 10 terms-dag)
; ===> ((EQU 1 6) (F 2 3) (X . T) (G 4 5) (A) (Y . T)
;                 (F 7 8) 2 (G 9 10) 5 2)
; (unif-two-terms-problem-st
;   '(f (h z) (g (h x) (h u))) '(f x (g (h u) v)) terms-dag)
; (show-dag 0 14 terms-dag)
; ===> ((EQU 1 9) (F 2 4) (H 3) (Z . T) (G 5 7) (H 6) (X . T) (H 8) (U . T)
;                 (F 10 11) 6 (G 12 14) (H 13) 8 (V . T))
; ACL2 !>(unif-two-terms-problem-st
; 			 '(f (h z) (g (h x) (h u))) '(f x (g (h u) v))
; 			 terms-dag)
; <terms-dag>
; ACL2 !>(dag-as-term t 0 terms-dag)
; (EQU (F (H Z) (G (H X) (H U)))
;      (F X (G (H U) V)))

(defun initial-to-be-solved-st (terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and
			      (< 0 (dag-length terms-dag))
			      (consp (dagi 0 terms-dag))
			      (consp (cdr (dagi 0 terms-dag)))
			      (consp (cddr (dagi 0 terms-dag))))))
  (list (cons (first (cdr (dagi  0 terms-dag)))
	      (second (cdr (dagi 0 terms-dag))))))

(local
 (defthm initial-to-be-solved-st-initial-to-be-solved-l
   (equal (initial-to-be-solved-st terms-dag)
	  (initial-to-be-solved-l (terms-dag-graph terms-dag)))
   :hints (("Goal" :in-theory (enable initial-to-be-solved-l)))) )

(local (in-theory (disable initial-to-be-solved-st)))


;;; Unification of two terms, receiving the stobj as input:

(defun dag-mgu-st (t1 t2 terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (term-p t1) (term-p t2)
			      (empty-graph-p-st terms-dag))
		  :verify-guards nil))
  (let ((terms-dag
	 (unif-two-terms-problem-st t1 t2 terms-dag)))
    (dag-mgs-st
     (initial-to-be-solved-st terms-dag) terms-dag)))

;;; Guard verification

;;; AVERIGUAR POR QUé ESTE TEOREMA TARDA TANTO!!!!!!!!


;;; I don't know why, but the following theory has an important
;;; slowdown, partially fixed disabling these rules:

(local (in-theory (disable mv-nth-0-first
			   mv-nth-1-second
			   mv-nth-2-third
			   mv-nth-3-fourth)))


(local
 (defthm several-properties-term-as-dag-l-on-initial-problem
   (and (consp (car (term-as-dag-l (list 'equ t1 t2) g)))
	(consp (cdar (term-as-dag-l (list 'equ t1 t2) g)))
	(consp (cddar (term-as-dag-l (list 'equ t1 t2) g))))
   :hints (("Goal" :in-theory (enable term-as-dag-l)))))


(local (in-theory (enable mv-nth-0-first
			  mv-nth-1-second
			  mv-nth-2-third
			  mv-nth-3-fourth)))


(local
 (defthm several-properties-unif-two-terms-problem-l
   (let ((uttp  (unif-two-terms-problem-l t1 t2 g)))
     (and (consp uttp)
	  (consp (car uttp))
	  (consp (cdr (car uttp)))
	  (consp (cddr (car uttp)))))
   :hints (("Goal" :in-theory (enable unif-two-terms-problem-l)))))


(verify-guards dag-mgu-st)

;;; Main theorem about dag-mgu-st and dag-mgu-l


(local
 (defthm  dag-mgu-st-first-component
   (implies (second (dag-mgu-st t1 t2 terms-dag))
	    (equal (first (dag-mgu-st t1 t2 terms-dag))
		   (second (dag-mgu-l t1 t2 (terms-dag-graph terms-dag)))))))


(local
 (defthm  dag-mgu-st-third-component
   (implies (second (dag-mgu-st t1 t2 terms-dag))
	    (equal (first (third (dag-mgu-st t1 t2 terms-dag)))
		   (third (dag-mgu-l t1 t2 (terms-dag-graph terms-dag)))))))

(local
 (defthm  dag-mgu-st-second-component
   (iff (second (dag-mgu-st t1 t2 terms-dag))
	(dag-mgu-l t1 t2 (terms-dag-graph terms-dag)))))

(local (in-theory (disable dag-mgu-l)))

(in-theory (disable dag-mgu-st))




;;; Finally, unification of two terms, using a local stobj:


(defun dag-mgu-aux (t1 t2 terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (term-p t1) (term-p t2)
			      (empty-graph-p-st terms-dag))
		  :verify-guards nil))

  (mv-let (sol bool terms-dag)
	  (dag-mgu-st t1 t2 terms-dag)
	  (if bool
	      (let ((sol-l (solved-as-system-st sol terms-dag)))
		(mv t sol-l terms-dag))
	    (mv nil nil terms-dag))))




(verify-guards dag-mgu-aux :otf-flg t
	       :hints (("Goal" :in-theory (disable well-formed-term-dag-p))))



;;; ***************************
;;; THE MAIN TOP LEVEL FUNCTION
;;; ***************************

(defun dag-mgu (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (with-local-stobj
   terms-dag
   (mv-let (bool sol terms-dag)
	   (dag-mgu-aux t1 t2 terms-dag)
	   (mv bool sol))))




;;; Examples:
; ACL2 >(dag-mgu '(f x x) '(f (h y) z))
; (T ((Z H Y) (X H Y)))
; ACL2 >(dag-mgu '(f (h z) (g (h x) (h u))) '(f x (g (h u) v)))
; (T ((V H (H Z)) (U H Z) (X H Z)))
; ACL2 >(dag-mgu '(f (h z) (g (h x) (h u))) '(f x (g (h y) v)))
; (T ((V H U) (Y H Z) (X H Z)))
; ACL2 >(dag-mgu '(f y x) '(f (k x) y))
; (NIL NIL)


;;; ============================================================================
;;;
;;; 4) The main properties:
;;;
;;; ============================================================================


;;; Main properties of the algorithm that solves systems of equations:

(defthm dag-mgs-st-completeness
  (let ((S (tbs-as-system-st S-dag terms-dag)))
    (implies (and (well-formed-dag-system-st S-dag terms-dag)
		  (solution sigma S))
	     (second (dag-mgs-st S-dag terms-dag)))))


(defthm dag-mgs-st-soundness
  (let* ((S (tbs-as-system-st S-dag terms-dag))
	 (dag-mgs-st (dag-mgs-st S-dag terms-dag))
	 (unifiable (second dag-mgs-st))
	 (sol (solved-as-system-st (first dag-mgs-st)
				   (third dag-mgs-st))))
    (implies (and (well-formed-dag-system-st S-dag terms-dag)
		  unifiable)
	     (solution sol S))))

(defthm dag-mgs-st-idempotent
  (let* ((dag-mgs-st (dag-mgs-st S-dag terms-dag))
	 (unifiable (second dag-mgs-st))
	 (sol (solved-as-system-st (first dag-mgs-st)
				   (third dag-mgs-st))))
    (implies (and (well-formed-dag-system-st S-dag terms-dag)
		  unifiable)
	     (idempotent sol)))
  :hints (("Goal" :in-theory (disable idempotent))))


(defthm dag-mgs-st-most-general-solution
  (let* ((S (tbs-as-system-st S-dag terms-dag))
	 (dag-mgs-st (dag-mgs-st S-dag terms-dag))
	 (sol (solved-as-system-st (first dag-mgs-st)
				   (third dag-mgs-st))))
    (implies (and (well-formed-dag-system-st S-dag terms-dag)
		  (solution sigma S))
	     (subs-subst sol sigma))))


;;; Properties of @dag-mgu-st@:



(defthm  dag-mgu-st-completeness
  (implies (and (equal (instance t1 sigma)
		       (instance t2 sigma))
		(term-p t1) (term-p t2)
		(empty-graph-p-st terms-dag))
	   (second (dag-mgu-st t1 t2 terms-dag))))



(defthm dag-mgu-st-soundness
  (let* ((dag-mgu-st (dag-mgu-st t1 t2 terms-dag))
	 (sol (solved-as-system-st (first dag-mgu-st)
				   (third dag-mgu-st))))
    (implies (and (empty-graph-p-st terms-dag)
		  (term-p t1) (term-p t2)
		  (second dag-mgu-st))
	     (equal (instance t1 sol) (instance t2 sol)))))


(defthm dag-mgu-st-most-general-solution
  (let* ((dag-mgu-st (dag-mgu-st t1 t2 terms-dag))
	 (sol (solved-as-system-st (first dag-mgu-st)
				   (third dag-mgu-st))))
    (implies (and (empty-graph-p-st terms-dag)
		  (term-p t1) (term-p t2)
		  (equal (instance t1 sigma)
			 (instance t2 sigma)))
	     (subs-subst sol sigma))))

(defthm dag-mgu-st-idempotent
  (let* ((dag-mgu-st (dag-mgu-st t1 t2 terms-dag))
	 (sol (solved-as-system-st (first dag-mgu-st)
				   (third dag-mgu-st))))
    (implies (and (empty-graph-p-st terms-dag)
		  (term-p t1) (term-p t2)
		  (second dag-mgu-st))
	     (idempotent sol)))
  :hints (("Goal" :in-theory (disable idempotent))))


;;; And finally, proerties of @dag-mgu@:


(defthm  dag-mgu-completeness
  (implies (and (equal (instance t1 sigma)
		       (instance t2 sigma))
		(term-p t1) (term-p t2))
	   (first (dag-mgu t1 t2))))




(defthm dag-mgu-soundness
  (let* ((dag-mgu (dag-mgu t1 t2))
	 (unifiable (first dag-mgu))
	 (sol (second dag-mgu)))
    (implies (and (term-p t1) (term-p t2)
		  unifiable)
	   (equal (instance t1 sol) (instance t2 sol)))))




(defthm dag-mgu-most-general-solution
  (let* ((dag-mgu (dag-mgu t1 t2))
	 (sol (second dag-mgu)))
  (implies (and (term-p t1) (term-p t2)
		(equal (instance t1 sigma)
		       (instance t2 sigma)))
	   (subs-subst sol sigma))))


(defthm dag-mgu-idempotent
  (let* ((dag-mgu (dag-mgu t1 t2))
	 (sol (second dag-mgu)))
    (implies (and (term-p t1) (term-p t2))
	     (idempotent sol))))


;;; ===============================================================
