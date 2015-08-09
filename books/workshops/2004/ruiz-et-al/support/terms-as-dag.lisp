;;; ============================================================================
;;; terms-as-dag.lisp
;;; Título: Storing first--order terms as dags
;;; ============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "terms-as-dag")


|#

(in-package "ACL2")


(include-book "dag-unification-rules")


;;; ============================================================================
;;;
;;; 0) Introducción
;;;
;;; ============================================================================

;;; In this book ({\tt terms-as-dag.lisp}), we define a function to
;;; store first--order terms (respresented in standard list/prefix
;;; notation) as directed acyclic graphs (dags), with shared
;;; variables. This function is essential (it is the first step) in the
;;; design of a unification algorithm using a dag representation.

;;; The following function {\tt term-as-dag} (with its main auxiliary
;;; function {\tt term-as-dag-aux}) receives as input a first--order
;;; term and a graph and returns a graph that stores the input terms
;;; (following the conventions explained in the book {\tt
;;; dags.lisp}). Note that the result is a graph such that the term
;;; pointed by the index @0@ is the input term:



(defun term-as-dag-aux (flg term g h variables)
  (if flg
      (if (variable-p term)
	  (let* ((bound (assoc term variables))
		 (g (update-dagi-l h (if bound (cdr bound) (cons term t)) g))
		 (new-variables (if bound variables (acons term h variables))))
	    (mv g (1+ h) nil new-variables))
	(mv-let (g h1 hsl var1)
		(term-as-dag-aux nil (cdr term) g (1+ h) variables)
		(let* ((g (update-dagi-l h (cons (car term) hsl) g)))
		  (mv g h1 nil var1))))
    (if (endp term)
	(mv g h term variables)
      (mv-let (g hcar ign varcar)
	      (term-as-dag-aux t (car term) g h variables)
	      (declare (ignore ign))
	      (mv-let (g hcdr hsl varcdr)
		      (term-as-dag-aux nil (cdr term) g hcar varcar)
		      (mv g hcdr (cons h hsl) varcdr))))))

(defun term-as-dag (term g)
  (mv-let (g h hs var)
	  (term-as-dag-aux t term g 0 nil)
	  (declare (ignore h hs var))
	  g))

;;; Example:

; ACL2 !>(term-as-dag
;            '(f (h x) y (k (g (k y) (k x z))))
;	       '(nil nil nil nil nil nil nil nil nil nil nil))
; ((F 1 3 4) (H 2) (X . T)
;            (Y . T)
;            (K 5) (G 6 8) (K 7) 3 (K 9 10) 2 (Z . T))


;;; The main auxiliary function {\tt term-as-dag-aux} is defined
;;; recursively in the structure of the term stored. The flag @flg@
;;; indicates if @term@ is considered to be a term or a list of terms,
;;; as usual. The argument @h@ is an index in the graph @g@; from this index
;;; on, the term is going to be stored in the graph. Since the term is
;;; stored with shared variables, the argument @variables@ stored a
;;; association list, associating variables previously stored with the
;;; corresponding index of the node where the variable is already stored
;;; in the graph.

;;; This function returns a multivalue with four values. The first one
;;; is the new graph obtained, the second is the first available index
;;; after the proccess, the third (only makes sense for the case of
;;; lists of terms) is the list of initial indices where each of the
;;; terms of the list have been stored, and the fourth is the new
;;; association list of variables to indices, extending the input
;;; association list.

;;; Our goal in this book is to verify this function, showing that it
;;; sores a term in the conditions required by the rules of
;;; transformation of a unification algorithm acting on term dags (see
;;; {\tt dag\--unification\--rules\-.lisp}. That is, we prove the
;;; following theorems (the predicate {\tt empty-graph-p} describes
;;; graphs with @nil@ in all its positions):

; (defthm term-as-dag-term-graph-p
;   (implies (and (empty-graph-p g) (term-p term))
;	     (term-graph-p (term-as-dag term g))))



; (defthm term-as-dag-dag-p
;   (implies (and (empty-graph-p g) (term-p term))
; 	     (dag-p (term-as-dag term g))))


; (defthm term-as-dag-stores-term
;   (implies (and (empty-graph-p g) (term-p term))
; 	     (equal (dag-as-term t 0 (term-as-dag term g))
;		    term)))


; (defthm term-as-dag-no-duplicatesp-variables
;    (implies (and (empty-graph-p g) (term-p term))
; 	      (no-duplicatesp
; 	         (list-of-term-dag-variables (term-as-dag term g))))


;;; These theorems ensure that we can use the function @term-as-dag@ to
;;; store well--formed unification problems (see the book {\tt
;;; dag-unification-rules.lisp}). In fact, in the last section of this
;;; book, we define and verify a function that (using the above function
;;; {\tt term-as-dag}) stores a given unification problem as directed
;;; acyclicic graph.

;;; Finally, note that for the moment we are not talking about
;;; single--threaded objects. But later (book {\tt
;;; dag-unification-st.lisp}), we will use the properties of
;;; these functions to verify an analogue functions defined using stobjs
;;; (that is, the graph obtained will be destructively updated).


;;; The following books are used, and contain information that is
;;; relevant to understand the contents of this book:

;;; *)
;;;  The book {\tt dag-unification-rules} describes the rules of
;;;  transformation of unification, done with a dag representation of
;;;  terms. It includes the book {\tt dags.lisp}, where it is described
;;;  how term graphs are represented and the meaning of the information
;;;  stored in the nodes
;;; -)


;;; ============================================================================
;;;
;;; 1) The proof strategy
;;;
;;; ============================================================================

;;; Note that verifying the function @term-as-dag@ may be difficult,
;;; for several reasons:

;;; *)
;;;   We use an association list to avoid duplication of variables.
;;; *)
;;;   The node corresponding to a function symbol is updated {\em after}
;;;   the list of its arguments have been stored.
;;; *)
;;;   To store a list of terms, the @cdr@ of the list is stored having
;;;   as input the graph obtained after storing the @car@ of the list.
;;; *)
;;;   We must ensure that the graph stored is a directed acyclic graph
;;;   (as defined by @dag-p@). In particular this property has to be
;;;   held in every stage of the proccess (because we need to use
;;;   induction hypothesis in the proof of the theorems).
;;; -)

;;; We tried to verify the functions directly and it turned (not very
;;; surprisingly) very difficult. So we explain now the approach we
;;; followed. The main idea is to employ some kind of compositional
;;; reasoning, in order to consider the difficult issues of the proofs
;;; separately. In particular, we reason about "shared variables" and
;;; the proccess of "storing the term", separately.

;;; For that purpose, we define a version of {\tt term-as-dag-aux},
;;; called {\tt term-as-dag-aux-ns}, storing terms (or list of terms)
;;; but without the burden of getting shared variables. Note that we do
;;; not need in this case the association list of variables to indices:


(local
 (defun term-as-dag-aux-ns (flg term g h)
   (if flg
       (if (variable-p term)
	   (let ((g (update-dagi-l h (cons term t) g)))
	     (mv g (1+ h) nil))
	 (mv-let (g h1 hsl)
		 (term-as-dag-aux-ns nil (cdr term) g (1+ h))
		 (let* ((g (update-dagi-l h (cons (car term) hsl) g)))
		   (mv g h1 nil))))
     (if (endp term)
	 (mv g h term)
       (mv-let (g hcar ign)
	       (term-as-dag-aux-ns t (car term) g h)
	       (declare (ignore ign))
	       (mv-let (g hcdr hsl)
		       (term-as-dag-aux-ns nil (cdr term) g hcar)
		       (mv g hcdr (cons h hsl))))))))


;;; We also define a function that makes variables to be shared in a
;;; given graph. More precisely, the following function {\tt
;;; make\--shared\--variables} receives as input a graph, an association
;;; list (associating variables to indices pointing where they appear
;;; for the first time in the graph) and a pair of indices (indicating a
;;; range), and returns a multivalue with a graph where all the
;;; variables in the range of indices are shared and a new computed
;;; association list. Note that during the proccess, if a variable node
;;; is found and the variable is bound in the associaton list to an
;;; index, then the node is updated to that index. If the variable node
;;; is not bound in the association list, then the node is not updated,
;;; but the association list is extended, binding the new variable to
;;; the current index.


(local
 (defun make-shared-variables (h1 h2 g variables)
   (declare (xargs :measure (nfix (- h2 h1))))
   (cond ((zp (- h2 h1))
	  (mv g variables))
	 ((term-dag-variable-p h1 g)
	  (let ((bound (assoc (term-dag-symbol h1 g) variables)))
	    (if bound
		(let ((g (update-nth h1 (cdr bound) g)))
		  (make-shared-variables (1+ h1) h2 g variables))
	      (make-shared-variables
	       (1+ h1) h2 g (acons (term-dag-symbol h1 g) h1
				   variables)))))
	 (t (make-shared-variables (1+ h1) h2 g variables)))))


;;; Our strategy is as follows:

;;; *)
;;;  Verify the properties of {\tt term-as-dag-aux-ns}, showing that
;;;  stores the input term as a directed acyclic graph.
;;; *)
;;;  Show that {\tt make-shared-variables} preserves those properties.
;;; *)
;;;  Prove that the composition of {\tt make-shared-variables} and {\tt
;;;  term-as-dag-aux-ns} is equal to {\tt term-as-dag-aux}
;;; *)
;;;  Combine all the above results to prove the intended properties of
;;;  {\tt term-as-dag-aux}. As a particular case, the properties of
;;;  {\tt term-as-dag}.
;;; -)

;;; There is an exception to this strategy: when we prove the {\tt
;;; term-graph-p} property of the graph obtained by {\tt
;;; term-as-dag} (theorem {\tt term-as-dag-term-graph-p} above),
;;; we will reason directly with the definition of the function {\tt
;;; term-as-dag}.

(local (in-theory (disable assoc-val)))


;;; ============================================================================
;;;
;;; 2) Some properties related to {\tt dag-p}
;;;
;;; ============================================================================

;;; One of the main drawbacks in the proof effort described in this book
;;; is the proof that the graphs obtained are acyclic, as defined by the
;;; function @dag-p@ (see {\tt dags.lisp}). In this section we define
;;; some conditions on graphs stronger than the @dag-p@ condition.


;;; -----------------------------------
;;;
;;; 2.1) The property {\tt init-term-dag-p}
;;;
;;; -----------------------------------

;;; The property @init-term-dag-p@ defined below describes a particular
;;; type of directed acyclicic graphs: those obtained storing terms
;;; using the function @term-as-dag@.

;;; Note the style of the definition: we define  {\em a property of
;;; nodes} ({\tt property\--element\--init\--term\--dag-p} in this
;;; case). Then we define a function ({\tt init\--term\--dag-p\--aux} in
;;; this case) checking if that property holds in a list of given
;;; nodes. Finally we define the function {\tt init\--term\--dag-p}
;;; checking the property in the list off all the nodes of a graph.

;;; A graph has the property {\tt init-term-dag-p} if every node is
;;; @nil@, or a compound node such that its arguments are bigger
;;; indices, or a variable node, or an "is" node pointing to a previous
;;; variable node:

(local
 (defun smaller-than-list (h l)
   (if (endp l)
       t
     (and (< h (car l))
	  (smaller-than-list h (cdr l))))))

(local
 (defun property-element-init-term-dag-p (h node g)
   (or (and (natp node) (< node h) (term-dag-variable-p node g))
       (equal node nil)
       (and (consp node)
	    (variable-p (car node)) (equal (cdr node) t))
       (and (consp node)
	    (nat-true-listp (cdr node))
	    (smaller-than-list h (cdr node))))))

(local
 (defun init-term-dag-p-aux (hs g)
   (if (endp hs)
       t
     (and (property-element-init-term-dag-p (car hs) (nth (car hs) g) g)
	  (init-term-dag-p-aux (cdr hs) g)))))


(defun list-from-to (n m)
  (declare (xargs :measure (nfix (- m n))
		  :guard (and (natp n) (natp m) (<= n m))))
  (if (zp (- m n))
      nil
    (cons n (list-from-to (1+ n) m))))



;;; First, some properties about the function {\tt list-from-to}:

(local
 (defthm list-from-to-main-property
   (implies (and (natp n) (natp m))
	    (iff (member x (list-from-to n m))
		 (and (natp x) (<= n x) (< x m))))))


(local
; Renamed from nat-listp by Matt K. after v4-3, to avoid conflict with
; books/arithmetic/nat-listp.lisp.
 (defun local-nat-listp (l)
   (if (endp l)
       t
     (and (natp (car l))
	  (local-nat-listp (cdr l))))))


(local
 (defthm list-from-to-local-nat-listp
   (implies (and (natp h1) (natp h2))
	    (local-nat-listp (list-from-to h1 h2)))))


(local
 (defthm append-list-from-to
   (implies (and (natp h1) (natp h2) (natp h3)
		 (<= h1 h2) (<= h2 h3))
	    (equal (append (list-from-to h1 h2)
			   (list-from-to h2 h3))
		   (list-from-to h1 h3)))))


(local
 (defun init-term-dag-p (g)
   (init-term-dag-p-aux (list-from-to 0 (len g)) g)))



;;; -----------------------------------
;;;
;;; 2.2) The property {\tt tree-p}
;;;
;;; -----------------------------------

;;; A particular case of {\tt init\--term\--dag\--p} is the property
;;; {\tt tree-p}. In this case we do not allow "is" nodes. This kind iof
;;; graphs are the graphs built by the function {\tt
;;; term-as-dag-aux-ns}:

(local
 (defun property-element-tree-p (h node)
   (or (equal node nil)
       (and (consp node)
	    (variable-p (car node)) (equal (cdr node) t))
       (and (consp node)
	    (nat-true-listp (cdr node))
	    (smaller-than-list h (cdr node))))))



(local
 (defun tree-p-aux (hs g)
   (if (endp hs)
       t
     (and (property-element-tree-p (car hs) (nth (car hs) g))
	  (tree-p-aux (cdr hs) g)))))

(local
 (defun tree-p (g)
   (tree-p-aux (list-from-to 0 (len g)) g)))




;;; -----------------------------------
;;;
;;; 2.2) The property {\tt init-term-dag-p} implies {\tt dag-p}
;;;
;;; -----------------------------------

;;; Due to the main properties of {\tt dag-p} (see {\tt dags.lisp}) we
;;; only has to show that every path in graph verifying {\tt
;;; init-term-dag-p} has no duplicates nodes. But this is true because
;;; the paths in this case are strictly increasing except (possibly) the
;;; last node (and in that case, this last node is a variable node and
;;; obvioulsy it has to be the first time it appears in a path):

;;; We first prove some properties about {\tt init-term-dag-p} before
;;; disabling the function:

(local
 (encapsulate

  ()

  (local
   (defthm init-term-dag-p-aux-member-1
     (implies (and (init-term-dag-p-aux hs g)
		   (member h hs)
		   (not (term-dag-is-p h g)))
	      (smaller-than-list h (neighbors h g)))))

  (local
   (defthm init-term-dag-p-aux-member-2
     (implies (and  (member x (neighbors h g))
		    (init-term-dag-p-aux hs g)
		    (member h hs)
		    (term-dag-is-p h g))
	      (not (consp (neighbors x g))))))


  (local
   (defthm init-term-dag-p-aux-member-3
     (implies (and (init-term-dag-p-aux hs g)
		   (member h hs))
	      (nat-true-listp (neighbors h g)))))

  (local
   (defthm nth-non-nil
     (implies (and (<= (len l) n) (natp n))
	      (not (nth n l)))))


;; If a node is not an "is" node, then is smaller than its neighbors.

  (defthm init-term-dag-p-property-1
    (implies (and (natp h)
		  (init-term-dag-p g)
		  (not (term-dag-is-p h g)))
	     (smaller-than-list h (neighbors h g)))
    :hints (("Goal" :cases ((< h (len g))))
	    ("Subgoal 1" :in-theory (disable neighbors))))

;; Non--terminal nodes are not neighbors of an "is" node:

  (defthm init-term-dag-p-property-2
    (implies (and (natp h)
		  (init-term-dag-p g)
		  (term-dag-is-p h g)
		  (consp (neighbors x g)))
	     (not (member x (neighbors h g))))
    :hints (("Goal" :cases ((< h (len g))))
	    ("Subgoal 1" :in-theory (disable neighbors))))


;; The list neighbors of every node is a true list of natural numbers:

  (defthm init-term-dag-p-property-3
    (implies (and (init-term-dag-p g) (natp h))
	     (nat-true-listp (neighbors h g)))
    :hints (("Goal" :cases ((< h (len g))))
	    ("Subgoal 1" :in-theory (disable neighbors))))))



;;; The three above properties should suffice:

(local (in-theory (disable neighbors init-term-dag-p)))


;;; The following sequence of events show that every path in graph
;;; verifying {\tt init-term-dag-p} has no duplicates. The main idea is
;;; to split every path into two pieces. The first one is a path with
;;; its nodes in a strictly increasing order. The second part is empty
;;; or a variable node that (obviusly) does not appear in the first
;;; part. Both parts has no nodes in common and no duplicate nodes:


(local
 (encapsulate
  ()

  (local
   (defun strictly-increasing-path-piece (p)
     (cond ((or (endp p) (endp (cdr p))) p)
	   ((< (first p) (second p)) (cons (car p)
					   (strictly-increasing-path-piece (cdr
									    p))))
	   (t (list (first p))))))

  (local
   (defun remaining-path-piece (p)
     (cond ((endp p) p)
	   ((endp (cdr p)) (cdr p))
	   ((< (first p) (second p)) (remaining-path-piece (cdr p)))
	   (t (cdr p)))))

  (local
   (defthm strictly-increasing-path-piece-append-remaining-path-piece
     (equal (append (strictly-increasing-path-piece p)
		    (remaining-path-piece p))
	    p)))

  (local
   (defun strictly-increasing-list (l)
     (cond ((endp l) t)
	   ((endp (cdr l)) t)
	   (t (and (< (first l) (second l))
		   (strictly-increasing-list (cdr l)))))))

  (local
   (defthm strictly-increasing-path-piece-strictly-increasing
     (strictly-increasing-list  (strictly-increasing-path-piece p))))


  (local
   (defthm smaller-than-list-main-property
     (implies (and (member y l)
		   (not (< x y)))
	      (not (smaller-than-list x l)))))

  (local
   (defthm map-nfix-true-listp
     (implies (nat-true-listp l)
	      (equal (map-nfix l) l))))

  (local
   (defthm init-term-dag-p-neighbors-main-property
     (implies (and (natp h)
		   (<= x h)
		   (consp (neighbors x g))
		   (init-term-dag-p g))
	      (not (member x (neighbors h g))))
     :hints (("Goal" :cases ((term-dag-is-p h g)))
	     ("Subgoal 2" :use init-term-dag-p-property-1))))



  (local
   (defthm remaining-path-piece-main-property
     (implies (and (path-p p g)
		   (init-term-dag-p g)
		   (not (endp (remaining-path-piece p))))
	      (not (consp (neighbors (first (remaining-path-piece p)) g))))))


  (local
   (defthm path-p-with-its-first-a-terminal-node
     (implies (and (path-p p g)
		   (not (endp (cdr p))))
	      (consp (neighbors (first p) g)))))


  (local
   (defthm remaining-path-piece-main-property-corollary
     (implies (and (path-p p g)
		   (init-term-dag-p g)
		   (not (endp (remaining-path-piece p))))
	      (not (consp (cdr (remaining-path-piece p)))))))



  (local
   (defthm strictly-increasing-path-piece-non-terminal-nodes
     (implies (and (path-p p g)
		   (member x (strictly-increasing-path-piece p))
		   (not (endp (remaining-path-piece p))))
	      (consp (neighbors x g)))))

  (local
   (defthm no-duplicatesp-strictly-increasing
     (implies (strictly-increasing-list p)
	      (no-duplicatesp p))))

  (local
   (defthm no-duplicatesp-unitary
     (implies (endp (cdr l))
	      (no-duplicatesp l))))


  (local
   (defthm disjointp-remaining-path-piece-and-strictly-increasing-path-piece
     (implies (and (consp (remaining-path-piece p))
		   (path-p p g)
		   (init-term-dag-p g))
	      (disjointp (remaining-path-piece p)
			 (strictly-increasing-path-piece p)))
     :hints (("Goal" :expand (disjointp (remaining-path-piece p)
					(strictly-increasing-path-piece
					 p))
	      :in-theory (disable disjointp-conmutative))
	     ("Goal'" :use remaining-path-piece-main-property))))


  (local
   (defthm path-p-init-term-dag-p-previous-lemma
     (implies (and (path-p p g)
		   (init-term-dag-p g))
	      (no-duplicatesp
	       (append (strictly-increasing-path-piece p)
		       (remaining-path-piece p))))
     :hints (("Goal"
	      :in-theory
	      (disable
	       strictly-increasing-path-piece-append-remaining-path-piece)
	      :cases ((endp (remaining-path-piece p)))))))



  (local
   (defthm path-p-init-term-dag-p
     (implies (and (path-p p g)
		   (init-term-dag-p g))
	      (no-duplicatesp p))
     :hints (("Goal" :use path-p-init-term-dag-p-previous-lemma))))


  (defthm init-term-dag-p-implies-dag-p
    (implies (init-term-dag-p g)
	     (dag-p g))
    :hints (("Goal" :use dag-p-soundness)))))


;;; -----------------------------------
;;;
;;; 2.3) The property {\tt tree-p-p} implies {\tt dag-p}
;;;
;;; -----------------------------------

;;; This is an easy corollary of the result of the previous section and
;;; the fact that @tree-p@  is a particular case of @init-term-dag-p@:

(local
 (defthm tree-p-aux-implies-init-term-dag-p-aux
   (implies (tree-p-aux hs g)
	    (init-term-dag-p-aux hs g))))

(local
 (defthm tree-p-implies-init-term-dag-p
   (implies (tree-p g)
	    (init-term-dag-p g))
   :hints (("Goal" :in-theory (enable init-term-dag-p)))))


;;; ============================================================================
;;;
;;; 3) About the {\tt tree-p} property of terms stored with {\tt term\--as\--dag\--aux\--l-ns}
;;;
;;; ============================================================================

;;; We now show that, under some conditions, the graph stored by the
;;; function {\tt term-as-dag-aux-ns} has the {\tt tree-p} property:

;;; First, we are prove some interesting properties about the function
;;; {\tt term-as-dag-aux-ns} that will be useful in general:

;;; The available index after storing is an integer bigger than the
;;; input index.  For terms, it is strictly bigger.

(local
 (defthm term-as-dag-aux-ns-increases-index
   (<= h (second (term-as-dag-aux-ns flg term g h)))
   :rule-classes :linear))

(local
 (defthm term-as-dag-aux-ns-increases-index-strictly
   (< h (second (term-as-dag-aux-ns t term g h)))
   :rule-classes :linear))

(local
 (defthm term-as-dag-aux-ns-second-value-integerp
   (implies (integerp h)
	    (integerp (second (term-as-dag-aux-ns flg term g h))))))

;;; The list of indices returned as the third value is a natural true
;;; list that with all its indices bigger than the input index:

(local
 (defthm  term-as-dag-aux-ns-nat-true-listp
   (implies (and (natp h) (term-p-aux flg term))
	    (nat-true-listp
	     (third (term-as-dag-aux-ns flg term g h))))))

(local
 (defthm  term-as-dag-aux-ns-smaller-than-list
   (implies (and (natp h) (natp h1) (< h h1))
	    (smaller-than-list h
			       (third (term-as-dag-aux-ns nil term g h1))))))

;;; The length of the graph finally obtained is bigger (or equal) than
;;; the the first available index returned:

(local
 (defthm len-term-as-dag-aux-ns
   (let* ((res (term-as-dag-aux-ns flg term g h))
	  (gf (first res))
	  (hf (second res)))
     (implies (and (natp h) (or flg (consp term)))
	      (<= hf (len gf))))
   :rule-classes :linear))

;;; All the indices in the list returned are smaller than the first
;;; available index returned:

(local
 (defun bigger-than-list (h l)
   (if (endp l)
       t
     (and (> h (car l))
	  (bigger-than-list h (cdr l))))))


(local
 (defthm term-as-dag-aux-ns-bigger-than-list
   (implies (natp h)
	    (bigger-than-list (second (term-as-dag-aux-ns flg term g h))
			      (third (term-as-dag-aux-ns flg term g h))))))



;;; The following sequence of events leads to show the intended property
;;; for {\tt term-as-dag-aux-ns}.

;;; The elements above the input index are not modified, so the
;;; @tree-p-aux@ property is preserved:

(local
 (defthm term-as-dag-aux-ns-initial-segment-nth
   (implies (and (natp h) (natp h1) (< h h1))
	    (equal (nth h (first (term-as-dag-aux-ns flg term g h1)))
		   (nth h g)))))




(local
 (defthm tree-p-aux-term-as-dag-aux-ns-initial-segment
   (implies (and (natp h) (natp h1) (<= h h1))
	    (equal (tree-p-aux (list-from-to h h1)
			       (first (term-as-dag-aux-ns flg term g h1)))
		   (tree-p-aux (list-from-to h h1) g)))))



;;; Concatenation of list of indices w.r.t. {\tt tree-p-aux}:

(local
 (defthm tree-p-aux-append
   (equal (tree-p-aux (append l1 l2) g)
	  (and (tree-p-aux l1 g) (tree-p-aux l2 g)))))



;;; A particular case, applied to solve one of the induction case of the
;;; theorem below:

(local
 (defthm tree-p-aux-append-particular-case
   (let* ((h1 (second (term-as-dag-aux-ns flg1 term1 g1 h)))
	  (h2 (second (term-as-dag-aux-ns flg2 term2 g2 h1))))
     (implies (natp h)
	      (equal (tree-p-aux (list-from-to h h2) g3)
		     (and (tree-p-aux (list-from-to h h1) g3)
			  (tree-p-aux (list-from-to h1 h2) g3)))))
   :hints (("Goal"
	    :in-theory (disable tree-p-aux-append)
	    :use
	    (:instance
	     tree-p-aux-append
	     (l1 (list-from-to
		  h
		  (second (term-as-dag-aux-ns flg1 term1 g1 h))))
	     (l2 (list-from-to
		  (second
		   (term-as-dag-aux-ns flg1 term1 g1 h))
		  (second
		   (term-as-dag-aux-ns
		    flg2 term2 g2
		    (second (term-as-dag-aux-ns flg1 term1 g1 h))))))

	     (g g3))))))


;;; Above the first available index, the graph is not modified:

(local
 (defthm term-as-dag-aux-ns-final-segment-nth
   (let* ((res (term-as-dag-aux-ns flg term g h1))
	  (hf (second res)))
     (implies (and (natp h) (<= hf h) (natp h1))
	      (equal (nth h (car (term-as-dag-aux-ns flg term g h1)))
		     (nth h g))))))

;;; And finally the intended property about {\tt term-as-dag-aux-ns}:

(local
 (encapsulate
  ()
  (local
   (defthm variable-p-property-element-tree-p
     (implies (variable-p term)
	      (property-element-tree-p h (cons term t)))))


  (local
   (defthm compound-node-property-element-tree-p
     (implies (and (natp h) (natp h1) (< h h1) (term-p-aux nil term))
	      (property-element-tree-p
	       h
	       (cons symb (third (term-as-dag-aux-ns nil term g h1)))))))


  (defthm tree-p-aux-term-as-dag-aux-ns-update-nth
    (implies (and (natp h) (natp h1) (< h h1))
	     (equal (tree-p-aux (list-from-to h1 h2)
				(update-nth h x g))
		    (tree-p-aux (list-from-to h1 h2)  g))))


  (defthm term-as-dag-aux-ns-implies-tree-p-main-lemma
    (let* ((res (term-as-dag-aux-ns flg term g h))
	   (gf (first res))
	   (hf (second res)))
      (implies (and (natp h) (term-p-aux flg term))
	       (tree-p-aux (list-from-to h hf) gf)))
    :hints (("Goal" :in-theory (disable property-element-tree-p))))))


;;; The above property about {\tt tree-p-aux} can be used to prove the
;;; intended property about {\tt tree-p}, but before we need some
;;; technical lemmas:

(local
 (encapsulate
  ()

  (local
   (defthm nth-non-nil
     (implies (and (<= (len l) n) (natp n))
	      (not (nth n l)))))

  (local
   (defthm tree-p-aux-member
     (implies (and (tree-p-aux l g) (member x l))
	      (property-element-tree-p x (nth x g)))
     :rule-classes nil))




  (defthm tree-p-aux-property-element-p
    (implies (and (tree-p g) (natp h))
	     (property-element-tree-p h (nth h g)))
    :hints (("Goal" :cases ((< h (len g))))
	    ("Subgoal 1" :use
	     (:instance tree-p-aux-member
			(x h)
			(l (list-from-to 0 (len g)))))))))


;;; The following sequence of events show the intended result:

(local
 (encapsulate
  ()

  (local
   (defthm term-as-dag-aux-ns-implies-tree-p-initial-segment
     (let* ((res (term-as-dag-aux-ns flg term g h))
	    (gf (first res)))
       (implies (and (natp h) (tree-p g) (subsetp l (list-from-to 0 h)))
		(tree-p-aux l gf)))
     :hints (("Goal"
	      :induct (len l)
	      :in-theory (disable property-element-tree-p)))))

  (local
   (defthm term-as-dag-aux-ns-implies-tree-p-final-segment
     (let* ((res (term-as-dag-aux-ns flg term g h))
	    (gf (first res))
	    (hf (second res)))
       (implies (and (natp h) (tree-p g) (subsetp l (list-from-to hf (len gf))))
		(tree-p-aux l gf)))
     :hints (("Goal"
	      :induct (len l)
	      :in-theory (disable property-element-tree-p)))))

  (local
   (defthm term-as-dag-aux-ns-implies-tree-p-almost
     (let* ((res (term-as-dag-aux-ns flg term g h))
	    (gf (first res))
	    (hf (second res))
	    (l1 (list-from-to 0 h))
	    (l2 (list-from-to h hf))
	    (l3 (list-from-to hf (len gf))))
       (implies (and (natp h) (tree-p g) (term-p-aux flg term))
		(tree-p-aux (append l1 (append l2 l3)) gf)))
     :rule-classes nil))


;; This is the intended result of this section: the term stored by {\tt
;; term-as-dag-aux-ns} verifies {\tt tree-p}:

  (defthm term-as-dag-aux-ns-implies-tree-p
    (implies (and (natp h)
		  (tree-p g)
		  (term-p-aux flg term))
	     (tree-p (first (term-as-dag-aux-ns flg term g h))))
    :hints (("Goal"
	     :cases ((and (not flg) (not (consp term)))))
	    ("Subgoal 2"
	     :in-theory (disable
			 tree-p-aux-append
			 append-list-from-to)
	     :use
	     (term-as-dag-aux-ns-implies-tree-p-almost
	      (:instance append-list-from-to
			 (h1 0) (h2 h)
			 (h3 (cadr (term-as-dag-aux-ns flg term g h))))
	      (:instance append-list-from-to
			 (h1 h)
			 (h2 (cadr (term-as-dag-aux-ns flg term g h)))
			 (h3 (len (car (term-as-dag-aux-ns flg term g h)))))
	      (:instance append-list-from-to
			 (h1 0) (h2 h)
			 (h3 (len (car (term-as-dag-aux-ns flg term g h)))))))))))


;;; ============================================================================
;;;
;;; 4) The term stored using {\tt term-as-dag-aux-ns} is the input term
;;;
;;; ============================================================================

;;; In this section we show that {\tt term-as-dag-aux-ns} builds a
;;; graph that represents the input term. That is, we want to show the
;;; following theorem:

;   (defthm term-as-dag-aux-ns-dag-as-term-aux-relationship
;     (let* ((res (term-as-dag-aux-ns flg term g h))
;            (g-ret (first res))
;	     (hs-ret (third res)))
;       (implies (and (natp h)
;		     (term-p-aux flg term)
;		     (tree-p g))
;		(equal (dag-as-term flg (if flg h hs-ret) g-ret)
;		       term))))


;;; We consider three stage in our proof:

;;; *)
;;;  First we show how the {\tt tree-p} property is related to updating
;;;  the graph. This is esssential to be able to use induction
;;;  hypothesis in the proof of the main result.
;;; *)
;;;  Then we introduce the notion of subgraph, and coincidence in a list
;;;  of indices. We show that when two graphs coincide in a subgraph,
;;;  then the terms stored are the same.
;;; *)
;;;  The above property can be used to use the induction hypothesis in
;;;  the proof of the main theorem, since, for example, it allows to use
;;;  the value of {\tt dag-as-term} in the rest of arguments of a list
;;;  of terms.
;;; *)
;;;  We prove the main theorem by induction on the structure of terms.
;;; -)



;;; -----------------------------------
;;;
;;; 4.1) The property {\tt tree-p} when updating a graph
;;;
;;; -----------------------------------

;;; The following sequence of events are needed to prove the theorems
;;; {\tt tree-p-update-nth-variables} and {\tt
;;; tree-p-update-nth-smaller-than-list} below, showing how the {\tt
;;; tree-p} property is preserved by  the updatings done during the
;;; proccess of {\tt terms-as-dag-l-ns}:

(local
 (encapsulate

  ()


  (local
   (defthm len-update-nth-2
     (implies (natp h) (<= (1+ h) (len (update-nth h x g))))
     :rule-classes :linear))


  (local
   (defthm property-element-tree-p-variable-p
     (implies (variable-p term)
	      (property-element-tree-p h (cons term t)))))

  (local
   (defthm tree-p-aux-update-nth-variables
     (implies (and (tree-p-aux hs g) (variable-p term))
	      (tree-p-aux hs (update-nth h (cons term t) g)))
     :hints (("Goal" :in-theory (disable property-element-tree-p)
	      :induct (len hs)))))

  (local
   (defthm nth-non-nil
     (implies (and (<= (len l) n) (natp n))
	      (not (nth n l)))))

  (local
   (defthm tree-p-aux-list-from-to-beyond-length-lemma
     (implies (and (<= (len g) h1)
		   (natp h1)
		   (subsetp hs (list-from-to (len g) h1)))
	      (tree-p-aux hs g))))

  (local
   (defthm tree-p-aux-list-from-to-beyond-length
     (implies (and (natp h1) (<= (len g) h1)
		   (tree-p-aux (list-from-to 0 (len g)) g))
	      (tree-p-aux (list-from-to 0 h1) g))
     :hints (("Goal"
	      :in-theory (disable
			  tree-p-aux-append
			  append-list-from-to)
	      :use
	      ((:instance append-list-from-to
			  (h1 0) (h2 (len g)) (h3 h1))
	       (:instance tree-p-aux-append
			  (l1 (list-from-to 0 (len g)))
			  (l2 (list-from-to (len g) h1))))))
     :rule-classes nil))

  (local
   (defthm property-element-tree-p-smaller-than-list
     (implies (and (nat-true-listp l)
		   (smaller-than-list h l))
	      (property-element-tree-p h (cons x l)))))


  (local
   (defthm tree-p-aux-update-nth-smaller-than-list
     (implies (and (tree-p-aux hs g)
		   (natp h)
		   (local-nat-listp hs)
		   (nat-true-listp l)
		   (smaller-than-list h l))
	      (tree-p-aux hs (update-nth h (cons x l) g)))
     :hints (("Goal" :in-theory (disable property-element-tree-p)
	      :induct (len hs)))))


;; These are the main theorems in this subsection, establishing that the
;; {\tt tree-p} property is preserved after updating the graph like our
;; function does:

  (defthm tree-p-update-nth-variables
    (implies (and (tree-p g) (variable-p term) (natp h))
	     (tree-p (update-nth h (cons term t) g)))
    :hints (("Goal"
	     :use
	     (:instance tree-p-aux-list-from-to-beyond-length
			(h1 (len (update-nth h (cons term t) g)))))))


  (defthm tree-p-update-nth-smaller-than-list
    (implies (and (tree-p g) (natp h)
		  (nat-true-listp l)
		  (smaller-than-list h l))
	     (tree-p (update-nth h (cons x l) g)))
    :hints (("Goal" :use
	     (:instance tree-p-aux-list-from-to-beyond-length
			(h1 (len (update-nth h (cons x l) g)))))))))

;;; All the needed properties about {\tt tree-p} are now extracted:

(local (in-theory (disable tree-p)))


;;; -----------------------------------
;;;
;;; 4.2) Subgraphs and coincidence in subgraphs.
;;;
;;; -----------------------------------

;;; When proving (by induction on the structure of terms) the main
;;; theorem of this section, one of the induction case is a to prove the
;;; result for non--empty list of terms, having as induction hypothesis
;;; the result for the first term and the result for the list of the
;;; rest of terms. To be able to use the first hypothesis, we must show
;;; that the first term after completing the process it is stored in the
;;; same way as before storing the rest of the terms. And this is true
;;; because every time a subterm is stored in the graph, it is stored in
;;; a subgraph, and subgraphs are "closed" w.r.t. the terms
;;; stored. We prove this in this subsection.


;;; Let us first define the notion of {\em subgraph}. The following
;;; function checks that that all the neighbors (in a graph @g@) of a
;;; list of nodes @hs1@ are a subset of the list of nodes @hs2@:

(local
 (defun subsetp-all-neighbors (hs1 hs2 g)
   (if (endp hs1)
       t
     (and (subsetp (neighbors (car hs1) g) hs2)
	  (subsetp-all-neighbors (cdr hs1) hs2 g)))))

;;; A list of nodes @hs@ is a subgraph of a graph @g@ if all the
;;; neighbors of the nodes of the list are in the same list.

(local
 (defun subgraph-p (hs g)
   (subsetp-all-neighbors hs hs g)))

;;; The following function define the notion of {\em coincidence} in a
;;; set of indices of two given graphs.

(local
 (defun graph-coincide (hs g1 g2)
   (if (endp hs)
       t
     (and (equal (nth (car hs) g1) (nth (car hs) g2))
	  (graph-coincide (cdr hs) g1 g2)))))


;;; Now we show that if we have two directed acyclic graphs such that a
;;; given set of indices form a subgraph and coincide in both subgraphs,
;;; then the function @dag-as-term@ behaves in the same way in both
;;; subgraphs, for every index of the subgraph. The following sequence
;;; of events show this (theorem {\tt
;;; dag-as-term-equal-when-coincide-in-subgraphs} below):

(local
 (encapsulate
  ()

  (local
   (defthm graph-coincide-forward-chaining
     (implies (and (graph-coincide hs g1 g2)
		   (member h hs))
	      (equal (nth h g1) (nth h g2)))
     :rule-classes :forward-chaining))

  (local (in-theory (enable neighbors)))

  (local
   (defthm subsetp-coincide-property-1
     (implies (and (subsetp-all-neighbors hs1 hs2 g)
		   (not (term-dag-variable-p h g))
		   (not (term-dag-is-p h g))
		   (member h hs1))
	      (subsetp (term-dag-args h g) hs2))))

  (local
   (defthm subsetp-coincide-property-2
     (implies (and (subsetp-all-neighbors hs1 hs2 g)
		   (term-dag-is-p h g)
		   (member h hs1))
	      (member (nth h g) hs2))))

  (defthm subsetp-all-neighbors-forward-chaining
    (implies (and (subsetp-all-neighbors hs1 hs2 g1)
		  (graph-coincide hs1 g1 g2))
	     (subsetp-all-neighbors hs1 hs2 g2))
    :rule-classes (:forward-chaining :rewrite))

  (local (in-theory (disable neighbors)))


  (defthm dag-as-term-equal-when-coincide-in-subgraphs
    (implies (and (subgraph-p hs g1)
		  (graph-coincide hs g1 g2)
		  (dag-p g1) (dag-p g2)
		  (if flg (member h hs) (subsetp h hs)))
	     (equal (dag-as-term flg h g1)
		    (dag-as-term flg h g2)))
    :rule-classes :forward-chaining)))


;;; -----------------------------------
;;;
;;; 4.3) Subgraphs and coincidence in {\tt term-as-dag-aux-ns}
;;;
;;; -----------------------------------

;;; We prove now that the terms stored by {\tt term-as-dag-aux-ns} are
;;; subgraphs of the entire graph. And we also prove that if two terms
;;; are stored sequentially, then the graph obtained after storing the
;;; first term coincide, in the subgraph corresponding to that subterm,
;;; with the graph obtained after succesively storing the first and then
;;; the second.

;;; In this way, we can use the result in the previous subsection to
;;; prove two theorems that will allow us to use the induction
;;; hypothesis in the proof of the main theorem in this section.

;;; First, we show the result about coincidence of graphs obtained after
;;; storing two terms sequentially:

(local
 (defthm graph-coincide-term-as-dag-aux-ns
   (implies (and (natp h)
		 (subsetp
		  hs
		  (list-from-to h (second (term-as-dag-aux-ns flg1 term1 g h)))))
	    (graph-coincide
	     hs
	     (first (term-as-dag-aux-ns flg1 term1 g h))
	     (first (term-as-dag-aux-ns
		     flg2 term2
		     (first (term-as-dag-aux-ns flg1 term1 g h))
		     (second (term-as-dag-aux-ns flg1 term1 g h))))))
   :hints (("Goal" :induct (len hs)))))



;;; And now, the following sequence of events show that the nodes of the
;;; graph used to store a term are a subgraph of the entire graph:

(local
 (encapsulate
  ()
  (local
   (defthm subsetp-all-neighbors-append
     (implies (and (subsetp-all-neighbors hs11 hs12 g)
		   (subsetp-all-neighbors hs21 hs22 g))
	      (subsetp-all-neighbors (append hs11 hs21)
				     (append hs12 hs22)
				     g))))

  (local
   (defthm very-ugly-lemma
     (let* ((ret-term1 (term-as-dag-aux-ns t term1 g h))
	    (g-term1 (first ret-term1))
	    (h1 (second ret-term1))
	    (ret-term2  (term-as-dag-aux-ns nil term2 g-term1 h1))
	    (g-term2 (first ret-term2))
	    (h2 (second ret-term2))
	    (l1 (list-from-to h h1))
	    (l2 (list-from-to h1 h2))
	    (l (list-from-to h h2)))
       (implies (and (natp h)
		     (subsetp-all-neighbors l1 l1 g-term2)
		     (subsetp-all-neighbors l2 l2 g-term2))
		(subsetp-all-neighbors l l g-term2)))
     :hints (("Goal" :use
	      (:instance
	       subsetp-all-neighbors-append
	       (hs11 (list-from-to h (second (term-as-dag-aux-ns t term1 g h))))
	       (hs12 (list-from-to h (second (term-as-dag-aux-ns t term1 g h))))
	       (hs21 (list-from-to
		      (second (term-as-dag-aux-ns t term1 g h))
		      (second (term-as-dag-aux-ns
			       nil term2
			       (first (term-as-dag-aux-ns t term1 g h))
			       (second (term-as-dag-aux-ns t term1 g h))))))
	       (hs22 (list-from-to
		      (second (term-as-dag-aux-ns t term1 g h))
		      (second (term-as-dag-aux-ns
			       nil term2
			       (first (term-as-dag-aux-ns t term1 g h))
			       (second (term-as-dag-aux-ns t
							     term1 g h))))))
	       (g (first (term-as-dag-aux-ns
			  nil term2
			  (first (term-as-dag-aux-ns t term1 g h))
			  (second (term-as-dag-aux-ns t term1 g
							h))))))))))



  (local
   (defthm subsetp-all-neighbors-coincide-particular-case
     (let* ((ret-term (term-as-dag-aux-ns flg term g h))
	    (g-term1 (first ret-term))
	    (h1 (second ret-term))
	    (hs (list-from-to h h1))
	    (g-term2 (first (term-as-dag-aux-ns flg2 term2 g-term1 h1))))
       (implies (and (natp h) (subsetp-all-neighbors hs hs g-term1))
		(subsetp-all-neighbors hs hs g-term2)))))

  (local
   (defthm subsetp-all-neighbors-cons-second-argument-lemma
     (implies (subsetp-all-neighbors l1 l2 g)
	      (subsetp-all-neighbors l1 (cons x l2) g))))

  (local
   (defthm subsetp-all-neighbors-cons-second-argument
     (implies (and (subsetp (neighbors x g) l)
		   (subsetp-all-neighbors l l g))
	      (subsetp-all-neighbors (cons x l) (cons x l) g))))

  (local
   (defthm subsetp-all-neighbors-update-nth-not-member
     (implies (and (not (member h hs1))
		   (natp h)
		   (nat-true-listp hs1)
		   (subsetp-all-neighbors hs1 hs2 g))
	      (subsetp-all-neighbors hs1 hs2 (update-nth h x g)))
     :hints (("Goal" :in-theory (enable neighbors)))))

  (local
   (defthm nat-true-listp-list-from-to
     (implies (natp h)
	      (nat-true-listp (list-from-to h h1)))))

  (defthm  term-as-dag-aux-ns-local-nat-listp
    (let* ((res (term-as-dag-aux-ns flg term g h))
	   (hs-ret (third res)))
      (implies (natp h)
	       (local-nat-listp hs-ret))))

  (defthm subsetp-list-from-to
    (implies
     (and (natp h1) (natp h2)
	  (local-nat-listp hs)
	  (smaller-than-list h1 hs)
	  (bigger-than-list h2 hs))
     (subsetp hs (list-from-to (1+ h1) h2))))

   (defthm subgraph-p-term-as-dag-aux-ns
     (implies (natp h)
	      (subgraph-p
	       (list-from-to
		h
		(second (term-as-dag-aux-ns flg term g h)))
	       (first (term-as-dag-aux-ns flg term g h))))
     :hints (("Goal" :in-theory (enable neighbors))))))


(local (in-theory (disable subgraph-p)))



;;; -----------------------------------
;;;
;;; 4.4) The main result of this section
;;;
;;; -----------------------------------


;;; We apply the results of the previous subsections to prove the main
;;; lemmas needed to deal with two induction hypothesis in the proof of
;;; the main result of this subsection.


(local
 (encapsulate
  ()

;; This lemma allows to use one the induction hypothesis (the one for
;; the first term of the list) in the induction case corresponding to
;; non-empty list of terms:

  (local
   (defthm equal-dag-as-term-composition-of-term-as-dag
     (let* ((ret-term1 (term-as-dag-aux-ns t term1 g h))
	    (g-term1 (first ret-term1))
	    (h1 (second ret-term1))
	    (ret-term2 (term-as-dag-aux-ns nil term2 g-term1 h1))
	    (g-term2 (first ret-term2)))
       (implies (and (natp h) (tree-p g)
		     (term-p-aux t term1) (term-p-aux nil term2))
		(equal (dag-as-term t h g-term2)
		       (dag-as-term t h g-term1))))
     :hints (("Goal" :use
	      (:instance
	       dag-as-term-equal-when-coincide-in-subgraphs
	       (flg t)
	       (g1 (first (term-as-dag-aux-ns t term1 g h)))
	       (g2 (first
		    (term-as-dag-aux-ns
		     nil term2
		     (first
		      (term-as-dag-aux-ns t term1 g h))
		     (second (term-as-dag-aux-ns t term1 g h)))))

	       (hs (list-from-to
		    h (second (term-as-dag-aux-ns t term1 g h)))))))))

  (local
   (defthm graph-coincide-update-nth
     (implies (and (not (member h hs)) (natp h) (local-nat-listp hs))
	      (graph-coincide hs g (update-nth h x g)))))

  (local
   (defthm list-from-to-local-nat-listp
     (implies (and (natp h1) (natp h2))
	      (local-nat-listp (list-from-to h1 h2)))))



;; And this lemma allows to use the induction hypothesis (the one for
;; the list of its arguments) corresponding to the induction case of
;; non-variable terms:


  (local
   (defthm equal-dag-as-term-update-nth
     (implies
      (and (natp h)
	   (term-p-aux nil term)
	   (tree-p g))
      (equal
       (dag-as-term
	nil
	(third (term-as-dag-aux-ns nil term g (+ 1 h)))
	(update-nth h
		    (cons f (third (term-as-dag-aux-ns nil term g (1+ h))))
		    (first (term-as-dag-aux-ns nil term g (+ 1 h)))))
       (dag-as-term
	nil
	(third (term-as-dag-aux-ns nil term g (+ 1 h)))
	(first (term-as-dag-aux-ns nil term g (+ 1 h))))))
     :hints
     (("Goal"
       :use
       (:instance
	dag-as-term-equal-when-coincide-in-subgraphs
	(flg nil)
	(h (third (term-as-dag-aux-ns nil term g (+ 1 h))))
	(g1 (first (term-as-dag-aux-ns nil term g (+ 1 h))))
	(g2 (update-nth
	     h
	     (cons f (third (term-as-dag-aux-ns nil term g (1+ h))))
	     (first (term-as-dag-aux-ns nil term g (+ 1 h)))))
	(hs (list-from-to
	     (1+ h)
	     (second (term-as-dag-aux-ns nil term g (+ 1 h))))))))))

;; And finally the intended result of this section:

  (local
   (defthm term-as-dag-aux-ns-dag-as-term-aux-relationship
     (let* ((res (term-as-dag-aux-ns flg term g h))
	    (g-ret (first res))
	    (hs-ret (third res)))
       (implies (and (natp h)
		     (term-p-aux flg term)
		     (tree-p g))
		(equal (dag-as-term flg (if flg h hs-ret) g-ret)
		       term)))
     :rule-classes nil))

;; This result is better used in form of a rewriting rule:

  (defthm term-as-dag-aux-ns-dag-as-term-aux-relationship-rewrite-rule
    (let* ((res (term-as-dag-aux-ns flg term g h))
	   (g-ret (first res))
	   (hs-ret (third res)))
      (implies (and (natp h)
		    (term-p-aux flg term)
		    (tree-p g)
		    (equal h1 (if flg h hs-ret)))
	       (equal (dag-as-term flg h1 g-ret)
		      term)))
    :hints (("Goal"
	     :use term-as-dag-aux-ns-dag-as-term-aux-relationship)))))


;;; ============================================================================
;;;
;;; 5) Relationship between {\tt terms\--as\--dag\--aux\--l-ns} and {\tt terms\--as-dag\--aux\--l}
;;;
;;; ============================================================================

;;; Our goal in this subsection is to prove the following theorem:


;  (defthm term-as-dag-aux-in-two-steps
;    (let* ((res1 (term-as-dag-aux flg term g h variables))
;	    (g-ret1 (first res1))
;	    (res2  (term-as-dag-aux-ns flg term g h))
;	    (g-ret2 (first res2))
;	    (h-ret2 (second res2)))
;      (implies (and (natp h)
;		    (term-p-aux flg term))
;	        (equal g-ret1
;		       (first (make-shared-variables h h-ret2 g-ret2 variables))))

;;; That is, we are going to prove that the graph obtained after storing
;;; a term using the function {\tt term-as-dag-aux} is the same than
;;; the graph obtained storing the same term with {\tt
;;; term-as-dag-aux-ns} and after that applying {\tt
;;; make-shared-variables}.



;;; The following two properties show that the second value returned by
;;; term-as-dag-aux is a natural number (that is, the first available
;;; index after storing the graph).

(local
 (defthm integerp-term-as-dag-aux
   (implies (integerp h)
	    (integerp (second (term-as-dag-aux flg term g h variables))))))

(local
 (defthm integerp-term-as-dag-aux-natp
   (implies (natp h)
	    (>= (second (term-as-dag-aux flg term g h variables)) 0))
   :rule-classes :linear))



;;; Now we establish some properties about the function {\tt
;;; make-shared-variables} (see its definition in Section 1):


;;; First, a property about updating the result of a {\tt
;;; make-shared-variables} outside the range where the sharing of
;;; variables occur.

(local
 (defthm update-nth-update-nth-disjoint
   (implies (and (natp h1) (natp h2) (< h2 h1))
	    (equal (update-nth h1 x (update-nth h2 y g))
		   (update-nth h2 y (update-nth h1 x g))))))


(local
 (defthm make-shared-variables-update-nth-disjoint-graph
   (implies
    (and (natp h) (natp h1) (natp h2) (< h h1) (<= h1 h2))
    (equal
     (first (make-shared-variables
	     h1 h2 (update-nth h x g) variables))
     (update-nth h x (first (make-shared-variables h1 h2 g variables)))))
   :hints (("Goal" :induct (make-shared-variables h1 h2 g variables))
	   ("Subgoal *1/4.2" :expand (make-shared-variables h1 h2 (update-nth h x g)
							    variables))
	   ("Subgoal *1/3.2" :expand (make-shared-variables h1 h2 (update-nth h x g)
							    variables))
	   ("Subgoal *1/2.2" :expand (make-shared-variables h1 h2 (update-nth h x g)
							    variables)))))

;;; A fundamental lemma, describing how make shared variables can be
;;; done in several stages:

(local
 (defthm make-shared-composition
   (implies (and (<= h1 h2) (<= h2 h3)
		 (natp h1) (natp h2) (natp h3))
	    (equal (make-shared-variables h1 h3 g variables)
		   (make-shared-variables
		    h2 h3
		    (first (make-shared-variables h1 h2 g variables))
		    (second (make-shared-variables h1 h2 g variables)))))
   :rule-classes nil))

;;; The following two lemmas show that some nodes of the original graph
;;; do not change after making the variables shared:


(local
 (defthm nth-make-shared-variables
   (implies (and (natp h) (natp h1) (natp h2) (< h h1))
	    (equal (nth h
			(car
			 (make-shared-variables h1 h2 g variables)))
		   (nth h g)))))


(local
 (defthm make-shared-variables-does-not-change-non-variables
   (implies (not (term-dag-variable-p h g))
	    (equal (nth
		    h
		    (first (make-shared-variables h1 h2 g variables)))
		   (nth h g)))))



;;; The following @encapsulate@ contains the lemmas and definitions
;;; needed to deal with all the induction cases of the goal theorem in
;;; this section.



(local
 (encapsulate
  ()
  (local
   (defun induct-hint-for-last-index-independent-of-graph
     (flg term g1 g2 h)
     (if flg
	 (if (variable-p term)
	     (list g1 g2 h)
	   (induct-hint-for-last-index-independent-of-graph
	    nil (cdr term) g1 g2 (1+ h)))
       (if (endp term)
	   t
	 (mv-let (g1-n hcar ign)
		 (term-as-dag-aux-ns t (car term) g1 h)
		 (declare (ignore ign))
		 (mv-let (g2-n ign1 ign2)
			 (term-as-dag-aux-ns t (car term) g2 h)
			 (declare (ignore ign1 ign2))
			 (and (induct-hint-for-last-index-independent-of-graph
			       t (car term) g1 g2 h)
			      (induct-hint-for-last-index-independent-of-graph
			       nil (cdr term) g1-n g2-n hcar))))))))


;; The second and third values returned by {\tt term-as-dag-aux-ns} do
;; not depend on the graph:

  (local
   (defthm last-index-independent-of-graph
     (and
      (equal (second (term-as-dag-aux-ns flg term g1 h))
	     (second (term-as-dag-aux-ns flg term g2 h)))
      (equal (third (term-as-dag-aux-ns flg term g1 h))
	     (third (term-as-dag-aux-ns flg term g2 h))))

     :hints (("Goal"
	      :induct
	      (induct-hint-for-last-index-independent-of-graph
	       flg term g1 g2 h)))
     :rule-classes nil))


;; The second and third values returned by {\tt term-as-dag-aux-ns}
;; and {\tt term-as-dag-aux} are the same:


  (local
   (defthm term-as-dag-aux-ns-term-as-dag-aux-equal-second-argument
     (equal (second (term-as-dag-aux flg term g h variables))
	    (second (term-as-dag-aux-ns flg term g h)))
     :hints (("Subgoal *1/4'''" :use
	      (:instance last-index-independent-of-graph
			 (flg nil) (term term2)
			 (h (cadr (term-as-dag-aux-ns t term1 g h)))
			 (g1 (car (term-as-dag-aux t term1 g h
						     variables)))
			 (g2 (car (term-as-dag-aux-ns t term1 g h))))))))

  (local
   (defthm term-as-dag-aux-ns-term-as-dag-aux-equal-third-argument
     (equal (third (term-as-dag-aux flg term g h variables))
	    (third (term-as-dag-aux-ns flg term g h)))
     :hints (("Subgoal *1/4'''" :use
	      (:instance last-index-independent-of-graph
			 (flg nil) (term term2)
			 (h (cadr (term-as-dag-aux-ns t term1 g h)))
			 (g1 (car (term-as-dag-aux t term1 g h
						     variables)))
			 (g2 (car (term-as-dag-aux-ns t term1 g h))))))))



;; The following (very long lemmas) deal with induction case 4 of the
;; induction proof of our main goal:

  (local
   (defthm last-index-independent-of-graph-particular-case
     (equal
      (cadr
       (term-as-dag-aux-ns nil term2
			     (car (term-as-dag-aux t term1 g h variables))
			     (cadr (term-as-dag-aux-ns t term1 g h))))

      (cadr (term-as-dag-aux-ns nil term2
				  (car (term-as-dag-aux-ns t term1 g h))
				  (cadr (term-as-dag-aux-ns t term1 g
							      h)))))
     :hints (("Goal"
	      :use
	      (:instance last-index-independent-of-graph
			 (flg nil) (term term2)
			 (h (cadr (term-as-dag-aux-ns t term1 g h)))
			 (g1 (car (term-as-dag-aux t term1 g h
						     variables)))
			 (g2 (car (term-as-dag-aux-ns t term1 g h))))))))

  (local
   (defthm update-nth-term-as-dag-aux-ns-below
     (implies (and (natp h1) (natp h2) (< h1 h2))
	      (equal
	       (first (term-as-dag-aux-ns
		       flg term (update-nth h1 x g) h2))
	       (update-nth h1 x
			   (first (term-as-dag-aux-ns
				   flg term g h2)))))
     :hints (("Goal" :induct (term-as-dag-aux-ns
			      flg term g h2))
	     ("Subgoal *1/4.1'"
	      :use (:instance last-index-independent-of-graph
			      (flg t) (term term1)
			      (h h2)
			      (g1 (update-nth h1 x g)) (g2 g)))
	     ("Subgoal *1/2.1''"
	      :use (:instance last-index-independent-of-graph
			      (flg nil) (term term2) (g1 g) (h (+ 1 h2))
			      (g2 (update-nth h1 x g)))))))

  (local
   (defthm make-shared-variables-terms-as-dag-aux-l-ns-graph
     (implies (and (natp h1) (natp h2))
	      (equal (first
		      (make-shared-variables
		       h1 h2
		       (car (term-as-dag-aux-ns flg term g h2))
		       variables))
		     (first
		      (term-as-dag-aux-ns
		       flg term (car (make-shared-variables h1 h2 g
							    variables))
		       h2))))))

  (local
   (defthm make-shared-variables-terms-as-dag-aux-l-ns-variables
     (implies (and (natp h1) (natp h2))
	      (equal (second
		      (make-shared-variables
		       h1 h2
		       (car (term-as-dag-aux-ns flg term g h2))
		       variables))
		     (second
		      (make-shared-variables h1 h2 g variables))))
     :hints (("Goal" :induct (make-shared-variables h1 h2 g variables)))))


  (local
   (defthm induction-case-4-term-as-dag-aux-in-two-steps-graph
     (implies
      (and
       (equal
	(first (make-shared-variables h
				      (second (term-as-dag-aux-ns t term1 g h))
				      (first (term-as-dag-aux-ns t term1 g h))
				      variables))
	(first (term-as-dag-aux t term1 g h variables)))
       (equal
	(second (make-shared-variables h
				       (second (term-as-dag-aux-ns t term1 g h))
				       (first (term-as-dag-aux-ns t term1 g h))
				       variables))
	(fourth (term-as-dag-aux t term1 g h variables)))
       (equal
	(first
	 (make-shared-variables
	  (second (term-as-dag-aux-ns t term1 g h))
	  (second
	   (term-as-dag-aux-ns nil term2
                              (first (term-as-dag-aux t term1 g h variables))
                              (second (term-as-dag-aux-ns t term1 g h))))
	  (first
	   (term-as-dag-aux-ns nil term2
				 (first (term-as-dag-aux t term1 g h variables))
				 (second (term-as-dag-aux-ns t term1 g h))))
	  (fourth (term-as-dag-aux t term1 g h variables))))
	(first
	 (term-as-dag-aux nil term2
			    (first (term-as-dag-aux t term1 g h variables))
			    (second (term-as-dag-aux-ns t term1 g h))
			    (fourth (term-as-dag-aux t term1 g h variables)))))
       (equal
	(second
	 (make-shared-variables
	  (second (term-as-dag-aux-ns t term1 g h))
	  (second
	   (term-as-dag-aux-ns nil term2
				 (first (term-as-dag-aux t term1 g h variables))
				 (second (term-as-dag-aux-ns t term1 g h))))
	  (first
	   (term-as-dag-aux-ns nil term2
				 (first (term-as-dag-aux t term1 g h variables))
				 (second (term-as-dag-aux-ns t term1 g h))))
	  (fourth (term-as-dag-aux t term1 g h variables))))
	(fourth
	 (term-as-dag-aux nil term2
			    (first (term-as-dag-aux t term1 g h variables))
			    (second (term-as-dag-aux-ns t term1 g h))
			    (fourth (term-as-dag-aux t term1 g h variables)))))
       (natp h))
      (equal
       (first
	(make-shared-variables
	 h
	 (second (term-as-dag-aux-ns nil term2
				       (first (term-as-dag-aux-ns t term1 g h))
				       (second (term-as-dag-aux-ns t term1 g h))))
	 (first (term-as-dag-aux-ns nil term2
				      (first (term-as-dag-aux-ns t term1 g h))
				      (second (term-as-dag-aux-ns t term1 g h))))
      variables))
       (first
	(term-as-dag-aux nil term2
			   (first (term-as-dag-aux t term1 g h variables))
			   (second (term-as-dag-aux-ns t term1 g h))
			   (fourth (term-as-dag-aux t term1 g h variables))))))
     :hints (("Goal" :use
	   (:instance make-shared-composition
		      (h1 h)
		      (h2 (cadr (term-as-dag-aux-ns t term1 g h)))
		      (h3 (cadr (term-as-dag-aux-ns
				 nil term2
				 (car (term-as-dag-aux-ns t term1 g h))
				 (cadr (term-as-dag-aux-ns t term1 g h)))))
		      (g (car (term-as-dag-aux-ns
			       nil term2
			       (car (term-as-dag-aux-ns t term1 g h))
			       (cadr (term-as-dag-aux-ns t term1 g h))))))))))



  (local
   (defthm induction-case-4-term-as-dag-aux-in-two-steps-variable
     (implies
      (and
       (equal
	(first (make-shared-variables h
				    (second (term-as-dag-aux-ns t term1 g h))
				    (first (term-as-dag-aux-ns t term1 g h))
				    variables))
	(first (term-as-dag-aux t term1 g h variables)))
       (equal
	(second (make-shared-variables h
				     (second (term-as-dag-aux-ns t term1 g h))
				     (first (term-as-dag-aux-ns t term1 g h))
				     variables))
	(fourth (term-as-dag-aux t term1 g h variables)))
       (equal
	(first
	 (make-shared-variables
	  (second (term-as-dag-aux-ns t term1 g h))
	  (second (term-as-dag-aux-ns nil term2
				      (first (term-as-dag-aux-ns t term1 g h))
				      (second (term-as-dag-aux-ns t term1 g h))))
	  (first
	   (term-as-dag-aux-ns nil term2
				 (first (term-as-dag-aux t term1 g h variables))
				 (second (term-as-dag-aux-ns t term1 g h))))
	  (fourth (term-as-dag-aux t term1 g h variables))))
	(first
	 (term-as-dag-aux nil term2
			    (first (term-as-dag-aux t term1 g h variables))
			    (second (term-as-dag-aux-ns t term1 g h))
			    (fourth (term-as-dag-aux t term1 g h variables)))))
       (equal
	(second
	 (make-shared-variables
	  (second (term-as-dag-aux-ns t term1 g h))
	  (second (term-as-dag-aux-ns nil term2
				      (first (term-as-dag-aux-ns t term1 g h))
				      (second (term-as-dag-aux-ns t term1 g h))))
	  (first
	   (term-as-dag-aux-ns nil term2
				 (first (term-as-dag-aux t term1 g h variables))
				 (second (term-as-dag-aux-ns t term1 g h))))
	  (fourth (term-as-dag-aux t term1 g h variables))))
	(fourth
	 (term-as-dag-aux nil term2
			    (first (term-as-dag-aux t term1 g h variables))
			    (second (term-as-dag-aux-ns t term1 g h))
			    (fourth (term-as-dag-aux t term1 g h variables)))))
       (natp h))
      (equal
       (second
	(make-shared-variables
	 h
	 (second (term-as-dag-aux-ns nil term2
				     (first (term-as-dag-aux-ns t term1 g h))
				     (second (term-as-dag-aux-ns t term1 g h))))
	 (first (term-as-dag-aux-ns nil term2
				    (first (term-as-dag-aux-ns t term1 g h))
				    (second (term-as-dag-aux-ns t term1 g h))))
	 variables))
       (fourth
	(term-as-dag-aux nil term2
			   (first (term-as-dag-aux t term1 g h variables))
			   (second (term-as-dag-aux-ns t term1 g h))
			   (fourth (term-as-dag-aux t term1 g h
						   variables))))))
     :hints (("Goal" :use
	      (:instance
	       make-shared-composition
	       (h1 h)
	       (h2 (second (term-as-dag-aux-ns t term1 g h)))
	       (h3 (second (term-as-dag-aux-ns
			  nil term2
			  (first (term-as-dag-aux-ns t term1 g h))
			  (second (term-as-dag-aux-ns t term1 g h)))))
	       (g (first (term-as-dag-aux-ns
			nil term2
			(first (term-as-dag-aux-ns t term1 g h))
			(second (term-as-dag-aux-ns t term1 g h))))))))))


;; The following deal with induction case 2 of the induction proof of
;; our main goal:


  (local
   (defthm update-nth-update-nth-at-the-same-index
     (equal (update-nth h y (update-nth h x g))
	    (update-nth h y g))))


  (local
   (defthm make-shared-variables-non-variable-term
     (implies
      (and (natp h) (natp h2) (<= h h2)
	   (nat-true-listp l))
      (equal
       (make-shared-variables
	h h2 (update-nth h (cons f l) g) variables)
       (make-shared-variables
	(1+ h) h2 (update-nth h (cons f l) g) variables)))))


  (local
   (defthm make-shared-variables-update-nth-disjoint-variables
     (implies
      (and (natp h) (natp h1) (natp h2) (< h h1) (<= h1 h2))
      (equal
       (cadr (make-shared-variables
	      h1 h2 (update-nth h x g) variables))
       (cadr (make-shared-variables h1 h2 g variables))))
     :hints (("Goal" :induct (make-shared-variables h1 h2 g variables))
	     ("Subgoal *1/4.2"
	      :expand (make-shared-variables h1 h2 (update-nth h x g) variables))
	     ("Subgoal *1/3.2"
	      :expand (make-shared-variables h1 h2 (update-nth h x g) variables))
	     ("Subgoal *1/2.2"
	      :expand (make-shared-variables h1 h2 (update-nth h x g) variables)))))


;; The following deals with base case 1 of the induction proof of our
;; main goal. Note that the lemma is needed because in some cases
;; the definition of {\tt make-shared-variables} is not expanded.

  (local
   (defthm make-shared-variables-one-position-one-variable
     (implies (and (variable-p term)
		   (natp h))
	      (equal (make-shared-variables
		      h (1+ h) (update-nth h (cons term t) g) variables)
		     (if (assoc term variables)
			 (list
			  (update-nth h (cdr (assoc term variables)) g)
			  variables)
		       (list (update-nth h (cons term t) g)
			     (cons (cons term h) variables)))))))



;; And finally, the intended result, proved by induction on the
;; structure of @term@

  (defthm term-as-dag-aux-in-two-steps
    (let* ((res1 (term-as-dag-aux flg term g h variables))
	   (g-ret1 (first res1))
	   (var-ret1 (fourth res1))
	   (res2  (term-as-dag-aux-ns flg term g h))
	   (g-ret2 (first res2))
	   (h-ret2 (second res2)))
      (implies (and (natp h)
		    (term-p-aux flg term))
	       (and (equal g-ret1
			   (first (make-shared-variables h h-ret2 g-ret2 variables)))
		    (equal var-ret1
			   (second (make-shared-variables h h-ret2 g-ret2
							  variables)))))))))


;;; ============================================================================
;;;
;;; 6) Sharing variables preserves {\tt dag-p}
;;;
;;; ============================================================================

;;; Our intention in this section is to prove a theorem that will allow
;;; us to conclude that after applying {\tt make-shared-variables} to
;;; the graph obtained by {\tt term-as-dag-aux-ns} we obtain a graph
;;; thta verifies the {\tt init-term-dag-p} property and, consequently,
;;; the {\tt dag-p} property. Since we have proved in section 3 that the
;;; graph obtained by {\tt term-as-dag-aux-ns} verifies {\tt tree-p}
;;; then the following theorem will be our final goal in this section:


;  (defthm init-term-dag-p-make-shared-variables
;    (implies (and (natp h1) (natp h2) (<= h1 h2) (<= h2 (len g))
;		  (tree-p g) (variables-well-stored-p h1 g variables))
;	     (init-term-dag-p
;	      (first (make-shared-variables h1 h2 g variables)))))

;;; This theorem will be a particular case of a more general theorem
;;; that can be proved by induction. The function {\tt
;;; variables-well-stored-p} defines some kind of "invariant" during the
;;; proccess of making variables shared; it defines how the association
;;; list computed by {\tt make-shared-variables} is related to the "piece"
;;; of graph already processed.

;;; -----------------------------------
;;;
;;; 6.1) Definition of the invariant
;;;
;;; -----------------------------------


;;; As we have said above, the following definition formalizes some kind
;;; of "invariant" during the proccess of making variables shared; it
;;; defines how the association list computed by {\tt
;;; make-shared-variables} is related to the "piece" of graph already
;;; processed. Intuitively, it establishes that the association list
;;; @variables@ binds the variable nodes of the graph @g@ to the index
;;; of the nodes of the graph where they appear, for all the nodes with
;;; index less than @h@. That is, if we have made variables shared in
;;; @g@ until index @h-1@ then {\tt ((variables-well-stored-p h g
;;; variables)} where @vraibles@ is the association list computed {\tt
;;; make-shared-variables} up to that moment.

(local
 (defun variables-well-stored-p (h g variables)
   (cond ((zp h) (equal variables nil))
	 ((term-dag-variable-p (1- h) g)
	  (and (equal (term-dag-symbol (1- h) g) (caar variables))
	       (equal (cdar variables) (1- h))
	       (variables-well-stored-p (1- h) g (cdr variables))))
	 (t (variables-well-stored-p (1- h) g variables)))))


;;; Now we prove some properties about @variables-well-stored-p@. For
;;; example, if {\tt (variables-well-stored-p h1 g variables)}, then in
;;; the association list @variables@ the variables are bound to
;;; natural numbers strictly less than the index @h1@, and those numbers
;;; point to variable nodes in the graph.

(local
 (defthm variables-well-stored-p-integerp
   (implies (and (variables-well-stored-p h1 g variables)
		 (assoc x variables))
	    (integerp (cdr (assoc x variables))))
   :rule-classes :type-prescription))

(local
 (defthm variables-well-stored-p-positive
   (implies (and (variables-well-stored-p h1 g variables)
		 (assoc x variables))
	    (<= 0 (cdr (assoc x variables))))
   :rule-classes :linear))



(local
 (defthm variables-well-stored-p-index-less-than
   (implies (and (variables-well-stored-p h1 g variables)
		 (natp h1)
		 (assoc x variables))
	    (< (cdr (assoc x variables)) h1))
   :rule-classes :linear))



(local
 (defthm variables-well-stored-p-index-stores-variables
   (implies (and (variables-well-stored-p h1 g variables)
		 (natp h1)
		 (assoc x variables))
	    (term-dag-variable-p (cdr (assoc x variables)) g))))


;;; These two lemmas establish how updating affects to {\tt
;;; variables-well-stored-p}:

(local
 (defthm variales-well-stored-p-update-nth-above-the-index
   (implies (and (natp h1) (natp h2) (<= h1 h2))
	    (equal (variables-well-stored-p h1 (update-nth h2 x g)
					    variables)
		   (variables-well-stored-p h1 g variables)))
   :hints (("Goal" :induct (variables-well-stored-p h1 g variables))
	   ("Subgoal *1/5"
	    :expand
	    (variables-well-stored-p h1 (update-nth h2 x g) variables)))))


(local
 (defthm variables-well-stored-p-update-nth-at-the-index
   (implies (and (assoc (car (nth h1 g)) variables)
		 (natp h1)
		 (variables-well-stored-p h1 g variables))
	    (variables-well-stored-p
	     (+ 1 h1)
	     (update-nth h1
			 (cdr (assoc (car (nth h1 g)) variables))
			 g)
	     variables))
   :hints (("Goal" :expand (variables-well-stored-p
			    (+ 1 h1)
			    (update-nth h1
					(cdr (assoc (car (nth h1 g)) variables))
					g)
			    variables)))))


;;; -----------------------------------
;;;
;;; 6.2) Proving the invariant and the intended property
;;;
;;; -----------------------------------


;;; The following sequence of events helps to prove the lemma {\tt
;;; init-term-dag-p-make-shared-variables-main-lemma}, which describes
;;; the main invariant related to the {\tt init-term-dag-p} property
;;; during the proccess. The goal theorem in this section will be a
;;; particular case of that lemma.

(local
 (encapsulate
  ()

  (local
   (defthm init-term-dag-p-aux-append
     (equal (init-term-dag-p-aux (append hs1 hs2) g)
	    (and (init-term-dag-p-aux hs1 g)
		 (init-term-dag-p-aux hs2 g)))))



;; Needed for {\tt Subgoal *1/4.3}



  (local
   (defthm property-element-tree-p-property-element-init-term-dag-p
     (implies (property-element-tree-p h node)
	      (property-element-init-term-dag-p h node g))))


  (local
   (in-theory (disable property-element-tree-p
		       property-element-init-term-dag-p)))


  (local
   (defthm init-term-dag-p-aux-property-element-tree-p-lemma
     (implies (and (natp h1) (natp h0) (<= h0 h1)
		   (init-term-dag-p-aux (list-from-to h0 h1) g)
		   (property-element-tree-p h1 (nth h1 g)))
	      (init-term-dag-p-aux (append (list-from-to h0 h1)
					   (list-from-to h1 (1+ h1)))
				   g))))

  (local
   (defthm init-term-dag-p-aux-property-element-tree-p
     (implies (and (natp h1) (natp h0) (<= h0 h1)
		   (init-term-dag-p-aux (list-from-to h0 h1) g)
		   (property-element-tree-p h1 (nth h1 g)))
	      (init-term-dag-p-aux (list-from-to h0 (1+ h1))
				  g))
     :hints (("Goal" :use init-term-dag-p-aux-property-element-tree-p-lemma
	      :in-theory (disable list-from-to)))))


  (local
   (defthm tree-p-aux-implies-property-element-tree-p
     (implies (and (natp h1) (natp h2) (< h1 h2)
		   (tree-p-aux (list-from-to h1 h2) g))
	      (property-element-tree-p h1 (nth h1 g)))))

  (local
   (defthm init-term-dag-p-aux-one-index-beyond
     (implies (and (tree-p-aux (list-from-to h1 h2) g)
		   (natp h1) (natp h2) (< h1 h2) (natp h0) (<= h0 h1)
		   (init-term-dag-p-aux (list-from-to h0 h1) g))
	      (init-term-dag-p-aux (list-from-to h0 (1+ h1)) g))
     :hints (("Goal"
	      :use init-term-dag-p-aux-property-element-tree-p))))

;; Needed for {\tt Subgoal *1/4.2}

  (local
   (defthm variables-well-stored-p-variables-one-index-beyond
     (implies (and (not (term-dag-variable-p h1 g))
		   (variables-well-stored-p h1 g variables))
	      (variables-well-stored-p (1+ h1) g variables))))



;; Needed for {\tt Subgoal *1/4.1}

  (local
   (defthm tree-p-aux-one-index-less
     (implies (and (natp h1) (natp h2) (< h1 h2)
		   (tree-p-aux (list-from-to h1 h2) g))
	      (tree-p-aux (list-from-to (1+ h1) h2) g))))


;; Needed for {\tt Subgoal *1/3.1}

  (local
   (defthm variables-well-stored-p-one-step-beyond
     (implies (and (natp h1)
		   (term-dag-variable-p h1 g)
		   (variables-well-stored-p h1 g variables))
	      (variables-well-stored-p (1+ h1) g
				       (cons (cons (car (nth h1 g)) h1)
					     variables)))))


;; Needed for {\tt Subgoal *1/2.2'}

  (local
   (defthm variables-well-stored-p-not-variable-if-stored
     (implies (and (variables-well-stored-p h1 g variables)
		   (assoc (car (nth h1 g)) variables))
	      (not (equal (cddr (assoc (car (nth h1 g)) variables))
			  t)))
     :hints (("Goal" :use (:instance variables-well-stored-p-integerp
				     (x (car (nth h1 g))))))))


;; Needed for {\tt Subgoal *1/2.1}

  (local
   (defthm variables-well-stored-p-property-element-init-term-dag-p-update-nth
     (implies (and (variables-well-stored-p h1 g variables)
		   (natp h1)
		   (assoc (car (nth h1 g)) variables))
	      (property-element-init-term-dag-p
	       h1 (cdr (assoc (car (nth h1 g)) variables))
	       (update-nth h1
			   (cdr (assoc (car (nth h1 g)) variables))
			   g)))
     :hints (("Goal" :in-theory (enable property-element-init-term-dag-p)))))

  (local
   (defthm property-element-init-term-dag-p-update-nth
     (implies (and (natp h0) (natp h2) (< h0 h2)
		   (property-element-init-term-dag-p h0 (nth h0 g)
						     g))
	      (property-element-init-term-dag-p h0 (nth h0 g)
						(update-nth h2 x g)))
     :hints (("Goal" :in-theory (enable property-element-init-term-dag-p)))))


  (local
   (defthm init-term-dag-p-aux-list-from-to-update-nth
     (implies (and (natp h0) (natp h1) (natp h2) (<= h0 h1) (<= h1 h2)
		   (init-term-dag-p-aux (list-from-to h0 h1) g))
	      (init-term-dag-p-aux (list-from-to h0 h1) (update-nth h2 x g)))))



  (local
   (defthm init-term-dag-p-aux-update-nth-one-index-beyond-almost
     (implies (and (variables-well-stored-p h1 g variables)
		   (natp h1) (natp h0) (<= h0 h1)
		   (init-term-dag-p-aux (list-from-to h0 h1) g)
		   (equal (cdr (nth h1 g)) t)
		   (assoc (car (nth h1 g)) variables))
	      (init-term-dag-p-aux (append (list-from-to h0 h1)
					   (list-from-to h1 (1+ h1)))
				   (update-nth h1
					       (cdr (assoc (car (nth h1 g)) variables))
					       g)))
     :hints (("Goal" :in-theory (disable  append-list-from-to)))))



  (local
   (defthm init-term-dag-p-aux-update-nth-one-index-beyond
     (implies (and (variables-well-stored-p h1 g variables)
		   (natp h1) (natp h0) (<= h0 h1)
		   (init-term-dag-p-aux (list-from-to h0 h1) g)
		   (equal (cdr (nth h1 g)) t)
		   (assoc (car (nth h1 g)) variables))
	      (init-term-dag-p-aux (list-from-to h0 (+ 1 h1))
				   (update-nth h1
					       (cdr (assoc (car (nth h1 g)) variables))
					       g)))
     :hints (("Goal" :use init-term-dag-p-aux-update-nth-one-index-beyond-almost
	      :in-theory (disable list-from-to)))))


;; And finally the main lemma:

  (defthm init-term-dag-p-make-shared-variables-main-lemma
    (implies (and (natp h1) (natp h2) (natp h0)
		  (<= h0 h1) (<= h1 h2)
		  (tree-p-aux (list-from-to h1 h2) g)
		  (init-term-dag-p-aux (list-from-to h0 h1) g)
		  (variables-well-stored-p h1 g variables))
	     (init-term-dag-p-aux
	      (list-from-to h0 h2)
	      (first (make-shared-variables h1 h2 g variables))))
    :hints (("Goal" :induct (make-shared-variables h1 h2 g variables))))


;; We now prove the theorem {\tt init-term-dag-p-make-shared-variables}
;; presented above, simply noting that when {\tt tree-p} is verified by
;; a graph, then it verifies {\tt tree-p-aux} for every range of natural
;; numbers:


  (local (in-theory (disable property-element-tree-p)))

  (local
   (defthm property-element-tree-p-natp-all-indices
     (implies (and (tree-p g)
		   (local-nat-listp hs))
	      (tree-p-aux hs g))))


  (local
   (defthm nth-aux-make-shared-variables-beyond-the-limit
     (implies (and (natp h1) (natp h2) (natp h3) (<= h2 h3))
	      (equal (nth h3 (first (make-shared-variables h1 h2 g
							   variables)))
		     (nth h3 g)))))



  (local
   (defthm tree-p-aux-make-shared-variables-beyond-the-limit
     (implies (and (natp h1) (natp h2) (natp h3)
		   (<= h2 h3) (natp h4)
		   (tree-p-aux (list-from-to h3 h4) g))
	      (tree-p-aux (list-from-to h3 h4)
			  (first (make-shared-variables h1 h2 g variables))))))


  (local
   (defthm init-term-dag-p-make-shared-variables-bridge-lemma
     (implies (and (natp h1) (natp h2) (<= h1 h2)
		   (tree-p g) (variables-well-stored-p h1 g variables))
	      (init-term-dag-p-aux
	       (append (list-from-to 0 h2)
		       (list-from-to h2
				     (len
				      (first
				       (make-shared-variables h1 h2 g variables)))))
	       (first
		(make-shared-variables h1 h2 g variables))))
     :rule-classes nil))


  (local
   (defthm len-update-nth-corollary
     (implies
      (and (natp h1) (natp h2) (< h1 h2)
	   (< h1 h2) (<= h2 (len g)))
      (not (< (len (update-nth h1 x g)) h2)))))


  (local
   (defthm len-make-shared-variables-auxiliar-property
     (implies (and (natp h1) (natp h2) (<= h1 h2) (<= h2 (len g)))
	      (<= h2 (len (first (make-shared-variables h1 h2 g
							variables)))))
     :rule-classes :linear))


;; Finally, the intended property:

  (defthm init-term-dag-p-make-shared-variables
    (implies (and (natp h1) (natp h2) (<= h1 h2) (<= h2 (len g))
		  (tree-p g) (variables-well-stored-p h1 g variables))
	     (init-term-dag-p
	      (first (make-shared-variables h1 h2 g variables))))
    :hints (("Goal" :use
	     init-term-dag-p-make-shared-variables-bridge-lemma
	     :in-theory (enable tree-p init-term-dag-p))))))

;;; Note that when @h1@ is @0@, then the condition {\tt
;;; (variables-well-stored-p 0 g nil)} trivially holds, so the above
;;; theorem trivially implies that whenever {\tt (tree-p g)} then the
;;; graph {\tt (first (make-shared-variables 0 (len g) g nil))} verifies
;;; the {\tt init-term-dag-p} property.

;;; ============================================================================
;;;
;;; 7) How making shared variables affects to the graph
;;;
;;; ============================================================================


;;; In this section we prove that the variables of the graph obtained
;;; after making the variables of a graph to be shared are
;;; not duplicated.  That is, our goal in this sectionis:

;  (defthm no-duplicatesp-make-shared-variables-particular-case
;    (no-duplicatesp
;     (list-of-term-dag-variables
;      (first
;       (make-shared-variables 0 (len g) g nil))))

;;; And also we show that making variables to be shared preserves the
;;; stored first--order terms. That is, the following theorem:

;  (defthm dag-as-term-make-shared-variables
;    (implies (and
;	      (natp h1) (natp h2) (<= h1 h2)
;	      (dag-p g)
;	      (variables-well-stored-p h1 g variables)
;	      (dag-p (first (make-shared-variables h1 h2 g variables))))
;	     (equal (dag-as-term
;		     flg h (first (make-shared-variables h1 h2 g
;							 variables)))
; 		    (dag-as-term flg h g))))


;;; The main lemma needed in this section is the lemma {\tt
;;; make-shared-variables-variables-main-lemma} below establishing the
;;; relation between the variables bound by the association list
;;; computed by {\tt make-shared-variables}, and the variables appearing
;;; in the graph computed by {\tt make-shared-variables}:

(local
 (encapsulate
  ()

  (defun nths-from-to (l h1 h2)
    (declare (xargs :measure (nfix (- h2 h1))))
    (if (zp (- h2 h1))
	nil
      (cons (nth h1 l)
	    (nths-from-to l (1+ h1) h2))))


  (defun my-subseq-list (l h1 h2)
    (declare (xargs :measure (list* (cons 1 (1+ (nfix (- h2 h1)))) (nfix h1))))
    (cond ((zp (- h2 h1)) nil)
	  ((zp h1) (cons (car l) (my-subseq-list (cdr l) h1 (- h2 1))))
	  (t (my-subseq-list (cdr l) (- h1 1) (- h2 1)))))


  (local
   (defthm update-nth-nths-from-to
     (implies (and (natp h) (natp h1) (natp h2) (< h h1))
	      (equal (nths-from-to (update-nth h x g) h1 h2)
		     (nths-from-to g h1 h2)))))

  (defun alist-to-acl2-numberp (a)
    (if (endp a)
	t
      (and (acl2-numberp (cdar a))
	   (alist-to-acl2-numberp (cdr a)))))

  (local
   (defthm alist-to-indices-does-not-provide-dag-variables
     (implies (and (alist-to-acl2-numberp a)
		   (assoc x a))
	      (acl2-numberp (cdr (assoc x a))))
     :rule-classes :type-prescription))

  (defthm make-shared-variables-variables-main-lemma
    (implies (and (natp h1)
		  (natp h2)
		  (alist-to-acl2-numberp variables))
	     (equal
	      (strip-cars
	       (second (make-shared-variables h1 h2 g variables)))
	      (revappend
	       (list-of-term-dag-variables
		(nths-from-to
		 (first (make-shared-variables h1 h2 g variables))
		 h1 h2))
	       (strip-cars variables))))
    :hints (("Goal" :induct (make-shared-variables h1 h2 g variables))))))


;;; As a particular case of this main lemma, the lemma {\tt
;;; make-shared-variables-variables} below establish the relation
;;; between the variables bound by the association list and the
;;; variables of the graph after making variables to be shared in {\em all}
;;; the graph.

(local
 (encapsulate
  ()
  (local
   (defthm equal-nths-from-to-my-subseq-list-lemma
     (implies (and (natp h1) (natp h2) (< h1 h2))
	      (equal (my-subseq-list l h1 h2)
		     (cons (nth h1 l)
			   (my-subseq-list l (+ 1 h1) h2))))))

  (local
   (defthm equal-nths-from-to-my-subseq-list
     (implies (and (natp h1) (natp h2))
	      (equal  (nths-from-to l h1 h2)
		      (my-subseq-list l h1 h2)))))

  (local
   (defthm my-subseq-list-particular-case
     (equal (my-subseq-list l 0 (len l))
	    (fix-true-list l))
     :rule-classes nil))

  (local
   (defthm nths-from-to-particular-case
     (equal (nths-from-to l 0 (len l)) (fix-true-list l))))

  (local
   (defthm list-of-term-dag-variables-fix-true-list-l
     (equal (list-of-term-dag-variables (fix-true-list l))
	    (list-of-term-dag-variables l))))

  (local
   (defthm revappend-rev-list
     (equal (revappend l ac)
	    (append (revlist l) ac))))

  (local
   (defthm len-update-nth-corollary-2
     (implies (and (natp h) (< h (len g)))
	      (equal (len (update-nth h x g)) (len g)))))

  (local
   (defthm len-make-shared-variables-arithmetic-lemma
     (implies (and (not (zp (- h2 h1)))
		   (natp h1) (natp h2)
		   (<= h1 h2)
		   (<= h2 x))
	      (< h1 x))
     :rule-classes nil))

  (local
   (defthm len-make-shared-variables
     (implies (and (natp h1) (natp h2) (<= h1 h2) (<= h2 (len g)))
	      (equal
	       (len (first (make-shared-variables h1 h2 g variables)))
	       (len g)))
     :hints (("Subgoal *1/4"
	      :use (:instance len-make-shared-variables-arithmetic-lemma
			      (x (len g)))))
     :rule-classes nil))

  (local
   (defthm make-shared-variables-variables
     (equal
      (revlist
       (list-of-term-dag-variables
	(first
	 (make-shared-variables 0 (len g) g nil))))
      (strip-cars
       (second (make-shared-variables 0 (len g) g nil))))

     :hints (("Goal" :use
	      ((:instance len-make-shared-variables
			  (h1 0) (h2 (len g)) (variables nil))
	       (:instance my-subseq-list-particular-case
			  (l (car (make-shared-variables 0 (len g) g nil)))))))))

;; Finally it is to show that the variables bound by the association
;; list are not duplicated, and consequently (using the previous lemmas)
;; we prove (theorem {\tt
;; no-duplicatesp-make-shared-variables-particular-case}) that the list
;; of variables of the graph after making variables to be shared are not
;; duplicated (that is, the main goal in this section):

  (local
   (defthm member-strip-cars-assoc
     (implies (alistp a)
	      (iff (member x (strip-cars a))
		   (assoc x a)))))

  (local
   (defthm no-duplicatesp-make-shared-variables
     (implies (and (alistp variables) (no-duplicatesp (strip-cars variables)))
	      (no-duplicatesp
	       (strip-cars
		(second
		 (make-shared-variables h1 h2 g variables)))))))

  (local
   (defthm no-duplicatesp-make-shared-variables-particular-case-lemma
     (no-duplicatesp
      (revlist
       (list-of-term-dag-variables
	(first
	 (make-shared-variables 0 (len g) g nil)))))
     :hints (("Goal"
	      :in-theory
	      (disable equal-nths-from-to-my-subseq-list
		       no-duplicatesp-revlist
		       make-shared-variables-variables-main-lemma)))))


  (defthm no-duplicatesp-make-shared-variables-particular-case
    (no-duplicatesp
     (list-of-term-dag-variables
      (first
       (make-shared-variables 0 (len g) g nil))))
    :hints (("Goal"
	     :use
	     no-duplicatesp-make-shared-variables-particular-case-lemma
	     :in-theory (disable
			 no-duplicatesp-make-shared-variables-particular-case-lemma
			 make-shared-variables-variables))))




;; {\bf We now prove the last piece of our strategy}, before assembling the
;; pieces to prove our main goals in this book.  We show now that the
;; terms computed by the function {\tt dag-as-term} are preserved
;; after making variables to be shared.

  (local
   (defthm variables-are-not-is
     (implies (term-dag-variable-p h g)
	      (not (term-dag-is-p h g)))))

  (local
   (defthm variables-well-stored-p-assoc
     (implies (and (assoc x variables)
		   (variables-well-stored-p h g variables))
	      (equal (car (nth (cdr (assoc x variables)) g))
		     x))))

  (local
   (defthm car-update-nth-in-strictly-positives-indices
     (implies (and (integerp h) (< 0 h))
	      (equal (car (update-nth h x g)) (car g)))))


;; Attention! The proof of the following lemma is very long, but I
;; prefer not to impose condition on @h@, since in that case I have to
;; impose conditions on @g@ and @gms@.


  (local
   (defthm make-shared-variables-dag-as-term-lemma
     (let* ((c1 (nth h g))
	    (gms (first (make-shared-variables h1 h2 g variables)))
	    (c2 (nth h gms)))
       (implies (and
		 (natp h1) (natp h2) (<= h1 h2)
		 (not (equal c1 c2))
		 (variables-well-stored-p h1 g variables)
		 (term-dag-variable-p h g))
		(and (integerp c2)
		     (term-dag-variable-p c2 gms)
		     (equal (term-dag-symbol c2 gms)
			    (term-dag-symbol h g)))))
     :hints (("Goal" :induct (make-shared-variables h1 h2 g variables)))))



  (local
   (defthm make-shared-variables-dag-as-term
     (implies (and
	       (natp h1) (natp h2) (<= h1 h2)
	       (dag-p (first (make-shared-variables h1 h2 g variables)))
	       flg
	       (variables-well-stored-p h1 g variables)
	       (term-dag-variable-p h g))
	      (equal (dag-as-term flg h
				    (first (make-shared-variables h1 h2 g
								  variables)))
		     (car (nth h g))))
     :hints
     (("Goal"
       :cases
       ((equal (nth h g)
	       (nth h (first (make-shared-variables h1 h2 g variables)))))))))


;; And finally one of the intended theorems in this section, showing that {\tt
;; make-shared-variables} preserves the value of {\tt dag-as-term}.

  (defthm dag-as-term-make-shared-variables
    (implies (and
	      (natp h1) (natp h2) (<= h1 h2)
	      (dag-p g)
	      (variables-well-stored-p h1 g variables)
	      (dag-p (first (make-shared-variables h1 h2 g variables))))
	     (equal (dag-as-term
		     flg h (first (make-shared-variables h1 h2 g
							 variables)))
		    (dag-as-term flg h g)))
    :hints (("Goal" :induct (dag-as-term flg h g))))))


;;; ============================================================================
;;;
;;; 9) Assembling all the pieces
;;;
;;; ============================================================================

;;; Recall that our goal is to prove the main properties of the graph
;;; computed by {\tt term-as-dag}, those properties that allows us to
;;; apply our unification algorithm acting on term dags to that
;;; graph. That is, under certain initial conditions, the following
;;; properties hold:

;;; *)
;;;   The graph is a well--formed directed acyclic graph
;;; *)
;;;   The graph has no duplicates variables
;;; *)
;;;   The term stored in the graph (at index 0) is the input term
;;; -)

;;; This is the initial conditions we will assume about the graph {\em
;;; before} storing the graph. We simply assume that all the nodes are empty:

(defun empty-graph-p (g)
  (declare (xargs :guard t))
  (if (atom g)
;      (equal g nil)
      t
      (and (not (car g))
	   (empty-graph-p (cdr g)))))

;;;----------------------------------------------------------------------------
;;;
;;; 9.2) Properties
;;;
;;;----------------------------------------------------------------------------

(local
 (defthm empty-graph-p-main-property
   (implies (and (not (equal x nil))
		 (member x g))
	    (not (empty-graph-p g)))))

(local
 (defthm empty-graph-p-nth-main-property
   (implies (not (equal (nth h g) nil))
	    (not (empty-graph-p g)))))

(defthm empty-graph-p-bounded-term-graph-p
  (implies (empty-graph-p g)
	   (bounded-term-graph-p g n)))

(defthm empty-graph-p-resize-list
  (implies (empty-graph-p g)
	   (empty-graph-p (resize-list g size nil))))

;;; In particular, the intended result:

(defthm empty-graph-p-implies-term-graph-p
  (implies (empty-graph-p g)
	   (term-graph-p g))
  :rule-classes nil)

;;; This condition trivially implies {\tt tree-p}:

(local
 (defthm empty-graph-p-property-element-tree-p
   (implies (and (empty-graph-p g)
		 (or (member node g)
		     (equal node nil)))
	    (property-element-tree-p h node))))

(local
 (defthm empty-graph-p-property-element-tree-p-nth
   (implies (empty-graph-p g)
	    (property-element-tree-p h (nth h g)))
   :hints (("Goal" :use (:instance empty-graph-p-property-element-tree-p
				   (node (nth h g)))))))

(defthm member-nth-property
  (implies (not (equal (nth h g) nil))
	   (member (nth h g) g)))

(local
 (defthm empty-graph-p-tree-p-aux
   (implies (empty-graph-p g)
	    (tree-p-aux hs g))
   :hints (("Goal" :in-theory (disable property-element-tree-p)))))

(local
 (defthm empty-graph-p-tree-p
   (implies (empty-graph-p g)
	    (tree-p g))
   :hints (("Goal" :in-theory (enable tree-p)))))

;;; The graph obtained by {\tt term-as-dag} verifies {\tt
;;; init-term-dag-p}:

(local
 (defthm term-as-dag-init-term-dag-p
   (implies (and (tree-p g) (term-p term))
	    (init-term-dag-p (term-as-dag term g)))))

;;; The graph obtained by {\tt term-as-dag} is a directed acyclic graph

(defthm term-as-dag-dag-p
  (implies (and (empty-graph-p g) (term-p term))
	   (dag-p (term-as-dag term g))))

;;; The graph obtained by {\tt term-as-dag} stores the input term (at
;;; index 0):

(defthm term-as-dag-stores-term
  (implies (and (empty-graph-p g) (term-p term))
	   (equal (dag-as-term t 0 (term-as-dag term g))
		  term)))

;;; And the following sequence of events shows that the list of
;;; variables of the graph obtained by {\tt term-as-dag} has no
;;; duplicates (theorem {\tt term-as-dag-no-duplicatesp-variables}
;;; below):

(encapsulate
 ()

 (local
  (defun empty-graph-p-aux (hs g)
    (declare (xargs :guard (and (nat-true-listp hs) (true-listp g))))
    (if (endp hs)
	t
	(and (equal (nth (car hs) g) nil)
	     (empty-graph-p-aux (cdr hs) g)))))

 (local
  (defthm empty-graph-p-empty-graph-p-aux
    (implies (empty-graph-p g)
	     (empty-graph-p-aux hs g))))

 (local
  (defthm make-shared-variables-empty-graph-p-aux-1
    (implies (and (natp h2) (natp h3)
		  (<= h2 h3)
		  (empty-graph-p-aux (list-from-to h2 h3) g))
	     (equal (first (make-shared-variables h2 h3 g variables))
		    g))))

 (local
  (defthm make-shared-variables-empty-graph-p-aux-2
    (implies (and (natp h1) (natp h2) (natp h3) (natp h4)
		  (<= h1 h2) (<= h2 h3) (<= h3 h4)
		  (empty-graph-p-aux (list-from-to h3 h4) g))
	     (empty-graph-p-aux
	      (list-from-to h3 h4)
	      (first (make-shared-variables h1 h2 g variables))))))

 (local
  (defthm make-shared-variables-empty-graph-p-aux-final-segment
    (implies (and (natp h1) (natp h2) (natp h3)
		  (<= h1 h2) (<= h2 h3)
		  (empty-graph-p-aux (list-from-to h2 h3) g))
	     (equal (first (make-shared-variables h1 h3 g variables))
		    (first (make-shared-variables h1 h2 g variables))))
    :hints (("Goal" :use make-shared-composition))))

 (local
  (defthm empty-graph-p-aux-term-as-dag-final-segment
    (implies (and (empty-graph-p-aux hs g)
		  (natp h)
		  (subsetp hs
			   (list-from-to
			    (cadr (term-as-dag-aux-ns flg term g h))
			    (len (car (term-as-dag-aux-ns flg term g h))))))
	     (empty-graph-p-aux
	      hs (car (term-as-dag-aux-ns flg term g h))))
    :hints (("Goal" :induct (empty-graph-p-aux hs g)))))

 (defthm term-as-dag-no-duplicatesp-variables
   (implies (and (empty-graph-p g) (term-p term))
	    (no-duplicatesp
	     (list-of-term-dag-variables (term-as-dag term g))))
   :hints (("Goal" :use
	    (:instance make-shared-variables-empty-graph-p-aux-final-segment
		       (h1 0) (h2 (second (term-as-dag-aux-ns t term g 0)))
		       (h3 (len (first (term-as-dag-aux-ns t term g 0))))
		       (g (first (term-as-dag-aux-ns t term g 0)))
		       (variables nil))
	    :in-theory
	    (disable make-shared-variables-empty-graph-p-aux-final-segment))))

 )

(local (in-theory (disable tree-p term-as-dag-aux-in-two-steps)))

;;; ============================================================================
;;;
;;; 10) The {\tt term-graph-p} property of {\tt term-as-dag-aux}
;;;
;;; ============================================================================


;;; We have left (intentionally) one property about {\tt
;;; term-as-dag}. We show in this section that the graph obtained by
;;; {\tt term-as-dag } acting on an empty graph is a well formed term
;;; graph.

;;; Unlike, the above properties, we will reason directly with the
;;; definition of {\tt term-as-dag-aux}. First, we prove that the
;;; property {\tt term-graph-p} is preserved by {\tt
;;; term-as-dag-aux}. And second, we show that {\tt empty-graph-p}
;;; implies {\tt term-graph-p}.

;;; -----------------------------------
;;;
;;; 10.1) The property {\tt term-graph-p} is preserved by {\tt term-as-dag-aux}
;;;
;;; -----------------------------------


;;; The following propeerties show how some updates to graph does not
;;; change the {\tt bounded-term-graph-p} property.

(local
 (defthm bounded-term-graph-p-update-nth-args
   (implies (and
	     (bounded-term-graph-p g n)
	     (eqlablep x)
	     (bounded-nat-true-listp l n))
	    (bounded-term-graph-p (update-nth h (cons x l) g) n))))


(local
 (defthm bounded-term-graph-p-update-nth-variable
   (implies (and
	     (bounded-term-graph-p g n)
	     (eqlablep x))
	    (bounded-term-graph-p (update-nth h (cons x t) g) n))))


(local
 (defthm bounded-nat-substitution-p-assoc
   (implies (and
	     (bounded-nat-substitution-p  a n)
	     (assoc x a))
	    (and (integerp (cdr (assoc x a)))
		 (< (cdr (assoc x a)) n)
		 (<= 0 (cdr (assoc x a)))))))



(local
 (defthm bounded-term-graph-p-update-nth-integer
   (implies (and
	     (bounded-term-graph-p g n)
	     (natp x) (< x n))
	    (bounded-term-graph-p (update-nth h x g) n))))


;;; The main result of this subsection. Note that we prove an
;;; invariant of {\tt term-as-dag-aux}:


(defthm term-as-dag-aux-term-graph-p
  (let* ((res (term-as-dag-aux flg term g h variables))
	 (g-res (first res))
	 (h-res (second res))
	 (hs-res (third res))
	 (var-res (fourth res)))
    (implies (and (term-graph-p g)
		  (natp h)
		  (<= (+ h (length-term flg term)) (len g))
		  (bounded-nat-substitution-p variables (len g))
		  (term-p-aux flg term))
	     (and (term-graph-p g-res)
		  (equal h-res (+ h (length-term flg term)))
		  (equal (len g-res) (len g))
		  (bounded-nat-true-listp hs-res (len g))
		  (bounded-nat-substitution-p var-res (len g))))))

;;; And the intended result of this subsection, a particular case of the
;;; above theorem:

(defthm term-as-dag-term-graph-p
  (implies (and (term-graph-p g)
		(term-p term)
		(<= (length-term t term) (len g)))
	   (term-graph-p (term-as-dag term g))))


(in-theory (disable term-as-dag))

;;; ============================================================================
;;;
;;; 11) Building unification problems
;;;
;;; ============================================================================

;;; The function {\tt terms-as-dag-l} will be our main auxiliary
;;; function for building (dag) unification problems. Recall that a
;;; unification problem (see {\tt dags.lisp}) is determined by an
;;; indices system, an indices substitution and a well--formed directed
;;; acyclic graph. Initially, the indices substitution is empty. We now
;;; describe how we build the graph and the indices system for a
;;; unification problem of the form $\{t_1=t_2\}$:

;;; This function computes the graph. Note that the list that represents
;;; the graph is previously resized after computing how many nodes are
;;; needed. Also note that the term {\tt (equ t1 t2)} is stored in the
;;; graph using {\tt term-as-dag}:

(defun unif-two-terms-problem (t1 t2 g)
  (let* ((size (+ (length-term t t1) (length-term t t2) 1))
	 (g (resize-list g size nil)))
    (term-as-dag (list 'equ t1 t2) g)))

;;; The initial indices system is taken from the argument list of the
;;; first node:

(defun initial-to-be-solved (g)
  (let ((args-0 (cdr (dagi-l 0 g))))
    (list (cons (first args-0)
		(second args-0)))))

;;; Following the results proved in the book {\tt
;;; dag-unification-rules}, our goal is to prove the following:

; If (empty-graph-p g)
; let* g-t1-t2     =  (unif-two-terms-problem t1 t2 g)
;      S-dag-t1-t2 = (initial-to-be-solved g-t1-t2)
; then:
;    (well-formed-dag-system S-dag-t1-t2 g-t1-t2)
;      and
;    (equal (tbs-as-system S-dag-t1-t2 g-t1-t2)
;           (list (cons t1 t2)))


;;; If we prove the above property, we will able to use the theorems
;;; proved in {\tt dag-unification-rules} to conclude the properties of
;;; a unification algorithm that applies the rules of transformation
;;; starting with the above initial unification problem.

;;; Resize list and {\tt length}

(local
 (defthm len-resize-list
   (implies (natp n)
	    (equal (len (resize-list l n x)) n))))

(local (in-theory (disable resize-list)))


;;; The following sequence of events show that the initial unification
;;; problem built by the function {\tt unif-two-terms-problem} and
;;; {\tt initial-to-be-solved} is a well--formed directed acyclic
;;; graph.


;;; Luego lo meto dentro

(defthm bounded-term-graph-p-particular-case
  (implies (and (consp g) (term-graph-p g))
	   (and (< (cadar g) (len g))
		(< (caddar g) (len g)))))

(defthm consp-term-as-dag
  (implies (consp g)
	   (consp (term-as-dag term g )))
  :hints (("Goal" :in-theory (enable term-as-dag))))



(defthm consp-resize-list
  (implies (and (natp n) (< 0 n))
	   (consp (resize-list l n x)))
  :hints (("Goal" :in-theory (enable resize-list))
	  ("Subgoal *1/2''" :expand (RESIZE-LIST L 1 X))))



(encapsulate

 ()

 (local
  (defthm equal-nth-car
	 (equal (nth 0 g) (car g))))

 (local
  (defthm len-args-term-as-dag-aux
    (equal (len (third (term-as-dag-aux nil args g h variables)))
	   (len args))))

 (local
  (defthm term-as-dag-aux-first-element-len
    (equal
     (len
      (cdr
       (car
	(first
	 (term-as-dag-aux t (cons symb args) g 0 nil)))))
     (len args))))

 (local
  (defthm term-as-dag-first-element
    (equal
     (len
      (cdr
       (car
	(term-as-dag (list 'equ t1 t2) g))))
     2)
    :hints (("Goal" :in-theory (enable term-as-dag)))))

;;; Este me hace falta despues
  (defthm term-as-dag-first-element-nth
    (equal
     (len
      (cdr
       (nth 0
	(term-as-dag (list 'equ t1 t2) g))))
     2)
    :hints (("Goal" :in-theory (enable term-as-dag))))

 (local
  (defthm nat-true-listp-len-two-first
    (implies (and (nat-true-listp l)
		  (equal (len l) 2))
	     (and (integerp (first l))
		  (<= 0 (first l))))))

 (local
  (defthm nat-true-listp-len-two-second
    (implies (and (nat-true-listp l)
		  (equal (len l) 2))
	     (and (integerp (second l))
		  (<= 0 (second l))))))
  (local
   (defthm term-graph-p-first-element-nat-true-listp
     (implies (and (equal (len (cdr (car g))) 2)
		   (term-graph-p g))
	      (nat-true-listp (cdr (car g))))))

  (defthm unif-two-terms-problem-well-formed-dag-system
    (let* ((g-t1-t2 (unif-two-terms-problem t1 t2 g))
	   (S-dag-t1-t2 (initial-to-be-solved g-t1-t2)))
      (implies (and (empty-graph-p g) (term-p t1) (term-p t2))
	       (well-formed-dag-system S-dag-t1-t2 g-t1-t2)))
    :hints (("Goal"
	     :use
	     (:instance term-as-dag-term-graph-p
			(g (resize-list g (+ (length-term t t1) (length-term t t2)
					     1) nil))
			(term (list 'equ t1 t2))))
	    ("Subgoal 1" :in-theory (enable
				     well-formed-upl)))))



;;; And finally, the following sequence of events show that the initial
;;; unification problem built by the function {\tt
;;; unif-two-terms-problem} and {\tt initial-to-be-solved} stores
;;; (in a dag form) the initial unification problem:


(encapsulate
 ()

 (local

  (defthm unif-two-terms-problem-stores-the-problem-lemma-1
    (implies (and
	      (equal (len (cdr (nth h g))) 2)
	      (equal (dag-as-term t h g)
		     (list 'equ t1 t2)))
	     (equal (dag-as-term t (first (cdr (nth h g))) g)
		    t1))
    :hints (("Subgoal 1'" :expand (dag-as-term nil (cdr (nth h g)) g)))))



 (local
  (defthm unif-two-terms-problem-stores-the-problem-lemma-2
    (implies (and
	      (equal (len (cdr (nth h g))) 2)
	      (equal (dag-as-term t h g)
		     (list 'equ t1 t2)))
	     (equal (dag-as-term t (second (cdr (nth h g))) g)
		    t2))
    :hints (("Goal'''" :expand (dag-as-term nil (cdr (nth h g)) g))
	    ("Goal'5'" :expand (dag-as-term nil (cddr (nth h g)) g)))))

 (local
  (defthm unif-two-terms-problem-stores-the-problem-almost
    (let* ((g-t1-t2 (unif-two-terms-problem t1 t2 g))
	   (S-dag-t1-t2 (initial-to-be-solved g-t1-t2)))
      (implies (and (empty-graph-p g) (term-p t1) (term-p t2)
		    (equal (dag-as-term t 0 g-t1-t2)
			   (list 'equ t1 t2)))
	       (equal (tbs-as-system S-dag-t1-t2 g-t1-t2)
		      (list (cons t1 t2)))))
    :hints (("Goal" :in-theory
	     (disable nth term-as-dag-stores-term)))
    :rule-classes nil))


 (defthm unif-two-terms-problem-stores-the-problem
   (let* ((g-t1-t2 (unif-two-terms-problem t1 t2 g))
	  (S-dag-t1-t2 (initial-to-be-solved g-t1-t2)))
     (implies (and (empty-graph-p g) (term-p t1) (term-p t2))
	      (equal (tbs-as-system S-dag-t1-t2 g-t1-t2)
		     (list (cons t1 t2)))))
   :hints (("Goal" :use unif-two-terms-problem-stores-the-problem-almost))))




;;; ===============================================================
