;;; ============================================================================
;;; dags.lisp
;;; Ti'tulo: Term dags in ACL2
;;; ============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "dags")

|#

(in-package "ACL2")


(include-book "basic")
(include-book "../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

;;; ============================================================================
;;;
;;; 0) Introduccio'n
;;;
;;; ============================================================================

;;; We discuss a representation for term graphs, using
;;; lists and we define the notion of directed acyclic graphs, proving
;;; its main properties. We also describe and prove a way of recursively
;;; traversing term dags.

;;; More precisely, in this book:

;;; *)
;;;   We define a representation for term graphs, {\em using lists}.
;;; *)
;;;   We define a predicate {\tt dag-p}, the property of being acyclic (a dag).
;;; *)
;;;   We prove the main properties of that definition.
;;; *)
;;;   We define a measure function that will be used to admit functions
;;;   that traverse dags in a way that resembles recursion on
;;;   first order terms represented as lists in preffix notation.
;;; *)
;;;   We prove the corresponding termination conjectures.
;;; -)

;;; The results in this book will be translated to an analogue
;;; representation of term-dags using stobjs, that will be used to
;;; compute. I feel more comfortable working with lists than working
;;; with stobjs (which requires more technical details), so I prefer to
;;; stay in the "logical side" and translate the main events later.

;;; ============================================================================
;;;
;;; 1) Representation of term graphs
;;;
;;; ============================================================================

;;; We represent a (directed) term graph as a list. If @g@ is a list
;;; representing a term graph, {\tt (nth x g)} stores a symbol (function or
;;; variable) and information about the neighbors of the node @x@.

;;; There are two kinds of nodes: function nodes and variable nodes.
;;; Depending on the kind of a node @h@, we will store in {\tt (nth h g)} the
;;; following information:

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

;;;   A graph will be represented as a list @G@ with the sequence of that
;;; information. See {\tt dag-unification.lisp} for some examples. This means
;;; that the neighbors of node @N@ and eventually its variable or function
;;; symbol is in {\tt (nth N G)}. We will say that a node of a graph @G@ is
;;; {\em important} if it is a natural number less than the length of the
;;; list @G@.

;;; The following function computes the neighbors of a node @h@ in a graph @G@:

(defun neighbors (h g)
  (let ((ng (nth h g)))
    (if (integerp ng)
	(list ng)
      (let ((ngs (cdr ng)))
	(if (equal ngs t) nil ngs)))))

;;; REMARK: As usual, every ACL2 object can be seen as a term
;;; graph. Moreover, since neighbors are determined by the behaviour of
;;; the function @nth@, every ACL2 has a list of neighbors (possibly
;;; empty) w.r.t. to a term graph. In particular, non-natural nodes has
;;; the same list of neighbors than the node @0@. Natural nodes geater
;;; than the length of @g@ have an empty list of neighbors (they can be
;;; seen as the constant @(nil)@).


;;; ============================================================================
;;;
;;; 2) Directed acyclic (term) graphs
;;;
;;; ============================================================================

;;; We now define a predicate checking that a given term graph has no
;;; cyclic paths. A term graph with this property is called a dag
;;; (directed acyclic graph).



;;; -----------------------------------------------
;;;
;;; 2.1) Definition of {\tt dag-p-aux} (and termination)
;;;
;;; -----------------------------------------------

;;; Firstly, we are going to define the following function to check if
;;; there exists a cycle in a term graph @g@, considering all the paths
;;; starting with a node in a list of nodes @h@ \cite{moore-graph}.

;;; The following function and its verification is inspired in "An
;;; exercise in graph theory", J Moore \cite{moore-graph}.

; (defun dag-p-aux (hs rev-path g)
;   (declare (xargs :measure (measure-dag-p hs rev-path g)))
;   (if (endp hs)
;       t
;     (let ((hs-car (nfix (car hs))))
;       (if (member hs-car rev-path)
; 	  nil
; 	(and (dag-p-aux (neighbors (car hs) g)
; 			(cons hs-car rev-path)
; 			g)
; 	     (dag-p-aux (cdr hs) rev-path g))))))

;;; REMARKS:

;;; 1)
;;;   In this definition, @g@ is a term graph, @hs@ is a stack of nodes that
;;;   remains to be explored and @rev-path@ contains a path (in reverse
;;;   order) with nodes already visited. This recursive schema is inspired
;;;   in the one given in J Moore's paper.
;;;
;;; 2)
;;;   We need to define a measure for the admission of the
;;;   function. The measure will also be used in some of the functions we
;;;   will define later.

;;; 3)
;;;   Note that cycle detection is done "modulo nfix". Non natural nodes
;;;   are transformed to 0.
;;; -)

;;; Now our goal is to define a measure {\tt measure-dag-p}, and show
;;; the following termination conjectures, which will allow the
;;; admission of the above function:

; (AND (E0-ORDINALP (MEASURE-DAG-P HS REV-PATH G))
;      (IMPLIES (AND (NOT (ENDP HS))
;                    (NOT (MEMBER (NFIX (CAR HS)) REV-PATH)))
;               (E0-ORD-< (MEASURE-DAG-P (NEIGHBORS (CAR HS) G)
;                                        (CONS (NFIX (CAR HS)) REV-PATH)
;                                        G)
;                         (MEASURE-DAG-P HS REV-PATH G)))
;      (IMPLIES (AND (NOT (ENDP HS))
;                    (NOT (MEMBER (NFIX (CAR HS)) REV-PATH))
;                    (DAG-P-AUX (NEIGHBORS (CAR HS) G)
;                               (CONS (NFIX (CAR HS)) REV-PATH)
;                               G))
;               (E0-ORD-< (MEASURE-DAG-P (CDR HS) REV-PATH G)
;                         (MEASURE-DAG-P HS REV-PATH G)))).

;;; This measure will be a lexicographic combination of:

;;; *)
;;;   The number of important nodes that are not in rev-path .
;;; *)
;;;   The length of @hs@.
;;; -)

;;; But previously, some auxiliary definitions and lemmas:

(defthm nfix-natp
  (natp (nfix x)))

(defthm nfix-neighbors
  (equal (neighbors (nfix x) g)
	 (neighbors x g)))


(defthm nfix-nth
  (equal (nth (nfix x) l)
	 (nth x l)))


(defun map-nfix (l)
  (if (endp l)
      l
    (cons (nfix (car l)) (map-nfix (cdr l)))))

(defthm map-nfix-member
  (implies (member x l)
	   (member (nfix x) (map-nfix l))))

(defun bounded-natp (x n)
  (and (natp x) (< x n)))

(defun count-bounded-natp-not-in (n l)
  (cond ((zp n) 0)
	((member (1- n) l) (count-bounded-natp-not-in (1- n) l))
	(t (1+ (count-bounded-natp-not-in (1- n) l)))))

;;; The measure:

(defun measure-dag-p (hs rp g)
  (cons (+ 1 (count-bounded-natp-not-in (len g) rp))
        (len hs)))



;;; The measure conjectures:

(defthm measure-dag-p-e0-ordinalp
  (e0-ordinalp (measure-dag-p hs rp g)))

(encapsulate
 ()

;; \begin{skip-for-latex-version}

 (local
  (defthm count-bounded-natp-not-in-cons-1
    (>= (count-bounded-natp-not-in n l)
	(count-bounded-natp-not-in n (cons m l)))
    :rule-classes :linear))

 (local
  (defthm count-bounded-natp-not-in-cons-2
    (implies (natp n)
	     (iff (equal (count-bounded-natp-not-in n (cons x m))
			 (count-bounded-natp-not-in n m))
		  (or (member x m) (not (bounded-natp x n)))))))

 (defthm natp-len
   (natp (len l)))

 (defthm positive-len
   (equal (< 0 (len l))
	  (consp l)))

 (defthm nth-non-nil
   (implies (and (<= (len l) n) (natp n))
	    (not (nth n l))))

;; \end{skip-for-latex-version}

 (defthm measure-dag-p-recursion-1
   (implies (and (consp hs)
		 (not (member (nfix (car hs)) rev-path)))
	    (e0-ord-< (measure-dag-p (neighbors (car hs) g)
					  (cons (nfix (car hs)) rev-path)
					  g)
		      (measure-dag-p hs rev-path g))))

 (defthm measure-dag-p-recursion-2
   (implies (consp hs)
	    (e0-ord-< (measure-dag-p (cdr hs) rev-path g)
		      (measure-dag-p hs rev-path g)))))

;;; We disable the functions:

(in-theory (disable neighbors))
(in-theory (disable measure-dag-p))
(in-theory (disable nfix))

;;; REMARK: Recall these "disables" when including this book.

;;; The function dag-p-aux, with its admission:

(defun dag-p-aux (hs rev-path g)
  (declare (xargs :measure (measure-dag-p hs rev-path g)))
  (if (endp hs)
      t
    (let ((hs-car (nfix (car hs))))
      (if (member hs-car rev-path)
 	  nil
 	(and (dag-p-aux (neighbors (car hs) g)
 			(cons hs-car rev-path)
 			g)
 	     (dag-p-aux (cdr hs) rev-path g))))))


;;; -----------------------------
;;;
;;; 2.2)  Definition of dag-p
;;;
;;; -----------------------------

;;; We will say that a directed term graph is acyclic (a dag), if it has
;;; no cycles starting in an important node. We do not have to worry
;;; about the rest of the nodes. If they are natural numbers greater
;;; than the length of the list representing the graph, they are nodes
;;; without neighbors. If they are not natural numbers, the behave as
;;; the node 0.

;;; First we define and characterize the list of natural numbers between
;;; 0 and n:

(defun list-of-n (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (if (zp n)
      nil
    (cons (1- n) (list-of-n (1- n)))))

(defthm bounded-natp-list-of-n
  (implies (natp n)
	   (iff (member x (list-of-n n))
		(bounded-natp x n))))

(in-theory (disable list-of-n))


;;; Finally, the definition {\tt dag-p}:


(defun dag-p (g)
  (dag-p-aux (list-of-n (len g)) nil g))


;;; ============================================================================
;;;
;;; 3) Verification of {\tt dag-p}
;;;
;;; ============================================================================


;;; Our goal is to prove that {\tt (dag-p g)} if and only if {\tt g} is
;;; cycle-free.


;;; -----------------------------------
;;;
;;; 3.1)  Definition of path and cycles
;;;
;;; -----------------------------------

;;; We define that relation between neigbors nodes in a graph:

(defun rel-graph (x y g)
  (member y (map-nfix (neighbors x g))))


;;; The following function defines the notion of path in a term graph:

(defun path-p (p g)
  (cond ((endp p) (equal p nil))
	((endp (cdr p)) (and (natp (car p)) (equal (cdr p) nil)))
	(t (and
	    (natp (first p))
	    (rel-graph (first p) (second p) g)
	    (path-p (cdr p) g)))))

;;; REMARK: Note that this definition of path differs slightly form the
;;; definition of Moore: paths are sequences of natural numbers. We use
;;; {\tt map-nfix} to transform non-natural nodes to node 0.


;;; An interesting property about concatenation of paths (taken from
;;; J's work):

(defthm path-p-append
  (implies (and (true-listp p1)
		(true-listp p2))
	   (iff (path-p (append p1 p2) g)
		(cond ((endp p1) (path-p p2 g))
		      ((endp p2) (path-p p1 g))
		      (t (and (path-p p1 g)
			      (path-p p2 g)
			      (rel-graph (car (last p1)) (car p2) g)))))))

;;; A cycle is a path with no duplicate nodes:

(defun cycle-p (p g)
  (and (path-p p g)
       (not (no-duplicatesp p))))




;;; -----------------------------------
;;;
;;; 3.1)  Soundness of {\tt dag-p}
;;;
;;; -----------------------------------

;;; We want to prove that {\tt (not (dag-p g))} implies the existence of
;;; a cycle. We have to give this cycle explicitly, defined by the below
;;; function {\tt one-cyclic-path}, whose main auxiliary function is the
;;; following:

(defun cyclic-path-aux (hs rev-path g)
  (declare (xargs :measure (measure-dag-p hs rev-path g)))
  (if (endp hs)
      nil
    (let ((hs-car (nfix (car hs))))
      (if (member hs-car rev-path)
	  (revlist (cons hs-car rev-path))
	(or (cyclic-path-aux (neighbors (car hs) g)
			     (cons hs-car rev-path)
			   g)
	    (cyclic-path-aux (cdr hs) rev-path g))))))


(defun one-cyclic-path (g)
  (cyclic-path-aux (list-of-n (len g)) nil g))

;;; The function {\tt cyclic-path-aux} returns a path. Note that this
;;; property states the general invariant of the function:

(defthm cyclic-path-aux-path-p
   (let ((cp (cyclic-path-aux hs rp g)))
     (implies (and (true-listp rp)
		   (path-p (revlist rp) g)
		   (if (consp rp)
		       (subsetp hs (neighbors (car rp) g))
		     t)
		   cp)
	      (path-p cp g))))


;;; The function {\tt cyclic-path-aux} returns a list with duplicate nodes:

;; \begin{skip-for-latex-version}

(defthm cyclic-path-aux-path-p-no-duplicatesp-aux
  (let ((cp (cyclic-path-aux hs rp g)))
    (implies (and (true-listp rp) cp)
	     (member (car (revlist cp)) (cdr (revlist cp))))))

;; \end{skip-for-latex-version}

(encapsulate
 ()

;; \begin{skip-for-latex-version}

 (local
  (defthm member-car-cdr-no-duplicatesp
    (implies (member (car l) (cdr l))
	     (not (no-duplicatesp l)))))

;;; Lists
 (local
  (defthm meber-revlist
    (iff (member x (revlist l))
	 (member x l))))

 (local
  (defthm no-duplicatesp-append-cons
    (equal (no-duplicatesp (append a (cons e b)))
	   (and (not (member e a))
		(not (member e b))
		(no-duplicatesp (append a b))))))

 (local
  (defthm no-duplicatesp-revlist
    (iff (no-duplicatesp x)
	 (no-duplicatesp (revlist x)))
    :rule-classes nil))


;; \end{skip-for-latex-version}

 (defthm cyclic-path-aux-path-p-no-duplicatesp
   (let ((cp (cyclic-path-aux hs rp g)))
     (implies (and (true-listp rp) cp)
	      (not (no-duplicatesp cp))))
   :hints (("Goal" :use (:instance
			 no-duplicatesp-revlist
			 (x (cyclic-path-aux hs rp g)))))))


;;; This is the main lemma for the soundness theorem:

(defthm cyclic-path-iff-not-dag
  (iff (cyclic-path-aux hs rp g)
       (not (dag-p-aux hs rp g))))

;;; Finally, the soundness theorem:
;;; ·······························

(defthm dag-p-soundness
  (implies (not (dag-p g))
	   (cycle-p (one-cyclic-path g) g)))

;;; -----------------------------------
;;;
;;; 3.2)  Completeness of {\tt dag-p}
;;;
;;; -----------------------------------


;;; Let us prove that if @p@ is a cyclic path in @g@, then {\tt (not (dag-p
;;; g))}

;;; This function checks if @p@ is list of nodes {\tt (n1 ... nk)} where @nk@ is
;;; in {\tt (append rp (n1 ... n(k-1)))} and no other @ni@ has this
;;; property. This function is needed to express an invariant property
;;; essential for the completeness theorem of {\tt dag-p}.

(local
 (defun extension-to-cyclic-path (p rp)
   (cond ((endp p) nil)
	 ((endp (cdr p)) (member (car p) rp))
	 (t (and (not (member (car p) rp))
		 (extension-to-cyclic-path (cdr p) (cons (car p) rp)))))))

;;; A function for an induction hint:

(local
 (defun induct-dag-p-aux-completeness (hs rev-path g p)
   (declare (xargs :measure (measure-dag-p hs rev-path g)
		   :hints (("Subgoal 1"  :use measure-dag-p-recursion-1
			    :in-theory (disable measure-dag-p-recursion-1)))))
   (cond ((endp hs) t)
	 ((member (nfix (car hs)) rev-path) t)
	 ((equal (car p) (nfix (car hs)))
	  (induct-dag-p-aux-completeness
	  (neighbors (car hs) g) (cons (car p) rev-path) g (cdr p)))
	 (t (induct-dag-p-aux-completeness (cdr hs) rev-path g p)))))


;;; The main lemma for completeness:
;;; ································

(local
 (defthm dag-p-aux-completeness-main-lemma
   (implies (and (true-listp rp)
		 (extension-to-cyclic-path p rp)
		 (path-p p g)
		 (member (car p) (map-nfix hs)))
	    (not (dag-p-aux hs rp g)))
   :hints (("Goal" :induct (induct-dag-p-aux-completeness hs rp g p)))))



;;; Now the rest of the proof consists of proving that when {\tt
;;; (cycle-p p g)}, we can build a path {\tt p1}, such that:

;;; 1)
;;;  {\tt (path-p p1 g)}
;;; 2)
;;;  {\tt (natp (car p1))} y {\tt (car p1) < (len g)}
;;; 3)
;;;  {\tt (extension-to-cyclic-path p1 nil)}
;;; -)

;;; These three properties will allows us to apply the above theorem to
;;; show that {\tt (not (dag-p g))}. So let's go:


(encapsulate
 ()

;; This function {\tt make-simple-cycle-aux} will be the auxiliary
;; function needed to build such a path @p1@. In particular, given a
;; cycle @p@, the "simple" cicle @p1@ will be given by {\tt
;; (make-simple-cycle-aux p nil)}.

 (local
  (defun make-simple-cycle-aux (to-visit visited)
    (cond ((endp to-visit) nil)
	  ((member (car to-visit) visited) (list (car to-visit)))
	  (t (let ((temp (make-simple-cycle-aux (cdr to-visit)
						(cons (car to-visit)
						      visited))))
	       (if temp (cons (car to-visit) temp) nil))))))

;; The main property of {\tt make-simple-cycle-aux}:

 (local
  (defthm extension-to-cyclic-path-make-simple-cycle-aux
    (implies (make-simple-cycle-aux to-visit visited)
	     (extension-to-cyclic-path (make-simple-cycle-aux to-visit
							      visited)
				       visited))))

;; Starting in a cycle, this function alway suceed:

 (local
  (defthm not-make-simple-cycle-aux-implies-disjointp
    (implies (and (member x l) (member x m))
	     (make-simple-cycle-aux l m))))

 (local
  (defthm not-no-duplicatesp-implies-make-simple-cycle-aux
    (implies (not (no-duplicatesp l))
	     (make-simple-cycle-aux l m))))

;; Starting in ap path, the function obtains a path:

 (local
  (defthm path-p-implies-make-simple-cycle-aux-pathp
    (implies (path-p p g)
	     (path-p (make-simple-cycle-aux p l) g))))

;; \begin{skip-for-latex-version}

 (local
  (defthm path-p-one-element
    (implies (and (consp p)
		  (not (bounded-natp (car p) (len g)))
		  (not (endp (cdr p))))
	     (not (path-p p g)))
    :hints (("Goal" :in-theory (enable nfix neighbors)))))

 (local
  (defthm car-make-simple-cycle-aux
    (implies (make-simple-cycle-aux p l)
	     (equal (car (make-simple-cycle-aux p l)) (car p)))))

 (local
  (defthm member-map-nfix-2
    (implies (and (member x l)
		  (natp x))
	     (member x (map-nfix l)))
    :hints (("Goal" :in-theory (enable nfix)))))


;; \end{skip-for-latex-version}


;; Finally, the completeness theorem:
;;; ··································


 (defthm dag-p-completeness
   (implies (cycle-p p g)
	    (not (dag-p g)))
   :hints (("Goal" :use ((:instance dag-p-aux-completeness-main-lemma
				    (p (make-simple-cycle-aux p nil))
				    (rp nil)
				    (hs (list-of-n (len g))))
			 path-p-one-element)))))



;;; ============================================================================
;;;
;;; 4) A measure function for traversing dags
;;;
;;; ============================================================================

;;; We will need to define functions on dags that traverse the graph in
;;; the same recursive fashion than functions acting on terms
;;; represented using lists. Unlike terms represented as lists, this
;;; functions may not terminate in general, although this is not the
;;; case for dags.


;;; Defining functions on dags using the same recursive schema than the
;;; corresponding function on terms in prefix notation will be essential
;;; for compositional reasoning, allowing us to translate properties
;;; from the prefix case to the dags case.

;;; For example, this will be a typical recursive definition on dags:


; (defun occur-check-l (flg x h g)
;   (declare (xargs :measure (measure-rec-dag flg h g)))
;   (if (dag-p g)
;       (if flg
;   	  (let ((p (term-dagi-l h g)))
; 	    (if (integerp p)
; 		(occur-check-l flg x p g)
; 	      (let ((args (cdr p)))
; 		(if (equal args t)
; 		    (= x h)
; 		  (occur-check-l nil x args g)))))
; 	(if (endp h)
; 	    nil
; 	  (or (occur-check-l t x (car h) g)
; 	      (occur-check-l nil x (cdr h) g))))
;    t))



;;; So we now define a measure called {\tt measure-rec-dag} for
;;; aceppting this type of recursive definitions.

;;; The idea is simple: we define  the number of nodes that can be
;;; reached in a dag starting from the nodes in a given list of
;;; nodes. If we detect a cycle, we return 0. The cycle detection is
;;; done as in the previous functions. This measure is a good choice
;;; except when @flg@ is @nil@ and we recurse on a list of dags. But in
;;; this case, we can compare the {\tt acl2-count} of the list:


(defun dag-nodes-aux (hs rev-path g)
  (declare (xargs :measure (measure-dag-p hs rev-path g)))
  (if (endp hs)
      0
    (let ((hs-car (nfix (car hs))))
      (if (member hs-car  rev-path)
	  0   ;; cycle detected
	(let ((nodes-car (dag-nodes-aux
			  (neighbors (car hs) g)
			  (cons hs-car rev-path)
			  g))
	      (nodes-cdr (dag-nodes-aux (cdr hs) rev-path g)))
	  (+ 1 nodes-car nodes-cdr))))))

(defun dag-nodes (hs g)
  (dag-nodes-aux hs nil g))

;;; That is the measure we want to define (lexicographic combination of
;;; numbers of nodes and the {\tt acl2-count} of @hs@)

(defun measure-rec-dag (flg h g)
  (if (dag-p g)
      (if flg
	  (cons (1+ (dag-nodes (list h) g)) (acl2-count h))
	(cons (1+ (dag-nodes h g)) (acl2-count h)))
    0))



;;; ============================================================================
;;;
;;; 5) Termination conjectures about {\tt measure-rec-dag}
;;;
;;; ============================================================================

;;; Some useful macros to improve readability:

(defmacro term-dag-is-p (x g)
  `(integerp (nth ,x ,g)))

(defmacro term-dag-variable-p (x g)
  `(equal (cdr (nth ,x ,g)) t))

(defmacro term-dag-non-variable-p (x g)
  `(and (not (term-dag-is-p ,x ,g))
        (not (term-dag-variable-p ,x ,g))))

(defmacro term-dag-symbol (x g)
  `(car (nth ,x ,g)))

(defmacro term-dag-args (x g)
  `(cdr (nth ,x ,g)))

;;; So our goal is to prove the following theorems about {\tt measure-rec-dag}:

; (defthm measure-rec-dag-e0-ordinalp
;    (e0-ordinalp (measure-rec-dag flg h g)))

; (defthm dag-recursion-case-1
;    (implies (and (dag-p g)
; 		 (term-dag-non-variable-p h g)
; 		 flg)
; 	    (e0-ord-< (measure-rec-dag nil (term-dag-args h g) g)
; 		      (measure-rec-dag flg h g))))


; (defthm dag-recursion-case-2
;    (implies (and (dag-p g)
; 		 (term-dag-is-p h g)
; 		 flg)
; 	    (e0-ord-< (measure-rec-dag flg (nth h g) g)
; 		      (measure-rec-dag flg h g))))


; (defthm dag-recursion-case-3
;   (implies (and (dag-p g) (consp h))
; 	   (e0-ord-< (measure-rec-dag t (car h) g)
; 		     (measure-rec-dag nil h g))))



; (defthm dag-recursion-case-4
;   (implies (and (dag-p g) (consp h))
; 	   (e0-ord-< (measure-rec-dag nil (cdr h) g)
; 		     (measure-rec-dag nil h g))))


;;; ------------------------------------------
;;;
;;; 5.1)  An important lemma about {\tt dag-p}
;;;
;;; ------------------------------------------


;;; Before we prove the above theorems, let us prove that under the
;;; hypothesis {\tt (dag-p g)}, we have {\tt (dag-p-aux hs nil g)} for
;;; all @hs@. Note that this is not a trivial property, since {\tt
;;; (dag-p g)} only ensures that for a specific list of nodes (the nodes
;;; from 1 to the length of @g@), in a given order, the graph is
;;; cycle-free. But nothing is said about the rest of nodes and about
;;; lists in an arbitrary order. Note also the role of the second
;;; argument, since it is changed  in every recursive call.

;;; The proof strategy will be the following:

;;; 1)
;;;  We will prove that {\tt dag-p-aux} is preserved in subsets.
;;; 2)
;;;  We will prove that {\tt dag-p-aux} is preserved in append.
;;; 3)
;;;  Every @hs@ can be included as a subset of a concatenation containing
;;;  the important nodes (for these nodes we have @dag-p-aux@ by
;;;  hypothesis) plus the natural numbers greater (they don't have
;;;  neighbors and trivially satisfies @dag-p-aux@) plus the non-naturals
;;;  (they behave like 0, which is in one of the previos pieces).
;;; -)

;;; For these two last theorems, @hs@ and @rp@ have to be disjoint.


;;; Append preserved

(defthm dag-p-aux-append
  (implies (and (dag-p-aux hs1 rp g)
		(dag-p-aux hs2 rp g))
	   (dag-p-aux (append hs1 hs2) rp g)))


;;; Subsetp preserved

(encapsulate
 ()

 (local
  (defthm dag-p-aux-member
    (implies (and (dag-p-aux hs rp g)
		  (member x hs))
	     (dag-p-aux (list x) rp g))))

 (local
  (defthm dag-p-aux-subsetp-lemma
    (implies (and (dag-p-aux hs2 rp g)
		  (dag-p-aux hs1 rp g)
		  (member x hs1))
	     (dag-p-aux (cons x hs2) rp g))
    :hints (("Goal" :use (:instance dag-p-aux-append
				    (hs1 (list x)))))))

 (defthm dag-p-aux-subsetp
   (implies (and (dag-p-aux hs2 rp g)
		 (subsetp hs1 hs2))
	    (dag-p-aux hs1 rp g))
   :hints (("Goal" :induct (subsetp hs1 hs2)))))

;;; The special case of empty graphs:

(encapsulate
 ()

 (local
  (defthm neighbors-empty-graph
    (implies (not (consp g))
	     (equal (neighbors h g) nil))
    :hints (("Goal" :in-theory (enable neighbors)))))

 (defthm dag-p-aux-not-consp-graph
   (implies (and (atom g)
		 (disjointp (map-nfix hs) rp))
	    (dag-p-aux hs rp g))))


;;; Non-natural nodes:

(encapsulate
 ()

 (defun list-of-non-natp (l)
   (if (endp l)
       t
     (and (not (natp (car l)))
	  (list-of-non-natp (cdr l)))))

;; \begin{skip-for-latex-version}

 (local (in-theory (enable neighbors nfix)))

 (local
  (defthm neighbors-non-natp
    (implies (not (natp x))
	     (equal (neighbors x g) (neighbors 0 g)))))

 (local
  (defthm dag-p-aux-non-natp-nodes-lemma
    (implies (and (dag-p-aux (list 0) rp g)
		  (list-of-non-natp l))
	     (dag-p-aux l rp g))))

 (local (in-theory (disable neighbors)))

;; \end{skip-for-latex-version}

 (defthm dag-p-aux-non-natp-nodes
   (implies (and (dag-p-aux (list-of-n (len g)) rp g)
		 (list-of-non-natp hs)
		 (disjointp (map-nfix hs) rp))
	    (dag-p-aux hs rp g))
   :hints (("Goal" :cases ((atom g))))))


;;; Natural nodes greater than the length:

(encapsulate
 ()

 (defun list-of-greater-natp (n l)
   (if (endp l)
       t
     (and (natp (car l)) (>= (car l) n)
	  (list-of-greater-natp n (cdr l)))))

;; \begin{skip-for-latex-version}

 (defthm neighbors-greater-natp
   (implies (and (natp n) (>= n (len g)))
	    (equal (neighbors n g) nil))
   :hints (("Goal" :in-theory (enable neighbors))))

;; \end{skip-for-latex-version}

 (defthm dag-p-aux-greater-natp-nodes
   (implies (and (dag-p-aux (list-of-n (len g)) rp g)
		 (list-of-greater-natp (len g) hs)
		 (disjointp (map-nfix hs) rp)) ;;; se puede dejar en hs.
	    (dag-p-aux hs rp g))))

;;; Let's now separate every list into three pieces:

(encapsulate
 ()


 (defun greater-natp-nodes (n hs)
   (cond ((endp hs) nil)
	 ((and (natp (car hs)) (>= (car hs) n))
	  (cons (car hs) (greater-natp-nodes n (cdr hs))))
	 (t (greater-natp-nodes n (cdr hs)))))

 (local
  (defthm list-of-greater-natp-greater-natp-nodes
   (list-of-greater-natp n (greater-natp-nodes n hs))))


 (defun non-natp-nodes (hs)
   (cond ((endp hs) nil)
	 ((not (natp (car hs)))
	  (cons (car hs) (non-natp-nodes  (cdr hs))))
	 (t (non-natp-nodes  (cdr hs)))))

 (local
  (defthm list-of-non-natp-non-natp-nodes
    (list-of-non-natp (non-natp-nodes  hs))))

 (local
  (defthm nodes-subsetp
    (implies (natp n)
	    (subsetp hs (append (list-of-n n)
				(greater-natp-nodes n hs)
				(non-natp-nodes hs))))))

;; And finally we have the desired property:


  (defthm dag-p-main-property
    (implies (dag-p g)
	     (dag-p-aux hs nil g))

    :hints (("Goal"
	     :in-theory (disable dag-p-aux-subsetp)
	     :use (:instance dag-p-aux-subsetp
			   (rp nil)
			   (hs1 hs)
			   (hs2 (append (list-of-n (len g))
					(greater-natp-nodes (len g) hs)
					(non-natp-nodes hs))))))))


;;; ------------------------------------------------------
;;;
;;; 5.2)  Normalization of {\tt dag-nodes-aux} expressions
;;;
;;; ------------------------------------------------------

;;; Analyzing the definition of {\tt dag-nodes-aux}, one could think
;;; that it is easy to prove that in a dag, {\tt dag-nodes} of a node is
;;; strictly greater than {\tt dag-nodes} of its neighbors. But ther is
;;; a subtle detail: the second argument of {\tt dag-nodes-aux} is
;;; different in the recursive call. Nevertheles we can "fix" this
;;; asimmetry:


;;; The function {\tt dag-nodes-aux} is independent of its second argument

(defthm dag-nodes-aux-independent-of-path
  (implies (and (dag-p-aux hs rev-path g)
		(dag-p-aux hs rev-path2 g))
	   (equal (dag-nodes-aux hs rev-path g)
		  (dag-nodes-aux hs rev-path2 g)))
  :rule-classes nil)

;;; Using this previous property and the property {\tt
;;; dag-p-main-property}, we "normalize" expressions involving {\tt
;;; dag-p-aux}, by means of the following rewrite rule:

(defthm dag-nodes-aux-subsetp-rewrite-rule
  (implies (and (dag-p g)
		(dag-p-aux hs rp g)
 		(syntaxp (not (and (consp rp) (eq (car rp) 'quote)))))
 	   (equal (dag-nodes-aux hs rp g)
 		  (dag-nodes-aux hs nil g)))
  :hints (("Goal" :use ((:instance dag-nodes-aux-independent-of-path
				   (rev-path rp)
				   (rev-path2 nil))))))


(in-theory (enable neighbors))


;;; ---------------------------
;;;
;;; 5.3)  The intended theorems
;;;
;;; ---------------------------


(defthm measure-rec-dag-e0-ordinalp
   (e0-ordinalp (measure-rec-dag flg h g)))

(encapsulate

 ()

 (local
  (defthm dag-recursion-case-1-lemma
    (implies (and (dag-p g)
		  (term-dag-non-variable-p h g))
	     (dag-p-aux (cdr (nth h g)) (list (nfix h)) g))
    :hints (("Goal" :use (:instance dag-p-main-property
				   (hs (list h)))
	     :in-theory (disable dag-p-main-property)))))

 (defthm dag-recursion-case-1
   (implies (and (dag-p g)
		 (term-dag-non-variable-p h g)
		 flg)
	    (e0-ord-< (measure-rec-dag nil (term-dag-args h g) g)
		      (measure-rec-dag flg h g)))
   :hints (("Goal" :expand (dag-nodes-aux (list h) nil g)))))


(encapsulate
 ()

 (local
  (defthm dag-recursion-case-2-lemma
    (implies (and (dag-p g)
		  (term-dag-is-p h g))
	     (dag-p-aux (list (nth h g)) (list (nfix h)) g))
    :hints (("Goal" :use (:instance dag-p-main-property
				    (hs (list h)))
	     :in-theory (disable dag-p-main-property)))))

 (defthm dag-recursion-case-2
   (implies (and (dag-p g)
		 (term-dag-is-p h g)
		 flg)
	    (e0-ord-< (measure-rec-dag flg (nth h g) g)
		      (measure-rec-dag flg h g)))
   :hints (("Goal" :expand (dag-nodes-aux (list h) nil g)))))

(defthm dag-recursion-case-3
  (implies (and (dag-p g) (consp h))
	   (e0-ord-< (measure-rec-dag t (car h) g)
		     (measure-rec-dag nil h g)))
  :hints (("Goal" :expand (dag-nodes-aux h nil g))))


(defthm dag-recursion-case-4
  (implies (and (dag-p g) (consp h))
	   (e0-ord-< (measure-rec-dag nil (cdr h) g)
		     (measure-rec-dag nil h g)))
    :hints (("Goal" :expand (dag-nodes-aux h nil g))))

;;; We disable {\tt measure-rec-dag}

(in-theory (disable measure-rec-dag))



;;; RECALL: These two theorems would allow us to define functions like these:
;;; ·········································································


; (defun occur-check-l (flg x h g)
;   (declare (xargs :measure (measure-rec-dag flg h g)))
;   (if (dag-p g)
;       (if flg
;   	  (let ((p (term-dagi-l h g)))
; 	    (if (integerp p)
; 		(occur-check-l flg x p g)
; 	      (let ((args (cdr p)))
; 		(if (equal args t)
; 		    (= x h)
; 		  (occur-check-l nil x args g)))))
; 	(if (endp h)
; 	    nil
; 	  (or (occur-check-l t x (car h) g)
; 	      (occur-check-l nil x (cdr h) g))))
;    t))


; (defun deref-l (h g)
;   (declare (xargs :measure (measure-rec-dag t h g)))
;   (if (dag-p g)
;       (let ((p (term-dagi-l h g)))
; 	(if (integerp p) (deref-l p g) h))
;     nil))

; (defun dag-as-term-l (flg h g)
;   (declare (xargs :measure (measure-rec-dag flg h g)))
;   (if (dag-p g)
;       (if flg
;   	  (let ((p (term-dagi-l h g)))
; 	    (if (integerp p)
; 		(dag-as-term-l flg p g)
; 	      (let ((args (cdr p))
; 		    (symb (car p)))
; 		(if (equal args t)
; 		    symb
; 		  (cons symb (dag-as-term-l nil args g))))))
; 	(if (endp h)
; 	    h
;  	  (cons (dag-as-term-l t (car h) g)
;  		(dag-as-term-l nil (cdr h) g))))
;     nil))

(in-theory (enable nfix))

(in-theory (disable dag-p))



;;; ===============================================================
