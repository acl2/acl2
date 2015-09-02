;;; ============================================================================
;;; dag-unification-rules.lisp
;;; Título: Unification rules on term dags
;;; ============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "dag-unification-rules")

|#

(in-package "ACL2")


(include-book "dags")
(include-book "list-unification-rules")



;;; ============================================================================
;;;
;;; 0) Introducción
;;;
;;; ============================================================================

;;; In this book, we define and verify a set of rules of transformation
;;; designed to obtain most general solutions of system of equations,
;;; when these systems of equations are represented as directed acyclicic
;;; graphs (dags).

;;; In the book {\tt dags.lisp}, we describe a representation of graphs
;;; using lists, where each element of the list describe a node of the
;;; graph. With this representation, if the graph is well--formed (this
;;; notion of well-formedness implies, for example, that the graph is
;;; acyclicic) every index (natural number) pointing to a node of the
;;; graph can be seen as a first order term. In the same way, we can
;;; define {\em indices systems} (representing systems of equations) or
;;; {\em indices substitutions} (representing substitutions), with
;;; respect to a given well--formed term dag. In this book we formally
;;; define {\em well--formed term dags} and the correspondece between
;;; well--formed term dags and first order terms.

;;; It is also possible to define the set of unification transformation
;;; rules of Martelli--Montanari, acting on this terms dag
;;; representation. We will define these transformation rules in an
;;; analogue way to the rules defined in the book {\tt
;;; list\--unification\--rules\--.lisp}, but taking into account that
;;; the representation of terms is based on dags.

;;; The main properties of the transformation rules acting on term dags
;;; can be proved by compositional reasoning, because similar properties
;;; were proved for the transformation rules acting on standard
;;; list/prefix representation of terms. For that purpose, we show that
;;; every transformation step given at the "dag level" corresponds to a
;;; transformation step given at the "list/prefix level". Having proved
;;; this fundamental result, it is easy to conclude that some sequences
;;; of transformation rules acting on term dags lead to find the most
;;; general solution (if it is solvable) of the system represented
;;; by the initial inidices system and term dag. This is a key result to
;;; design a unification algorithm acting on term dags.

;;; In sum, in this book:


;;; *)
;;;  We define well--formedness properties for term dags and unification
;;;  problems represented using term dags.
;;; *)
;;;  We define the correspondence between the dag representation and the
;;;  standard list/prefix notation of first--order terms.
;;; *)
;;;  We define the Martelli--Montanari unification rules with respect to
;;;  the term dag representation.
;;; *)
;;;  We show that the well--formedness properties are preserved by the
;;;  transformation rules.
;;; *)
;;;  We show that for every transformation step given at the "dag level",
;;;  there exists a corresponding step given at the "list/prefix level".
;;; *)
;;;  We extend these properties to sequences of transformation rules.
;;; *)
;;;  And finally, using compositional reasoning, we show that some
;;;  sequences of dag transformations starting in a given indices system
;;;  may be used to compute a most general solution (or detect
;;;  unsolvability) of the system of equations represented by the
;;;  initial indices system.
;;; -)


;;; The following books are used, and contain information that is
;;; relevant to understand the contents of this book:

;;; *)
;;;  The book {\tt dags.lisp} contains information about how term graphs
;;;  are represented, and the intended meaning of the information stored
;;;  in nodes. The concept of directed acyclic graphs is  defined and
;;;  verified. An interesting result about updating dags is also used
;;;  here. And also a well--founded measure to recurse on term dags is
;;;  defined (this measure will allow us to define several functions in
;;;  this book).
;;; *)
;;;  The book {\tt list-unification-rules.lisp} contains the definition
;;;  and verification of the main properties of the Martelli--Montanari
;;;  unification rules, representing first--order terms in the standard
;;;  list/prefix representation.  Once proved the correspondence between
;;;  the transformation steps given with the dag representation and with
;;;  the standard representation, the results of the book are used
;;;  here to prove analogue properties about the transformation rules
;;;  given at the "dag level".
;;; -)


;;; ============================================================================
;;;
;;; 1) Well--formed term dags
;;;
;;; ============================================================================

;;; In this section, we define well--formedness properties for those
;;; ACL2 objects representing term dags, systems of equations,
;;; substitutions and unification problems.  We also define the
;;; correspondence between these objects and the first--order terms,
;;; systems, substitutions and unification problems represented in the
;;; standard list/prefix representation.

;;; Previously, we define the following macros to access and update the
;;; contents of a term graph. These names resemble the corresponding
;;; accessor and updater functions that will be automatically defined
;;; when defining a single--threaded object storing the graph (see the
;;; book {\tt terms\--dag\--stobj\-.lisp}).

(defmacro dagi-l (i g)
  `(nth ,i ,g))

(defmacro update-dagi-l (i v g)
  `(update-nth ,i ,v ,g))


;;; In the following, {\em by an index we mean a natural number}.

;;; -----------------------------------
;;;
;;; 1.1)  Well--formedness properties
;;;
;;; -----------------------------------

;;; The following function define true lists of indices bounded by a
;;; given natural number:

(defun bounded-nat-true-listp (l n)
  (declare (xargs :guard (natp n)))
  (if (atom l)
      (equal l nil)
    (and (natp (car l))
	 (< (car l) n)
	 (bounded-nat-true-listp (cdr l) n))))

;;; And a function for true lists of natural numbers:

(defun nat-true-listp (l)
  (declare (xargs :guard t))
  (if (atom l)
      (equal l nil)
    (and (natp (car l))
	 (nat-true-listp (cdr l)))))

;;; Both concepts are related:

(defthm bounded-nat-true-listp-nat-true-listp
  (implies (bounded-nat-true-listp l n)
	   (nat-true-listp l)))


;;; The following function defines {\em term graphs}. That is, lists
;;; having the expected contents: indices -or- @nil@ -or- pairs of
;;; symbol functions and a bounded true list of indices -or- pairs of
;;; variable symbol and the symbol @t@ (see {\tt dags.lisp} for
;;; details). Note that we also require that the symbols (functions and
;;; variables) have to be eqlablep. The first function
;;; @term-graph-p-aux@ also takes as argument the bound for the
;;; indices. As a particular case, the function @term-graph-p@ is
;;; defined as a particular case when the bound is the length of the
;;; graph.

(defun bounded-term-graph-p (g n)
  (declare (xargs :guard (natp n)))
  (if (atom g)
      t
    (and (or (equal (car g) nil)
	     (and (natp (car g)) (< (car g) n))
	     (and (consp (car g))
		  (eqlablep (caar g))
		  (or (equal (cdar g) t)
		      (bounded-nat-true-listp (cdar g) n))))
	 (bounded-term-graph-p (cdr g) n))))


(defun term-graph-p (g)
   (declare (xargs :guard t))
   (bounded-term-graph-p g (len g)))


;;; Some properties about the contents:


(defthm bounded-term-graph-p-nth-property-1
   (implies (and (bounded-term-graph-p g n)
		 (integerp (nth h g)))
	    (<= 0 (nth h g)))
   :rule-classes :linear)


(defthm bounded-term-graph-p-nth-property-2
   (implies (and (bounded-term-graph-p g n)
		 (integerp (nth h g)))
	    (< (nth h g) n))
   :rule-classes :linear)



;;; REMARS: Some of the conditions required in the definition of
;;; @term-graph-p@ are required by the expected properties of the
;;; unification algorithm (for example, that the indices have to be
;;; natural numbers). Other properties are required if we want that our
;;; algorithm be Common Lisp compliant; that is, for guard
;;; verification (for example the "eqlablep" properties or the bound for
;;; the indices). Moreover, the properties about the bound of the
;;; indices are only needed for the "stobj" version of the algorithm
;;; (see the book {\tt dag-unification-st.lisp}). But we include it here
;;; because we will prove here some invariant properties about these
;;; well-formedness conditions that will be needed later for guard
;;; verification.

;;; Since only some of the above properties are required for the
;;; correctness of the unification algorithm, it will be sometimes more
;;; comfortable to define only those properties (without the properties
;;; required for guard verification). And also this weaker property
;;; sometimes are enough for the guards of this book:

(defun quasi-term-graph-p (g)
  (declare (xargs :guard t))
  (if (atom g)
      t
    (and (or (natp (car g))
	     (equal (car g) nil)
	     (and (consp (car g)) (variable-p (caar g)) (equal (cdar g) t))
	     (and (consp (car g)) (nat-true-listp (cdar g))))
	 (quasi-term-graph-p (cdr g)))))


;;; Relation between these concepts:


(defthm bounded-term-graph-p-implies-quasi-term-graph-p
  (implies (bounded-term-graph-p g n)
	   (quasi-term-graph-p g)))


;;; The list of variable symbols of a term graph:

(defun list-of-term-dag-variables (g)
  (declare (xargs :guard (quasi-term-graph-p g)))
  (cond ((atom g) nil)
	((and (consp (car g)) (equal (cdar g) t))
	 (cons (caar g) (list-of-term-dag-variables (cdr g))))
	(t (list-of-term-dag-variables (cdr g)))))


;;; Useful property for guard verification (see {\tt
;;; dag-unification-st.lisp}).


(defthm list-of-term-dag-variables-eqlable-listp
  (implies (bounded-term-graph-p g n)
	   (eqlable-listp (list-of-term-dag-variables g))))


;;; A {\em well-formed term dag} is an acyclic term graph, with shared
;;; variables. We define the "bounded" version and the "relaxed"
;;; version.

(defun bounded-well-formed-term-dag-p (g n)
   (and (bounded-term-graph-p g n)
        (dag-p g)
        (no-duplicatesp (list-of-term-dag-variables g))))


;;  REVISAR SI LO DEJO O NO
(defun well-formed-term-dag-p (g)
  (bounded-well-formed-term-dag-p g (len g)))

;;; The following function defines lists of pairs of indices. Given a
;;; well--formed term dag, these lists represent system of equations
;;; (see the next subsection). For that reason, we usually name them as
;;; {\em indices system}. Note that we require that those indices have
;;; to be bounded.

(defun bounded-nat-pairs-true-listp (l n)
  (declare (xargs :guard (natp n)))
  (if (atom l)
      (equal l nil)
    (and (consp (car l))
	 (natp (caar l)) (< (caar l) n)
	 (natp (cdar l)) (< (cdar l) n)
	 (bounded-nat-pairs-true-listp (cdr l) n))))


;;; The following function defines lists of pairs such that the second
;;; element is an index (the first element, although implicit, is
;;; intended to be a variable symbol). Given a well--formed term dag,
;;; these lists represent substitutions (see the next subsection). For
;;; that reason, we usually name them as {\em indices substitution}.


(defun bounded-nat-substitution-p (l n)
  (declare (xargs :guard (natp n)))
  (if (atom l)
      (equal l nil)
    (and (consp (car l))
	 (natp (cdar l)) (< (cdar l) n)
	 (bounded-nat-substitution-p (cdr l) n))))


;;; The following function defines what we call {\em well--formed
;;; dag unification problems}: 3--tuples containing an indices system, an
;;; indices substitution and a well--formed term dag. The unification
;;; transformation relation will be defined acting on these objects. As
;;; in the standard notation, the indices system represent the system of
;;; equations to be solved and the indices substitution represent the
;;; substitution partially computed. In this case a well--formed term
;;; dag is needed, to store the terms pointed by the indices of the
;;; system and the substitution.

(defun bounded-well-formed-upl (upl n)
  (and (bounded-nat-pairs-true-listp (first upl) n)
       (bounded-nat-substitution-p (second upl) n)
       (bounded-well-formed-term-dag-p (third upl) n)))



(defun well-formed-upl (upl)
  (bounded-well-formed-upl upl (len (third upl))))



;;; -----------------------------------
;;;
;;; 1.2) Relations between dags and terms, substitutions and systems
;;;
;;; -----------------------------------

;;; The following function computes the term associated to an index or a
;;; list of indices:

(defun dag-as-term-l (flg h g)
  (declare (xargs :measure (measure-rec-dag flg h g)))
  (if (dag-p g)
      (if flg
  	  (let ((p (dagi-l h g)))
	    (if (integerp p)
		(dag-as-term-l flg p g)
	      (let ((args (cdr p))
		    (symb (car p)))
		(if (equal args t)
		    symb
		  (cons symb (dag-as-term-l nil args g))))))
	(if (endp h)
	    h
 	  (cons (dag-as-term-l t (car h) g)
 		(dag-as-term-l nil (cdr h) g))))
    'undef))


;;; There are several remarks that are worth to be pointed out here.

;;; 1)
;;; Note that the function is defined at the same time for
;;; indices and for lists of indices, using the flag @flg@ to indicate
;;; if @h@ is an index or a list of indices. This style of definitions
;;; is very similar to our definitions on the stucture of terms (see,
;;; for example, {\tt terms.lisp}).
;;; 2)
;;; Note that the admission of this function is not trivial. In
;;; fact, we need to explicitly test that the graph @g@ is acyclic. The
;;; measure function {\tt measure\--rec\--dag} and the proved properties
;;; that allow the admission of this functions are in the book {\tt
;;; dags\-.lisp}.
;;; -)

;;; Given an indices system and a term dag, the following function computes the
;;; corresponding system of equations in list/prefix noation:

(defun tbs-as-system (S g)
  (if (endp S)
      S
    (cons (cons (dag-as-term-l t (caar S) g)
		(dag-as-term-l t (cdar S) g))
	  (tbs-as-system (cdr S) g))))

;;; Given an indices substitution and a term dag, the following function
;;; computes the corresponding substitution in list/prefix notation:

(defun solved-as-system (sol g)
  (if (endp sol)
      sol
    (cons (cons (caar sol)
		(dag-as-term-l t (cdar sol) g))
	  (solved-as-system (cdr sol) g))))

;;; Given a well--formed dag unification problem, the following function computes
;;; the corresponding unification problem in list/prefix representation:


(defun upl-as-pair-of-systems (upl)
  (if (not upl)
      nil
    (let ((S (first upl))
	  (sol (second upl))
	  (g (third upl)))
      (list (tbs-as-system S g)
	    (solved-as-system sol g)))))


;;; ============================================================================
;;;
;;; 2) Unification transformation rules acting on term dags
;;;
;;; ============================================================================

;;; In this section, we define the unification rules of
;;; Martelli--Montanari acting on well-formed dag unification
;;; problems. As in the case of the standard representation (see {\tt
;;; list\--unification\--rules\-.lisp}), we will define it by means of
;;; operators, the applicability test, and the one--step of reduction
;;; function of the transformation.

;;; Previously, we define two important auxiliary functions that recurse
;;; on the term dag structure.

;;; The following function checks if a given index @x@ (corresponding to
;;; a variable node) is in the subgraph pointed by another index
;;; @h@. Note again the measure used in the admission of the function
;;; and the explicit @dag-p@ check:

(defun occur-check-l (flg x h g)
  (declare (xargs :measure (measure-rec-dag flg h g)))
  (if (dag-p g)
      (if flg
  	  (let ((p (dagi-l h g)))
	    (if (integerp p)
		(occur-check-l flg x p g)
	      (let ((args (cdr p)))
		(if (equal args t)
		    (= x h)
		  (occur-check-l nil x args g)))))
	(if (endp h)
	    nil
	  (or (occur-check-l t x (car h) g)
	      (occur-check-l nil x (cdr h) g))))
    'undef))



;;; The following function finds the end of an instantiation chain,
;;; following the "IS" nodes starting in the node @h@. Note
;;; again the measure used in the admission of the function and the
;;; explicit @dag-p@ check:


(defun dag-deref-l (h g)
  (declare (xargs :measure (measure-rec-dag t h g)))
  (if (dag-p g)
      (let ((p (dagi-l h g)))
	(if (integerp p) (dag-deref-l p g) h))
    'undef))


;;; -----------------------------------
;;;
;;; 2.1) Applicability test on term dags
;;;
;;; -----------------------------------

;;; To define the unification transformation rules of
;;; Martelli--Montanari acting on term dags, we will use the same
;;; operators than in the standard representation (see {\tt
;;; list\--unification\--rules\-.lisp}).  Here these operators are
;;; applied to well--formed dag unification problems: that is, 3--tuples
;;; containing an indices substitution, and indices system and a
;;; well--formed term dag.  Operators are the following:

;;; 1)
;;; {\tt (delete $N$)}: delete  equation $N$ of the indices system.
;;; 2)
;;; {\tt (decompose $N$)}: decompose equation $N$.
;;; 3)
;;; {\tt (orient $N$)}: orient equation $N$.
;;; 4)
;;; {\tt (eliminate $N$)}: eliminate equation N.
;;; 5)
;;; {\tt (clash1 $N$)}: clash for different top function symbol
;;; (equation $N$).
;;; 6)
;;; {\tt (clash2 $N$)}: clash for different number of arguments
;;; (equation $N$).
;;; 7)
;;; {\tt (occur-check $N$)}: detect occur-check (equation $N$).
;;; -)


;;; The function @unif-legal-l@ defines the applicability test of the
;;; operators. Recall that the number $N$ in the operator indicates the
;;; (indices) equation of the indices system of equation. Note also the
;;; use of @dag-deref-l@ in the definition of @unif-legal-l@; thus the
;;; first two arguments of the following auxiliary functions are the
;;; indices of the $N$-th equation of the system, after applying
;;; @dag-deref-l@ (this ensures that they are not "IS" nodes). We now
;;; describe the auxiliary functions used for each of the rules. \\


;;; {\tt DELETE} can be applied if both indices are the same:

(defun unif-legal-l-delete (t1 t2 g)
  (declare (ignore g))
  (equal t1 t2))


;;; {\tt DECOMPOSE} can be applied if both indices point to
;;; non--variable nodes with the same function symbol and the list of
;;; indices corresponding to their arguments can be paired:


(defun unif-legal-l-decompose (t1 t2 g)
  (and (not (term-dag-variable-p t1 g))
       (not (term-dag-variable-p t2 g))
       (equal (term-dag-symbol t1 g) (term-dag-symbol t2 g))
       (mv-let (pair-args bool)
	       (pair-args (term-dag-args t1 g) (term-dag-args t2 g))
	       (declare (ignore pair-args))
	       bool)))


;;; {\tt CLASH1} can be applied if both indices point to non--variable
;;; nodes with different function symbols:

(defun unif-legal-l-clash1 (t1 t2 g)
  (and (not (term-dag-variable-p t1 g))
       (not (term-dag-variable-p t2 g))
       (not (eql (term-dag-symbol t1 g)
		 (term-dag-symbol t2 g)))))


;;; {\tt CLASH2} can be applied if both indices point to non--variable
;;; nodes with lists of arguments that cannot be paired:

(defun unif-legal-l-clash2 (t1 t2 g)
  (and (not (term-dag-variable-p t1 g))
       (not (term-dag-variable-p t2 g))
       (mv-let (pair-args bool)
	       (pair-args (term-dag-args t1 g) (term-dag-args t2 g))
	       (declare (ignore pair-args))
	       (not bool))))

;;; {\tt ORIENT} can be applied if the first index points to a non--variable
;;; node and the second points to a variable:


(defun unif-legal-l-orient (t1 t2 g)
  (and (not (term-dag-variable-p t1 g))
       (term-dag-variable-p t2 g)))

;;; {\tt ELIMINATE} can be applied if the first index is a variable node
;;; not occurring in the subgraph pointed by the second:

(defun unif-legal-l-eliminate (t1 t2 g)
  (and (term-dag-variable-p t1 g)
       (not (occur-check-l t t1 t2 g))))


;;; {\tt OCCUR-CHECK} can be applied if the first index is a variable node
;;; occurring in the subgraph pointed by the second (that must be
;;; different):

(defun unif-legal-l-occur-check (t1 t2 g)
  (and (term-dag-variable-p t1 g)
       (not (equal t1 t2))
       (occur-check-l t t1 t2 g)))

;;; All these auxiliary functions allow us to define @unif-legal-l@:

(defun unif-legal-l (upl op)
  (let ((name (first op))
	(equ-n (second op))
	(tbs (first upl))
	(g (third upl)))
    (and (natp equ-n)
	 (< equ-n (len tbs))
	 (let* ((equ (nth equ-n tbs))
		(t1 (dag-deref-l (car equ) g))
		(t2 (dag-deref-l (cdr equ) g)))
	   (case name
		 (delete (unif-legal-l-delete t1 t2 g))
		 (decompose (unif-legal-l-decompose t1 t2 g))
		 (orient (unif-legal-l-orient t1 t2 g))
		 (eliminate (unif-legal-l-eliminate t1 t2 g))
		 (clash1 (unif-legal-l-clash1 t1 t2 g))
		 (clash2 (unif-legal-l-clash2 t1 t2 g))
		 (occur-check (unif-legal-l-occur-check t1 t2 g))
		 (t nil))))))


;;; -----------------------------------
;;;
;;; 2.2) One step of reduction on term dags
;;;
;;; -----------------------------------


;;; The function @unif-reduce-one-step-l@ defines the applicability test
;;; of the transformation rules. Note the auxiliary functions used for
;;; each of the rules. The same remarks as in the applicability test
;;; described in the previous subsection apply here, but the auxiliary
;;; functions also take here as arguments the rest of (indices)
;;; equations to be solved and the (indices) substitution partially
;;; computed. \\

;;; The application of {\tt DELETE} simply remove the selected equation:


(defun unif-reduce-one-step-l-delete (t1 t2 R sol g)
   (declare (ignore t1 t2))
   (list R sol g))

;;; The application of {\tt DECOMPOSE} replaces the selected equation by
;;; the equations obtained pairing the corresponding list of
;;; (indices) arguments:

(defun unif-reduce-one-step-l-decompose (t1 t2 R sol g)
  (let ((args1 (term-dag-args t1 g))
	(args2 (term-dag-args t2 g)))
    (mv-let (pair-args bool)
	    (pair-args args1 args2)
	    (declare (ignore bool))
	    (list (append pair-args R) sol g))))


;;; The application of {\tt CLASH1} obtains failure (represented as
;;; @nil@).

(defun unif-reduce-one-step-l-clash1 (t1 t2 R sol g)
  (declare (ignore t1 t2 R sol g))
  nil)


;;; The application of {\tt CLASH2} obtains failure (represented as
;;; @nil@).

(defun unif-reduce-one-step-l-clash2 (t1 t2 R sol g)
  (declare (ignore t1 t2 R sol g))
  nil)

;;; The application of {\tt ORIENT} reorients the selected equation:

(defun unif-reduce-one-step-l-orient (t1 t2 R sol g)
  (list (cons (cons t2 t1) R) sol g))


;;; The application of {\tt ELIMINATE} uses the selected equation to
;;; store a new binding in the indices substitution and updates the
;;; position corresponding to the first index with the second
;;; index. That is replace the variable node with an "IS" node. This is
;;; a key operation in the unification proccess:

(defun unif-reduce-one-step-l-eliminate (t1 t2 R sol g)
  (list R
	(cons (cons (term-dag-symbol t1 g) t2) sol)
	(update-dagi-l t1 t2 g)))

;;; The application of {\tt OCCUR-CHECK} obtains failure:


(defun unif-reduce-one-step-l-occur-check (t1 t2 R sol g)
  (declare (ignore t1 t2 R sol g))
  nil)

;;; All these auxiliary functions allow us to define @unif-reduce-one-step-l@:


(defun unif-reduce-one-step-l (upl op)
   (let* ((name (first op))
	  (equ-n (second op))
	  (S (first upl))
	  (sol (second upl))
	  (g (third upl))
	  (equ (nth equ-n S))
	  (R (eliminate-n equ-n S))
	  (t1 (dag-deref-l (car equ) g))
	  (t2 (dag-deref-l (cdr equ) g)))
   (case name
	 (delete (unif-reduce-one-step-l-delete t1 t2 R sol g))
	 (decompose (unif-reduce-one-step-l-decompose t1 t2 R sol g))
	 (orient (unif-reduce-one-step-l-orient t1 t2 R sol g))
	 (eliminate (unif-reduce-one-step-l-eliminate t1 t2 R sol g))
	 (clash1 (unif-reduce-one-step-l-clash1 t1 t2 R sol g))
	 (clash2 (unif-reduce-one-step-l-clash2 t1 t2 R sol g))
	 (occur-check (unif-reduce-one-step-l-occur-check t1 t2 R sol g))
	 (t nil))))

;;; ============================================================================
;;;
;;; 3) Relation between the transformations acting on both representations
;;;
;;; ============================================================================


;;; In this section, we are going to prove the following theorems,
;;; formalizing the relation between the transformation rules acting on
;;; term dags and the transformation rules acting on the standard
;;; list/prefix reesentation. These properties will be fundamental in
;;; order to prove, by compositional reasoning, that the rules can be
;;; used to compute most geneal solutions of systems. \\

;;; First goal: the well--formedness condition is preserved by the
;;; transformation rules:

; (defthm unif-reduce-one-step-l-preserves-well-formed-upl
;   (implies (and (well-formed-upl upl)
; 		  (unif-legal-l upl op))
; 	     (well-formed-upl (unif-reduce-one-step-l upl op) n)))


;;; Second goal: if an operator is legal with respect to a well--formed
;;; dag unification problem, then the same operator is legal with
;;; respect to the corresponding unification problem represented in
;;; list/prefix notation.

; (defthm unif-legal-l-implies-unif-legal-s
;    (implies (and (well-formed-upl upl)
; 		   (unif-legal-l upl op))
;  	      (unif-legal-s (upl-as-pair-of-systems upl) op)))

;;; Third goal: if an operator is legal with respect to a well--formed
;;; dag unification problem, the dag unification problem obtained
;;; applying the operator represents the same unification problem in
;;; list/prefix notation than the unification problem obtained applying
;;; the same operator to the list/prefix representation of the original
;;; unification problem:

; (defthm unif-reduce-one-step-l-equal-unif-reduce-one-step-s
;    (implies (and (well-formed-upl upl)
; 		   (unif-legal-l upl op))
; 	    (equal (upl-as-pair-of-systems (unif-reduce-one-step-l upl op))
; 		   (unif-reduce-one-step-s (upl-as-pair-of-systems upl)
; 					   op))))

;;; With these three properties, every sequence of transformation rules
;;; ``at the dag level'' can be transformed in a sequence of
;;; transformation ``at the list/prefix level''.

;;; Let us prove the above three properties.

;;; -----------------------------------
;;;
;;; 3.1) Some preliminary lemmas
;;;
;;; -----------------------------------

;;; Term graphs have variable symbols in variable nodes:

(local
 (defthm bounded-term-graph-p-variable-p
   (implies (and (term-dag-variable-p h g)
		 (bounded-term-graph-p g n))
	    (variable-p (term-dag-symbol h g)))
   :rule-classes :forward-chaining))

;;; The following lemmas establish properties related with the natural
;;; number contents of term graph nodes.

(local
 (defthm bounded-nat-pairs-true-listp-natp-car-and-cdr
   (implies (and (natp n) (< n (len l))
		 (bounded-nat-pairs-true-listp l m))
	    (and (natp (car (nth n l)))
		 (natp (cdr (nth n l)))))))



(local
 (defthm bounded-nat-pairs-true-listp-bounded-car-and-cdr
   (implies (and (natp n) (< n (len l))
		 (bounded-nat-pairs-true-listp l m))
	    (and (< (car (nth n l)) m)
		 (< (cdr (nth n l)) m)))))
;;   :rule-classes :linear))


(local
 (defthm bounded-term-graph-p-nth-positive
   (implies (bounded-term-graph-p g n)
	    (>= (nth h g) 0))
   :rule-classes :linear))

(local
 (defthm bounded-term-graph-p-contents
   (implies (and (bounded-term-graph-p g n)
		 (not (term-dag-variable-p h g))
		 (not (term-dag-is-p h g)))
	    (and (bounded-nat-true-listp (term-dag-args h g) n)
		 (nat-true-listp (term-dag-args h g))))))


(local
 (defthm bounded-nat-pairs-true-listp-l-eliminate-n
   (implies (and (natp n)
		 (bounded-nat-pairs-true-listp l m)
		 (< n (len l)))
	    (bounded-nat-pairs-true-listp (eliminate-n n l) m))))


(local
 (defthm bounded-nat-pairs-true-listp-append
   (implies (and (bounded-nat-pairs-true-listp l1 n)
		 (bounded-nat-pairs-true-listp l2 n))
	    (bounded-nat-pairs-true-listp (append l1 l2) n))))


(defun bounded-nat-listp (l m)
  (if (endp l)
      t
    (and (natp (car l)) (< (car l) m)
	 (bounded-nat-listp (cdr l) m))))

(local
 (defthm bounded-term-graph-p-bounded-nat-listp
   (implies (bounded-term-graph-p g n)
	    (bounded-nat-listp (cdr (nth h g)) n))))


(local
 (defthm bounded-nat-listp-pair-args
   (implies (and (bounded-nat-listp l1 m) (bounded-nat-listp l2 m))
	    (bounded-nat-pairs-true-listp (car (pair-args l1 l2)) m))))


;;; Below, three fundamental properties of @dag-deref-l@:

;;; 1)
;;; It returns an index.
;;; 2)
;;; The node pointed by this index is not an "IS" node.
;;; 3)
;;; The term corresponding to that index is the same than the term
;;; corresponding to that node (note the @syntaxp@ condition of this
;;; rule, used to prevent loops).
;;; -)

(local
 (defthm natp-dag-deref-l-bounded-term-graph-p
   (implies (and (natp h)
		 (bounded-term-graph-p g n)
		 (dag-p g))
	    (natp (dag-deref-l h g)))))



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
 (defthm dag-as-term-l-dag-deref-l
   (implies (syntaxp (not (and (consp h) (eq (car h) 'dag-deref-l))))
	    (equal (dag-as-term-l t h g)
		   (dag-as-term-l t (dag-deref-l h g) g)))))

(local (in-theory (disable dag-as-term-l-dag-deref-l)))


;;; The following group of lemmas show the main property of a term dag
;;; related with "shared variables". The lemma {\tt
;;; term-graph-variables-uniquely-determined} below prove that there are
;;; not two different variable nodes with the same variable symbol. As a
;;; corollary the lemma {\tt not\--equal\--pointers\--not\--equal\--terms} prove
;;; that the terms pointed by two different non-"IS" nodes, one of them
;;; a variable, are not equal (this property will be useful when
;;; reasoning about the {\tt ELIMINATE} rule).

(local
 (encapsulate
  ()

  (local
   (defthm injective-lemma-1-lemma
     (implies (and (not (member a (list-of-term-dag-variables l)))
		   (member x l)
		   (equal (cdr x) t))
	      (not (equal a (car x))))
     :rule-classes nil))

  (local
   (defthm injective-lemma-1
     (implies (and (consp g)
		   (no-duplicatesp (list-of-term-dag-variables g))
		   (equal (cdr (car g)) t)
		   (member x (cdr g))
		   (equal (cdr x) t))
	      (not (equal (caar g) (car x))))
     :hints (("Goal" :use (:instance injective-lemma-1-lemma
				     (l (cdr g))
				     (a (caar g)))))))

  (local
   (defthm injective-lemma-2
     (implies (and (consp g)
		   (natp i)
		   (not (equal i 0))
		   (term-dag-variable-p i g))
	      (member (dagi-l i g) (cdr g)))))

  (local
   (defun induction-hint (x1 x2 l)
     (cond ((endp l) 1)
	   ((zp x1) 2)
	   ((zp x2) 3)
	   (t (induction-hint (1- x1) (1- x2) (cdr l))))))

  (defthm term-graph-variables-uniquely-determined
    (implies (and (no-duplicatesp (list-of-term-dag-variables g))
		  (natp x1) (natp x2)
		  (term-dag-variable-p x1 g)
		  (term-dag-variable-p x2 g)
		  (not (equal x1 x2)))
	     (not (equal (term-dag-symbol x1 g)
			 (term-dag-symbol x2 g))))
    :hints (("Goal" :induct (induction-hint x1 x2 g))))


  (defthm not-equal-pointers-not-equal-terms
    (implies (and (bounded-term-graph-p g n)
		  (dag-p g)
		  (no-duplicatesp (list-of-term-dag-variables g))
		  (natp h1) (natp h2)
		  (term-dag-variable-p h1 g)
		  (not (term-dag-is-p h2 g))
		  (not (equal h1 h2)))
	     (not (equal (term-dag-symbol h1 g)
			 (dag-as-term-l t h2 g))))
    :hints (("Goal" :expand (dag-as-term-l t h2 g))))))

;;;(local (in-theory (disable bounded-well-formed-term-dag-p)))

;;; The following three events help us to reason about occur
;;; checks. Note that the "occur check" test used in the list/prefix
;;; representation simply checks if a variable is in the set of
;;; variables of a term. At the dag level, we traverse the graph
;;; seraching the variable node. To relate both approaches, we first
;;; define a function @occur-check-s@ acting on the list/prefix
;;; representation that traverses the list representing a term in a
;;; similar way that @occur-chek-l@ traverses the dag representing a
;;; term. The theorem {\tt occur-check-s-occur-check-l} relates both
;;; functions. Finally, the theorem {\tt occur\--check-s\--member\--variables}
;;; relates @occur-check-s@ with the condition used by {\tt OCCUR-CHECK}
;;; rule for the list/prefix representation.

(defun occur-check-s (flg x term)
  (if flg
      (if (variable-p term)
	  (equal x term)
	(occur-check-s nil x (cdr term)))
    (if (endp term)
	nil
      (or (occur-check-s t x (car term))
	  (occur-check-s nil x (cdr term))))))


(local
 (defthm occur-check-s-occur-check-l
   (implies (and (bounded-term-graph-p g n)
		 (dag-p g)
		 (no-duplicatesp (list-of-term-dag-variables g))
		 (natp x)
		 (if flg (natp h) (nat-true-listp h))
		 (term-dag-variable-p x g))
	    (iff (occur-check-l flg x h g)
		 (occur-check-s flg
				(term-dag-symbol x g)
				(dag-as-term-l flg h g))))))


(local
 (defthm occur-check-s-member-variables
   (implies (variable-p x)
	    (iff (occur-check-s flg x term)
		 (member x (variables flg term))))))


;;; -----------------------------------
;;;
;;; 3.2) Well--formed term dags preserved by the transformations
;;;
;;; -----------------------------------


;;; We prove in this subsection that the property of being a
;;; well--formed unification problem is preserved by the transformation
;;; rules. Not very surprisingly, the only rule that needs auxiliary
;;; lemmas to prove this, is the {\tt ELIMINATE} rule. It turns out to
;;; be difficult to show that the @dag-p@ property is preserved by the
;;; {\tt ELIMINATE} rule. \\

;;; First, we show that @term-graph-p@ is preserved by the {\tt
;;; ELIMINATE} rule:

(local
 (defthm bounded-term-graph-p-preserved-by-eliminate
   (implies (and (bounded-term-graph-p g n)
		 (natp x)
		 (natp h0)
		 (< h0 n))
	    (bounded-term-graph-p (update-dagi-l x h0 g) n))))

;;; Second, the following events prove that the {\tt ELIMINATE} rule
;;; preserves shared variables:

(local
 (encapsulate
  ()

  (local
   (defun submultisetp (l m)
     (if (endp l)
	 t
       (and (member (car l) m)
	    (submultisetp (cdr l) (delete-one (car l) m))))))

  (local
   (defthm delete-one-no-duplicatesp
     (implies (no-duplicatesp m)
	      (no-duplicatesp (delete-one l1 m)))))

  (local
   (defthm member-no-duplicatesp-1
     (implies (and (member l1 m)
		   (no-duplicatesp m))
	      (not (member l1 (delete-one l1 m))))))

  (local
   (defthm not-submultisetp-witness
     (implies (and (member l1 l2)
		   (not (member l1 d)))
	      (not (submultisetp l2 d)))))

  (local
   (defthm submultisetp-no-duplicatesp
     (implies (and (submultisetp l m)
		   (no-duplicatesp m))

	      (no-duplicatesp l))
     :rule-classes nil))

  (local
   (defthm submultisetp-list-of-term-dag-variables-update-nth-1
     (implies (and (natp x) (natp h0) (< x (len g)))
	      (submultisetp (list-of-term-dag-variables
			     (update-nth x h0 g))
			    (list-of-term-dag-variables g)))))

  (local
   (defthm list-of-term-dag-variables-update-nth-nil
     (implies (integerp h)
	      (not (consp (list-of-term-dag-variables (update-nth x h nil)))))))

  (local
   (defthm submultisetp-list-of-term-dag-variables-update-nth-2
     (implies (and (natp x) (natp h0) (>= x (len g)))
	      (submultisetp (list-of-term-dag-variables
			     (update-nth x h0 g))
			    (list-of-term-dag-variables g)))))

  (local
   (defthm submultisetp-list-of-term-dag-variables-update-nth
     (implies (and (natp x) (natp h0))
	      (submultisetp (list-of-term-dag-variables
			     (update-nth x h0 g))
			    (list-of-term-dag-variables g)))
     :hints (("Goal" :cases ((< x (len g)))))))



  (defthm no-duplicatesp-variables-preserved-by-eliminate
    (implies (and (natp x)
		  (natp h0)
		  (no-duplicatesp (list-of-term-dag-variables g)))
	     (no-duplicatesp (list-of-term-dag-variables (update-nth x h0
								     g))))
    :hints (("Goal" :use (:instance
			  submultisetp-no-duplicatesp
			  (l (list-of-term-dag-variables (update-nth x h0
								     g)))
			  (m (list-of-term-dag-variables g))))))))

;;; And finally, we show that the @dag-p@ property is preserved by the
;;; {\tt ELIMINATE} rule.

;;; To prove it, we need the following property (proved in {\tt
;;; dags.lisp}). This theorem establishes that if we update a dag in the
;;; form that {\tt ELIMINATE} does it, an we obtaing a cyclic graph,
;;; then there exists a path from the index used to update to the
;;; updated index, in the original graph.

; (defthm obtain-path-from-h-to-x-from-an-updated-dag-main-property
;   (let ((p* (obtain-path-from-h-to-x-from-an-updated-dag x h g)))
;     (implies (and (natp x) (natp h) (dag-p g)
; 		    (not (dag-p (update-nth x h g))))
; 	   (and (path-p p* g)
; 		(equal (first p*) h) (equal (car (last p*)) x)))))

;;; Therfore, it is not possible to obtain a cyclic graph if we apply
;;; {\tt ELIMINATE} only when the operator is legal, because the ``occur
;;; check'' ensures that there is no such path. That is what the
;;; following sequence of events establishes:

(local
 (encapsulate
  ()
  (local
   (defun induct-occur-check-l-path (flg h g path)
     (declare (xargs :measure (measure-rec-dag flg h g)))
     (if (dag-p g)
	 (if flg
	     (let ((p (dagi-l h g)))
	       (if (integerp p)
		   (induct-occur-check-l-path flg p g (cdr path))
		 (let ((args (cdr p)))
		   (if (equal args t)
		       t
		     (induct-occur-check-l-path nil args g (cdr path))))))
	   (if (endp h)
	       t
	     (cons (induct-occur-check-l-path t (car h) g path)
		   (induct-occur-check-l-path nil (cdr h) g path))))
       path))) ;;; to make this formal relevant

  (local
   (defthm map-nfix-true-listp
     (implies (nat-true-listp l)
	      (equal (map-nfix l) l))))

  (local
   (defthm occur-check-l-path-from-to-main-lemma
     (implies (and (dag-p g) (bounded-term-graph-p g n)
		   (if flg (natp h) (nat-true-listp h))
		   (natp x) (term-dag-variable-p x g)
		   (path-p p g)
		   (equal (car (last p)) x)
		   (if flg
		       (equal (first p) h)
		     (member (first p) h)))
	      (occur-check-l flg x h g))
     :hints (("Goal" :induct (induct-occur-check-l-path flg h g p)))))

  (local
   (defthm occur-check-l-path-from-to
     (implies (and (dag-p g)
		   (bounded-term-graph-p g n)
		   (natp x) (natp h)
		   (term-dag-variable-p x g)
		   (path-p p g)
		   (equal (car (last p)) x)
		   (equal (first p) h)
		   (member (first p) h))
	      (occur-check-l t x h g))
     :rule-classes nil))

  (defthm well-formed-term-dag-p-preserved-by-eliminate
    (implies (and (dag-p g)
		  (bounded-term-graph-p g n)
		  (not (occur-check-l t x h g))
		  (natp x) (natp h)
		  (term-dag-variable-p x g))
	     (dag-p (update-dagi-l x h g)))
    :hints (("Goal" :use
	     (obtain-path-from-h-to-x-from-an-updated-dag-main-property
	      (:instance occur-check-l-path-from-to
		   (p (obtain-path-from-h-to-x-from-an-updated-dag x h g)))))))))



;;; Finally, we have the intended theorem:

(defthm unif-reduce-one-step-l-preserves-bounded-well-formed-upl
  (implies (and (bounded-well-formed-upl upl n)
		(unif-legal-l upl op))
	   (bounded-well-formed-upl (unif-reduce-one-step-l upl op) n))
  :hints (("Goal" :in-theory (disable natp))))


;;; Later, we will need that the @n@ of the above theorem be (len (third
;;; upl)). That is, we need a similar theorem for well-formed-upl. Le us
;;; prove it.


(local
 (defthm len-update-nth-bis
   (implies (and (natp n) (< n (len l)))
	    (equal (len (update-nth n x l)) (len l)))))

(local
 (defthm unif-reduce-one-step-l-preserves-length
   (implies (and (well-formed-upl upl)
		 (unif-legal-l upl op)
		 (unif-reduce-one-step-l upl op))
	    (equal (len (third (unif-reduce-one-step-l upl op)))
		   (len (third upl))))))

(defthm unif-reduce-one-step-l-preserves-well-formed-upl
  (implies (and (well-formed-upl upl)
		(unif-legal-l upl op))
	   (well-formed-upl (unif-reduce-one-step-l upl op)))
  :hints (("Goal"
	   :in-theory (disable bounded-well-formed-upl
			       unif-legal-l
			       unif-reduce-one-step-l)
	   :cases ((unif-reduce-one-step-l upl op)))))




;;; -----------------------------------
;;;
;;; 3.3) Applicability with both representations
;;;
;;; -----------------------------------

;;; In this subsection, we show that if an operator is applicable to a
;;; well-formed dag unification problem then is applicable to the
;;; corresponding unification problem in the standard representation.  \\

;;; First, some previous lemmas about the function @tbs-as-system@

(local
 (defthm len-tbs-as-system
   (equal (len (tbs-as-system l g)) (len l))))

(local
 (defthm nth-tbs-as-system
   (implies (and (natp n) (< n (len l)))
	    (equal (nth n (tbs-as-system l g))
		   (cons (dag-as-term-l t (car (nth n l)) g)
			 (dag-as-term-l t (cdr (nth n l)) g))))))

(local
 (defthm eliminate-n-tbs-as-system
   (implies (and (natp n) (< n (len l)))
	    (equal (eliminate-n n (tbs-as-system l g))
		   (tbs-as-system (eliminate-n n l) g)))))


(local
 (defthm tbs-as-system-append
   (equal (tbs-as-system (append S1 S2) g)
	  (append (tbs-as-system S1 g) (tbs-as-system S2 g)))))




;;; The following events show that the function @pair-args@ behaves in
;;; the same way with both representations:


(local
 (encapsulate
  ()
  (local
   (defthm consp-dag-as-term-l
     (implies (and (dag-p g)
		   (consp l))
	      (consp (dag-as-term-l nil l g)))
     :hints (("Goal" :expand (dag-as-term-l nil l g)))))

  (local
   (defthm pair-args-dag-as-term-l-lemma
     (implies (and (dag-p g)
		   (not (consp l))
		   (not (equal l m)))
	      (not (equal l (dag-as-term-l nil m g))))
     :hints (("Goal" :cases ((consp m))))))

  (defthm pair-args-dag-as-term-l
    (implies (dag-p g)
	     (iff (second (pair-args (dag-as-term-l nil l g)
				     (dag-as-term-l nil m g)))
		  (second (pair-args l m)))))))


;;; Two special cases for our result:

(local
 (defthm unif-legal-l-implies-upl-not-nil
   (implies (not upl)
	    (not (unif-legal-l upl op)))
   :rule-classes nil))

(local
 (defthm unif-legal-upl-consp-op
   (implies (unif-legal-l upl op)
	    (and (consp op) (consp (cdr op))))
   :rule-classes nil))



;;; Finally, the intended result in this subsection:

(encapsulate
 ()

 (local
  (defthm unif-legal-l-implies-unif-legal-s-almost
    (implies (and (bounded-well-formed-term-dag-p (third upl) n)
		  (consp op) (consp (cdr op))
		  upl
		  (bounded-nat-pairs-true-listp (first upl) n)
		  (unif-legal-l upl op))
	     (unif-legal-s (upl-as-pair-of-systems upl) op))
    :hints (("Goal" :in-theory (enable dag-as-term-l-dag-deref-l)))
    :rule-classes nil))



 (defthm unif-legal-l-implies-unif-legal-s
   (implies (and (well-formed-upl upl)
		 (unif-legal-l upl op))
	    (unif-legal-s (upl-as-pair-of-systems upl) op))
   :hints (("Goal"
	    :in-theory (disable unif-legal-l unif-legal-s)
	    :use (
		  (:instance unif-legal-l-implies-unif-legal-s-almost
			     (n (len (caddr upl))))

		  unif-legal-l-implies-upl-not-nil
		  unif-legal-upl-consp-op)))))



;;; -----------------------------------
;;;
;;; 3.4) One step of reduction with both representations
;;;
;;; -----------------------------------

;;; We prove now our third goal in this section: the relation between
;;; the application of a legal operator in both representations. \\

;;; First, a technical lemma:

(local
 (encapsulate
  ()
  (local
   (defthm ugly-lemma-1
     (implies flg (and (equal (dag-as-term-l flg h g)
			      (dag-as-term-l t h g))
		       (equal (variables flg term)
			      (variables t term))))
     :rule-classes nil))

  (defthm substitution-does-not-change-term-particular-case
    (implies (and (not (member x (variables t (dag-as-term-l t h0 g))))
		  flg)
	     (equal (apply-subst
		     flg
		     (list (cons x t1))
		     (dag-as-term-l flg h0 g))
		    (dag-as-term-l t h0 g)))
    :hints (("Goal" :use
	     ((:instance substitution-does-not-change-term
			 (sigma (list (cons x t1)))
			 (term (dag-as-term-l flg h0 g)))
	      (:instance ugly-lemma-1 (h h0) (term (DAG-AS-TERM-L FLG H0 G)))))))))

;;; This lemma describes how the updates done by the {\tt ELIMINATE}
;;; rule affect to the term stored in a term graph. Note that simply
;;; updating a node with an index, one obtains an instantiation of the
;;; terms stored by the term dag. This a key property for the efficiency
;;; of the algorithms based on term dags:

(local
 (defthm eliminate-on-term-dags
   (implies (and (bounded-term-graph-p g n)
		 (dag-p g)
		 (no-duplicatesp (list-of-term-dag-variables g))
		 (not (occur-check-l t x h0 g))
		 (natp x) (natp h0)
		 (if flg (natp h) (nat-true-listp h))
		 (term-dag-variable-p x g))
	    (equal
	     (dag-as-term-l flg h (update-dagi-l x h0 g))
	     (apply-subst
	      flg
	      (list (cons (term-dag-symbol x g)
			  (dag-as-term-l t h0 g)))
	      (dag-as-term-l flg h g))))))


;;; Easy consequences of this property are the following results,
;;; extending the above property to the functions @apply-syst@ and
;;; @apply-range@ and describing how the eliminate rule affect to these
;;; functions:


(local
 (defthm tbs-as-system-apply-syst-eliminate
   (implies (and (bounded-term-graph-p g n)
		 (dag-p g)
		 (no-duplicatesp (list-of-term-dag-variables g))
		 (not (occur-check-l t x h0 g))
		 (natp x) (natp h0)
		 (bounded-nat-pairs-true-listp l n)
		 (term-dag-variable-p x g))
	    (equal (tbs-as-system l (update-nth x h0 g))
		   (apply-syst
		    (list (cons (term-dag-symbol x g)
				(dag-as-term-l t h0 g)))
		    (tbs-as-system l g))))))


(local
 (defthm solved-as-system-apply-range-eliminate
   (implies (and (bounded-term-graph-p g n)
		 (dag-p g)
		 (no-duplicatesp (list-of-term-dag-variables g))
		 (not (occur-check-l t x h0 g))
		 (natp x) (natp h0)
		 (bounded-nat-substitution-p l n)
		 (term-dag-variable-p x g))
	    (equal (solved-as-system l (update-nth x h0 g))
		   (apply-range
		    (list (cons (term-dag-symbol x g)
				(dag-as-term-l t h0 g)))
		    (solved-as-system l g))))))


;;; This lemma relates the value of @pair-args@ in both representations
;;; (it is needed for the {\tt DECOMPOSE} rule):

(local
 (defthm tbs-as-system-pair-args
   (implies (and (dag-p g) (second (pair-args l1 l2)))
	    (equal (tbs-as-system (car (pair-args l1 l2)) g)
		   (car (pair-args (dag-as-term-l nil l1 g)
				   (dag-as-term-l nil l2 g)))))))




;;; Finally, this is the intended result in this subsection:

(encapsulate
 ()
 (local
  (defthm unif-reduce-one-step-l-equal-unif-reduce-one-step-s-almost
    (implies (and (bounded-term-graph-p (third upl) n)
		  (dag-p (third upl))
		  (no-duplicatesp (list-of-term-dag-variables (third upl)))
		  upl
		  (consp op) (consp (cdr op))
		  (bounded-nat-pairs-true-listp (first upl) n)
		  (bounded-nat-substitution-p (second upl) n)
		  (unif-legal-l upl op))
	     (equal (upl-as-pair-of-systems (unif-reduce-one-step-l upl op))
		    (unif-reduce-one-step-s (upl-as-pair-of-systems upl)
					    op)))
    :hints (("Goal" :in-theory (enable dag-as-term-l-dag-deref-l)))
    :rule-classes nil))


 (defthm unif-reduce-one-step-l-equal-unif-reduce-one-step-s
   (implies (and (well-formed-upl upl)
		 (unif-legal-l upl op))
	    (equal (upl-as-pair-of-systems (unif-reduce-one-step-l upl op))
		   (unif-reduce-one-step-s (upl-as-pair-of-systems upl)
					   op)))
   :hints (("Goal"
	    :in-theory (disable unif-legal-l unif-reduce-one-step-l
				unif-reduce-one-step-s)
	    :use ((:instance
		   unif-reduce-one-step-l-equal-unif-reduce-one-step-s-almost
		   (n (len (third upl))))
		  unif-legal-l-implies-upl-not-nil
		  unif-legal-upl-consp-op)))))

(in-theory (disable well-formed-upl))

(local
 (in-theory (disable
	     upl-as-pair-of-systems
	     unif-legal-l unif-legal-s
	     unif-reduce-one-step-l unif-reduce-one-step-s)))


;;; ============================================================================
;;;
;;; 4) Sequences of transformation rules
;;;
;;; ============================================================================

;;; We now define sequences of transfromations acting on well--formed
;;; dag unification problems. As with the list/prefix notation (see
;;; functions @unif-seq-s-p@ and @unif-seq-s-last@ in {\tt
;;; list\--unification\--rules\-.lisp}), a sequence of transformations can be
;;; represented as the sequence of operators applied. The following
;;; function check that every of these operators is legal:


(defun unif-seq-l-p (upl unif-seq)
  (declare (xargs :measure (acl2-count unif-seq)))
  (if (endp unif-seq)
      t
    (let ((op (car unif-seq)))
      (and (unif-legal-l upl op)
	   (unif-seq-l-p
	    (unif-reduce-one-step-l upl op)
	    (cdr unif-seq))))))


;;; The following function obtains the last well--formed dag unification
;;; problem obtained by a sequence of transformations (given by a
;;; sequence of operators):


(defun unif-seq-l-last (upl unif-seq)
  (if (endp unif-seq)
      upl
    (unif-seq-l-last (unif-reduce-one-step-l upl (car unif-seq))
		     (cdr unif-seq))))


;;; Now, the properties shown in subsection 3.3 and 3.4 can be extended
;;; to sequences of transformations, establishing the relationship
;;; between @unif-seq-l-p@, @unif-seq-l-last@ and @unif-seq-s-p@,
;;; @unif-seq-s-last@ (taht is, showing how sequences of transformations
;;; acting on both representations are related):

(defthm unif-seq-l-p-unif-seq-s-p
  (implies (and (well-formed-upl upl)
		(unif-seq-l-p upl unif-seq))
	   (unif-seq-s-p (upl-as-pair-of-systems upl) unif-seq))
  :rule-classes nil)


(defthm unif-seq-s-last-unif-seq-l-last
  (implies (and (well-formed-upl upl)
		(unif-seq-l-p upl unif-seq))
	   (and
	    (well-formed-upl (unif-seq-l-last upl unif-seq))
	    (equal
	     (upl-as-pair-of-systems (unif-seq-l-last upl unif-seq))
	     (unif-seq-s-last (upl-as-pair-of-systems upl) unif-seq))))
  :rule-classes nil)




;;; Given an indices system and a well--formed term dag, we can define
;;; also a particular case of sequences of transformation. Those
;;; sequences of tranformation startin with a unification problem with
;;; that system and the empty substitution and ending in @nil@ (failure)
;;; or with an empty indices system and an indices substitution (recall
;;; the functions @mgs-seq-p@ and @mgs-seq@ in the book {\tt
;;; list-unification-rules.lisp}). We call these type of sequences of
;;; transformations {\em complete legal sequences} with respect to a
;;; given indices system and a term graph.

(defun mgs-seq-l-p (S g seq)
  (and (unif-seq-l-p (list S nil g) seq)
       (normal-form-syst (unif-seq-l-last (list S nil g) seq))))

(defun mgs-seq-l (S g seq)
  (unif-seq-l-last (list S nil g) seq))

;;; This function checks that a given initial indices system and graph
;;; form a well--formed dag unification problem:

(defmacro well-formed-dag-system (S g)
  `(well-formed-upl (list ,S nil ,g)))


(local
 (in-theory
  (enable mgs-seq-p mgs-seq bounded-well-formed-upl upl-as-pair-of-systems)))

;;; As a particular case of the above properties, the following three
;;; theorems show the relation between @mgs-seq-l-p@, @mgs-seq-l@ and
;;; @mgs-seq-p@, @mgs-seq@. That is:

;;; 1)
;;;  A complete legal sequence w.r.t. the dag representation is also
;;;  legal w.r.t. the list/prefix representation.
;;; 2)
;;; A complete legal sequence succeeds w.r.t. the dag representation
;;; if and only if it succeeds w.r.t. the list/prefix representation.
;;; 3)
;;;  The indices substitution finally obtained by a complet succesful
;;;  legal sequence
;;;  w.r.t. the dag representation represents the substitution finally
;;;  obtained by the same sequence w.r.t. the list/prefix
;;;  representation.
;;; -)




(defthm mgs-seq-l-p-mgs-seq-p
  (implies (and (well-formed-dag-system S g)
		(mgs-seq-l-p S g unif-seq))
	   (mgs-seq-p (tbs-as-system S g) unif-seq))
  :hints (("Goal" :use ((:instance unif-seq-l-p-unif-seq-s-p
				   (upl (list S nil g)))
			(:instance unif-seq-s-last-unif-seq-l-last
				   (upl (list S nil g)))))))


(defthm mgs-seq-l-mgs-seq-failure-success
  (implies (and (well-formed-dag-system S g)
		(mgs-seq-l-p S g unif-seq))
	   (iff (mgs-seq (tbs-as-system S g) unif-seq)
		(mgs-seq-l S g unif-seq)))
  :hints (("Goal" :use ((:instance unif-seq-l-p-unif-seq-s-p
				   (upl (list S nil g)))
			(:instance unif-seq-s-last-unif-seq-l-last
				   (upl (list S nil g)))))))

(defthm mgs-seq-l-mgs-seq-computed-substitution
  (let ((last-upl (mgs-seq-l S g unif-seq)))
    (implies (and (well-formed-dag-system S g)
		  (mgs-seq-l-p S g unif-seq))
	     (equal
	      (solved-as-system (second last-upl)
				(third last-upl))
	      (second (mgs-seq (tbs-as-system S g) unif-seq)))))
  :hints (("Goal" :use ((:instance unif-seq-l-p-unif-seq-s-p
				   (upl (list S nil g)))
			(:instance unif-seq-s-last-unif-seq-l-last
				   (upl (list S nil g)))))))

;;; This theorem is also interesting. The graph obtained by a complete
;;; legal sequence of transformations is acyclic:

(defthm mgs-seq-l-dag-p
  (implies (and (well-formed-dag-system S g)
		(mgs-seq-l-p S g unif-seq))
	   (dag-p (third (mgs-seq-l S g unif-seq))))
  :hints (("Goal"
	   :in-theory (enable well-formed-upl)
	   :use ((:instance unif-seq-l-p-unif-seq-s-p
			    (upl (list S nil g)))
		 (:instance unif-seq-s-last-unif-seq-l-last
			    (upl (list S nil g)))))))

(local (in-theory (disable mgs-seq-p mgs-seq)))
(in-theory (disable mgs-seq-l-p mgs-seq-l))



;;; ============================================================================
;;;
;;; 5) Using the rules to obtain most general solutions
;;;
;;; ============================================================================

;;; In the book {\tt list-unification-rules.lisp} we proved the main
;;; properties of sequences of transformation rules (functions
;;; @mgs-seq-p@ and @mgs-seq@) obtaining most general solutions of
;;; systems of equations (or failure). The above properties allows us
;;; (using compositional reasoning) to prove analogue properties of
;;; complete sequences of transformations on term dags. These properties
;;; are the final product of this book.

;;; If the system represented by an indices system has a solution, then
;;; every complete legal sequence of operators starting in that system
;;; succeeds:

(defthm mgs-seq-l-completeness
  (let ((S (tbs-as-system S-dag g)))
    (implies (and (well-formed-dag-system S-dag g)
		  (solution sigma S)
		  (mgs-seq-l-p S-dag g unif-seq))
	     (mgs-seq-l S-dag g unif-seq)))
  :hints (("Goal" :use (:instance mgs-seq-completeness
				  (S (tbs-as-system S-dag g))))))


;;; If a complete legal sequence of transformations on term dags
;;; succeeds, then the indices substitution finally obtained represents
;;; a solution of the system represented by the initial indices system:

(defthm mgs-seq-l-soundness
  (let* ((S (tbs-as-system S-dag g))
	 (last-upl (mgs-seq-l S-dag g unif-seq))
	 (sol (solved-as-system (second last-upl) (third last-upl))))
    (implies (and (well-formed-dag-system S-dag g)
		  (mgs-seq-l-p S-dag g unif-seq)
		  last-upl)
	     (solution sol S)))
  :hints (("Goal" :use (:instance mgs-seq-soundness
				  (S (tbs-as-system S-dag g))))))


;;; If a complete legal sequence of transformations on term dags
;;; succeeds, then the indices substitution finally obtained represents
;;; an idempotent substitution:

(defthm mgs-seq-l-idempotent
  (let* ((last-upl (mgs-seq-l S-dag g unif-seq))
	 (sol (solved-as-system (second last-upl) (third last-upl))))
    (implies (and (well-formed-dag-system S-dag g)
		  (mgs-seq-l-p S-dag g unif-seq))
	     (idempotent sol)))
  :hints (("Goal" :in-theory (disable idempotent))))

;;; If the system represented by an indices system has a solution, then
;;; it is subsumed by the substitution represented by the indices
;;; substitution obtaned by a complet legal sequence of transformations:


(defthm mgs-seq-l-most-general-solution
  (let* ((S (tbs-as-system S-dag g))
	 (last-upl (mgs-seq-l S-dag g unif-seq))
	 (sol (solved-as-system (second last-upl) (third last-upl))))
    (implies (and (well-formed-dag-system S-dag g)
		  (solution sigma S)
		  (mgs-seq-l-p S-dag g unif-seq))
	     (subs-subst sol sigma))))


;;; ===============================================================


