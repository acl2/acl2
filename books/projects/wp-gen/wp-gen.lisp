(in-package "ACL2")

(include-book "shared")
(include-book "mutrec/mutrec")
(include-book "xdoc/top" :dir :system)

;; Original lisp implementation by Wilfred Legato. (Original comments have been
;; modified and added.)  Conversion to ACL2 (4/20/2011) by Sarah Weissman

;; This file contains routines which support reasoning about assembly
;; language programs using Dijkstra's Weakest Preconditions.
;; Symbols represent variables or function/predicate names.
;; Substitutions are represented by association lists.  The identity
;; substitution is represented by t.

;; The semantics of assembly language programs are captured using Dijkstra's
;; predicate transformer, which maps the postcondition of an instruction into
;; its weakest precondition.  Predicate transformers are represented by a
;; substitution operator that maps variables in the new state to expressions in
;; the old state.

;; Each node of the input program corresponds to a macro instruction whose
;; predicate transformer is computed by converting a sequential substitution
;; into a parallel substitution.  Nodes have the following format:
;;
;; (:node
;;    :label idx
;;    :pre annot-pre
;;    :subst sub
;;    :branches ((pred1 . idx1) ... (predn . idxn))
;;    :post annot-post)
;;
;; The idx component is a label for for the macro instruction.  The sub
;; component is the sequential substitution representing the effects of the
;; micro program.  (predi . idxi) pairs represent the condition (predi) under
;; which control transfers to the instruction with index idxi.  annot-pre is
;; a predicate on state prior to execution of the instruction. annot-post is
;; the predicate on state following execution of the instruction) at the
;; node. This sequence of nodes represents a forward control flow graph of the
;; program. This graph is then converted into an inverse control flow graph,
;; whose nodes have the following format:
;;
;; (idx annot mark wp sub prev1 prev2 ... )
;;
;; The idx component has the same meaning as before.  annot is the annotation
;; for the node.  mark is initially set to the number of successors to this
;; node.  wp is initially set to nil, and is used to accumulate the computation
;; of the weakest precondition.  sub is  a substitution representing the combined
;; action of all instructions which were collapsed into this node.  prev1,
;; prev2, ... are of the form (predi . nodei), where nodei is a node which
;; transfers control to (idx mark wp sub prev1 prev2 ... ) under condition
;; predi.

;; Here are accessors for the nodes of the two graphs.


; Forward control flow

(defmacro node-label (x) `(cadr (assoc-keyword :label ,x)))
(defmacro node-substitution (x) `(cadr (assoc-keyword :subst ,x)))
(defmacro node-branches (x) `(cadr (assoc-keyword :branches ,x)))
(defmacro node-pre-annotation (x) `(if (consp (assoc-keyword :pre ,x))
				       (cadr (assoc-keyword :pre ,x))
				     t))
(defmacro node-post-annotation (x) `(if (consp (assoc-keyword :post ,x))
				       (cadr (assoc-keyword :post ,x))
				     t))


; Inverse control flow

(defmacro idx (node) `(car ,node))
(defmacro pre-annot (node) `(cadr , node))
(defmacro post-annot (node) `(caddr , node))
(defmacro mark (node) `(cadddr ,node))
(defmacro wp (node) `(car (cddddr ,node)))
(defmacro sub (node) `(cadr (cddddr ,node)))
(defmacro prev (node) `(cddr (cddddr ,node)))
(defmacro predi (prev) `(caar ,prev))
(defmacro nodei (prev) `(cdar ,prev))

;; remove any subst pair in sigma with a car that occurs as the
;; the car of a subst pair in tau
(defun sub-difference (sigma tau)
  (if (atom sigma)
      nil
    (if (assoc-equal (caar sigma) tau)
	(sub-difference (cdr sigma) tau)
      (cons (car sigma)
	    (sub-difference (cdr sigma) tau)))))

;; applies the substitution sigma to the substitution tau
(defun apply-sigma-tau (sigma tau)
  (if (atom tau)
      nil
    (let* ((s (car tau))
	   (sig-rs (sublis sigma (cdr s))))
      (if (equal (car s) sig-rs)
	  (apply-sigma-tau sigma (cdr tau))
	(cons (cons (car s)
		    sig-rs)
	      (apply-sigma-tau sigma (cdr tau)))))))

;; composes two substitutions.  The resulting substitution is
;; equivalent to first applying tau then sigma.
(defun composer (sigma tau)
  (if (atom sigma)
      tau
    (if (atom tau)
	sigma
      (append (sub-difference sigma tau)
	      (apply-sigma-tau sigma tau)))))

;; convert a parallel substitution to a serial substitution
(defun parallel-to-serial-sub (sigma)
  (if (atom sigma)
      nil
    (composer (list (car sigma))
	      (parallel-to-serial-sub (cdr sigma)))))

;; collects a skeleton inverse CFG from the nodes of the forward CFG
(defun collect-nodes (m)
  (if (atom m)
      nil
    (cons (list (node-label (cdar m))			      ; idx
		(node-pre-annotation (cdar m))		      ; annot
		(node-post-annotation (cdar m))		      ; annot
		(length (node-branches (cdar m)))	      ; mark
		nil				      ; wp
		(parallel-to-serial-sub (node-substitution (cdar m))))	      ; sub
	  (collect-nodes (cdr m)))))

;; Functions for setting values of inverse CFG node data structures
(defun set-sub-node (node sigma)
  (append
   (list (idx node)
	 (pre-annot node)
	 (post-annot node)
	 (mark node)
	 (wp node)
	 sigma)
   (prev node)))

(defun set-wp-node (node q)
  (append
   (list (idx node)
	(pre-annot node)
	(post-annot node)
	(mark node)
	q
	(sub node))
   (prev node)))

(defun set-prev-node (node prev)
  (append
   (list (idx node)
	 (pre-annot node)
	 (post-annot node)
	 (mark node)
	 (wp node)
	 (sub node))
   prev))

(defun decrement-mark-node (node)
  (append
   (list (idx node)
	 (pre-annot node)
	 (post-annot node)
	 (- (mark node) 1)
	 (wp node)
	 (sub node))
   (prev node)))

;; Sets the node in graph with index (idx node) to node
(defun set-node-graph (graph node)
  (if (atom graph)
      nil
    (if (eql (idx (car graph)) (idx node))
	(cons node (cdr graph))
      (cons (car graph)
	  (set-node-graph (cdr graph) node)))))


;; updates the list of branches to a node in the inverse CFG
(defun update-node-with-branch (branch node line-label)
  (if (equal (car node) (cdr branch))
      (set-prev-node
       node
       (append (list (cons (car branch) line-label))
	       (prev node)))
    node))

;; updates the list of branches in nodes in the inverse CFG
(defun update-graph-with-branch (branch graph line-label)
  (if (atom graph)
      nil
    (cons
     (update-node-with-branch branch (car graph) line-label)
     (update-graph-with-branch branch (cdr graph) line-label))))

;; updates the predecessor lists of the appropriate nodes of the
;; inverse CFG
(defun update-graph-with-branch-list (branches graph line-label)
  (if (atom branches)
      graph
    (update-graph-with-branch (car branches)
			      (update-graph-with-branch-list
			       (cdr branches)
			       graph
			       line-label)
			      line-label)))

;; builds the inverse CFG from the list of skeleton nodes and the
;; original forward CFG
(defun add-line-branches (line-list graph)
  (if (atom line-list)
      graph
    (add-line-branches
     (cdr line-list)
     (update-graph-with-branch-list (node-branches (cdar line-list))
				    graph
				    (node-label (cdar line-list))))))


;; generates an inverse control flow graph
(defun make-graph (main)
  (let* ((graph
	 (collect-nodes main)))
    (add-line-branches main graph)))

;idx annot mark wp sub blist

;; finds the node with minimum mark and returns its index in node-list
(defun find-min-mark (node-list graph mn mn-idx)
  (if (atom node-list)
      mn-idx
    (let* ((node-idx (car node-list))
	   (node (assoc node-idx graph)))
      (if (<= (mark node) mn)
	(find-min-mark (cdr node-list) graph (mark node) node-idx)
	(find-min-mark (cdr node-list) graph mn mn-idx)))))

;; sets the wp of the node in graph with label idx to q
(defun update-wp-graph (graph idx q)
  (if (atom graph)
      nil
    (if (equal idx (idx (car graph)))
	(cons (set-wp-node (car graph) q)
	      (cdr graph))
      (cons (car graph)
	    (update-wp-graph (cdr graph) idx q)))))

;; create a (hopefully) new name for a wp function according to index
;; and provided prefix
(defun make-wp-string (idx prefix)
  (intern
    (concatenate
     'string
     (if prefix
	 (concatenate
	  'string
	  (coerce (explode-atom prefix 10)
		  'string)
	  "-")
       "wp-")
     (coerce (explode-atom idx 10)
	     'string))
   "ACL2"))

;; Efficient disjunction of uninterpreted terms (not necessary but
;; makes function definitions simpler in the end)
(defun make-or (r l)
  (cond ((null l) r)
	((null r) l)
	((equal l t) t)
	((equal r t) t)
	(t
	 (list 'or r l))))

;; Efficient conjunction of uninterpreted terms (not necessary but
;; makes function definitions simpler in the end)
(defun make-and (r l)
  (cond ((null l) nil)
	((null r) nil)
	((equal l t) r)
	((equal r t) l)
	(t
	 (list 'and r l))))

;; The weakest precondition at node n is
;; Q_n /\ \sigma_n(\/_{n' \in S(n)} (P_n' /\ B_{n,n'}))
;;
;; where
;;
;;     Q_n is (annot n)
;;     \sigma_n is (sub n)
;;     \P_n is (wp n)
;;     B_{n,n'} is branch-cond
;;
;; To implement this at node, for each prev that is a predecessor of
;; node we accumulate (via disjunction) into (wp prev):
;;
;;          (sub prev) applied to (make-and (wp node) branch_cond)
;;
;; where the branch condition from prev to node is branch_cond
;;
;; See "A Weakest Precondition Model for Assembly Language Programs"
;; by Wilfred J. Legato for details
(defun acc-wp (prev node branch-cond state-vars prefix)
  (make-or (wp prev)
	   (make-and
	    (sublis (sub prev) (post-annot prev)) ;; do i want to do this?
	    (make-and
	     (pre-annot prev)
		 (sublis (sub prev)
			 (make-and
			       branch-cond
			       (cons (make-wp-string (idx node) prefix)
				     state-vars))
			 )))))

;; Initially set the wp of each node to be the annotation at that node
(defun init-wp (graph)
  (if (atom graph)
      nil
    (if (= (mark (car graph)) 0)
	(cons (set-wp-node (car graph) (post-annot (car graph)))
	      (init-wp (cdr graph)))
      (cons (car graph)
	    (init-wp (cdr graph))))))

;; Accumulate wps over the list of predecessors of a node
(defun acc-wp-list (prevlist node graph state-vars prefix)
  (if (atom prevlist)
      graph
    (let* ((prev (assoc (nodei prevlist) graph))
	   (bc (predi prevlist)))
      (acc-wp-list
       (cdr prevlist)
       node
       (set-node-graph graph
		     (decrement-mark-node
		      (set-wp-node prev (acc-wp prev node bc state-vars prefix))))
       state-vars
       prefix))))

;; remove node from node-list
(defun remove-node (node node-list)
  (if (atom node-list)
      nil
    (if (eql node (car node-list))
	(cdr node-list)
      (cons (car node-list)
	    (remove-node node (cdr node-list))))))

(defthm set-node-graph-conserves-length
  (equal (len (set-node-graph graph node))
	 (len graph)))

#|
(defthm acc-wp-list-conserves-length
  (equal (len (acc-wp-list l n graph vars))
	 (len graph)))

(defthm remove-node-reduces-acl2-count
  (implies (and (consp graph)
		(member-equal node graph))
	   (= (len (remove-node (acc-wp-list l node graph vars) node))
	      (len (remove-node graph node)))))
|#

;; Implements the algorithm described in
;; "A Weakest Precondition Model for Assembly Language Programs"
;; by Wilfred J. Legato
(defun wp-gen-graph (graph node-list state-vars n prefix)
  (if (zp n)
      graph
  (let* ((idx (find-min-mark node-list graph (mark (assoc (car node-list) graph)) nil))
	 (minnode (assoc idx graph)))
    (wp-gen-graph
     (acc-wp-list (prev minnode) minnode graph state-vars prefix)
     (remove-node idx node-list)
     state-vars
     (- n 1)
     prefix))))

;; Update the substitution at node to include a decrement for the counter
;; Used when a counter variable is supplied
(defun add-count-sub-node (node count-var)
  (let ((countsub (acons count-var `(- ,count-var 1) (sub node))))
    (set-sub-node node countsub)))

(defun add-count-sub-graph (graph count-var)
  (if (atom graph)
      nil
    (cons (add-count-sub-node (car graph) count-var)
	  (add-count-sub-graph (cdr graph) count-var))))

;; Functions for collecting variables that occur in each wp function
;; definition
;;
;; TODO: This over-approximates the necessary variables for each generated
;; function. Can we calculate exactly what variables are needed and avoid
;; having to use  "(set-irrelevant-formals-ok t)" below?
(defun collect-vars-sub (sigma)
  (if (atom sigma)
      nil
    (union-equal
     (collect-vars (cdar sigma))
     (collect-vars-sub (cdr sigma)))))

(defun collect-vars-branch (prev-list)
  (if (atom prev-list)
      nil
    (union-equal
     (collect-vars (predi prev-list))
     (collect-vars-branch (cdr prev-list)))))

(defun collect-vars-node (node)
  (union-equal (collect-vars-branch (prev node))
	       (union-equal (collect-vars (post-annot node))
			    (union-equal (collect-vars (post-annot node))
					 (collect-vars-sub (sub node))))))

(defun collect-vars-graph (graph)
  (if (atom graph)
      nil
    (union-equal (collect-vars-node (car graph))
		 (collect-vars-graph (cdr graph)))))

;; Check to make sure that the count-var given by the user does not
;; occur in the body of the function. If it does, produce an error.
(defun chk-vars-prog (count-var state-vars ctx)
  (and (member count-var state-vars)
	(er hard ctx
	    "Specified count variable ~x0 occurs in body of program."
	    count-var)))

;; Sets up the inverse CFG graph and state variables and calls the wp-generation function. Returns the inverse CFG populated with wp expressions.
(defun wp-gen (main count-var prefix ctx)
  (let* ((graph (make-graph main))
	 (state-vars (collect-vars-graph graph))
	 (node-list (get-alist-keys graph))
	 (graph (if count-var
		    (init-wp (add-count-sub-graph graph count-var))
		  (init-wp graph))))
    (prog2$
     (chk-vars-prog count-var state-vars ctx)
     (mv (wp-gen-graph graph node-list
			(if count-var
			    (append state-vars (list count-var))
			  state-vars)
			(len graph)
			prefix)
	  state-vars))))

;; Generates a defun from the (wp node) using the naming convention
;; wp-prefix-idx for each node of the input program
(defun collect-wp-node (node state-vars count-var prog-mode prefix)
  (cond (count-var
	 (list 'defun (make-wp-string (idx node) prefix)
	       (append state-vars (list count-var))
	       `(declare (xargs :measure (acl2-count ,count-var)))
	       `(if (zp ,count-var) nil
		  ,(wp node))))
	(prog-mode (list 'defun (make-wp-string (idx node) prefix)
			 state-vars
			 '(declare (xargs :mode :program))
			 (wp node)))
	(t (list 'defun (make-wp-string (idx node) prefix)
			 state-vars
			 (wp node)))))

(defun collect-wps-mutual (graph state-vars count-var prog-mode prefix)
  (if (atom graph)
      nil
    (cons (collect-wp-node (car graph) state-vars count-var prog-mode prefix)
	  (collect-wps-mutual (cdr graph) state-vars count-var prog-mode prefix))))

;; Generates a list of mutually recursive wp function defuns
(defun collect-wps (graph state-vars count-var prog-mode prefix mutrec)
      (append (if mutrec
                   (list 'mut-rec)
                 (list 'mutual-recursion))
	  (collect-wps-mutual graph state-vars count-var prog-mode prefix)))

;; Generates run-wp output as a list without making an event
(defun run-wp-list (main prefix count-var mutrec prog-mode)
  (mv-let (main-graph state-vars)
	  (wp-gen main count-var prefix 'run-wp)
      (append (if mutrec
                   (list 'mut-rec)
                 (list 'mutual-recursion))
              (collect-wps-mutual main-graph state-vars count-var prog-mode prefix))))


;; Top level macro for running wp procedure
(defmacro run-wp (main
		  &key
		  prefix  ; optional prefix for naming generated functions
		  count-var  ; optional variable for measure
		  (prog-mode 'nil)
		  (ccg 'nil)
                  (mutrec 't)
		  )

;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.
; ":DOC-SECTION run-wp
;
;generate WP functions~/
;
;See :DOC WEAKEST-PRECONDITIONS-GENERATOR.~/
;"

  (append
   '(encapsulate
     ()
     (set-ignore-ok t)
     (set-irrelevant-formals-ok t)
     (set-bogus-mutual-recursion-ok t))

   (if ccg '((set-termination-method :ccg))
     nil)

   `((make-event
      (mv-let (main-graph state-vars)
	       (wp-gen ,main ',count-var ',prefix 'run-wp)
	       (collect-wps
		main-graph
		state-vars
		',count-var
		,prog-mode
		',prefix
                ,mutrec))))))

(defxdoc run-wp
  :parents (run-wp)
  :short "Generate WP functions"
  :long "<p>See :DOC WEAKEST-PRECONDITIONS-GENERATOR.</p>

 ")

(deflabel weakest-preconditions-generator

;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.

; :doc
; ":DOC-SECTION weakest-preconditions-generator

;generate WP functions~/


;*OVERVIEW*

;This book generates weakest precondition predicates, which are
;admitted as (possibly mutually recursive) ACL2 functions as described
;in the paper ``A Weakest Precondition Model for Assembly Language
;Programs'' by Bill Legato, dated January 28, 2003.

;The input program is given in a variation of Legato's format for
;assembly language programs. In this format each node of the program
;(where node roughly corresponds to program line) is represetned as a
;sequential substitution defining updates to state. Presently, state
;variables are inferred from the given substitutions and predicates and
;all functions are given as functions of full state with irrelevant
;formals ignored. (See :DOC IRRELEVANT-FORMALS)

;No particular program language is required. The right hand side of a
;substitution can be any function defined in the current ACL2 logical
;world, although we typically think of these operations as being
;low-level or primitive. Many of the examples provided with the book
;use pcode operations, for which a partial semantics has been provided
;in \"examples/pcode.lisp\".~/


;*GENERAL FORM*
;        (run-wp main)

;Here main is the program to be analyzed, in the format as specified
;below in the section *PROGRAM FORMAT*.  (Also, see examples directory
;for some sample programs).

;A user of this book will generally want to specify one or more of the
;following options.


;*OPTIONS*

;:prefix - a prefix for the generated function names, which is
;appended to the node label when the WP for the node is generated. This
;is generally useful for providing meaningful function names and for
;avoiding function naming conflicts. If no prefix is specified, the
;default prefix for each function is \"wp-\".

;:count-var - a count variable to be decremented by the substitution at
;each node. This allows ACL2 to automatically calculate a measure for
;the (possibly) mutually recursive WP definitions. If the count
;variable is not unique from the state variables in main, run-wp will
;generate an error.

;:prog-mode - Default value is nil. If prog-mode is set to t the WP functions
;are defined in prog-mode, which allows ACL2 to skip proofs.

;:ccg - Default value is nil. If the ccg books are available and
;included in the current ACL2 environment then setting :ccg to t will
;attempt to use CCG analysis to automatically calculate a measure. (See
;http://acl2s.ccs.neu.edu/acl2s/doc/ for more details on CCG and The ACL2 Sedan.)

;:mutrec - Default value is t. Uses a call tree analysis to determine
;which WP functions are mutually recursive, and defines those in a
;mutual-recursion form. The rest are defined as individual defuns. This
;should generally be on (unless it is acting buggy, in which case
;contact the author) as bogus mutual recursions can make ACL2 proofs
;more difficult.


;*PROGRAM FORMAT*

;A program consists of a list of nodes in the following format.

;(:node
;   :label idx
;   :pre annot-pre
;   :subst sub
;   :branches ((pred1 . idx1) ... (predn . idxn))
;   :post annot-post)

;where:
; idx is a unique node label (possibly corresponding to a program line number,
;     e.g. l_1, l_2,...)
; annot-pre is a predicate on state prior to execution of the line (i.e., before
;           the given substituation on program state is applied)
; sub is a substitution representing execution as an alist
; branches specifies program control using (pred . idx) pairs, where pred is a
;          condition on state and idx is the label of a node
; annot-post is a predicate on state after execution of the line


;*MISCELLANY*

;To generate a list of WP functions without admitting them, use run-wp-list:

;(run-wp-list main prefix count-var mutrec prog-mode)

;e.g.

;(ld \"examples/sum.lisp\")
;(run-wp-list (@ new-prog) 'wp-new1 'count t nil)

;Generates:

; (MUT-REC (DEFUN WP-NEW1-L_1 (U V W COUNT)
;                (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT)))
;                (IF (ZP COUNT)
;                    NIL
;                    (WP-NEW1-L_2 U (INT_XOR U 12345 32)
;                                 W (- COUNT 1))))
;         (DEFUN WP-NEW1-L_2 (U V W COUNT)
;                (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT)))
;                (IF (ZP COUNT)
;                    NIL
;                    (WP-NEW1-L_3 U V (INT_ADD V 2345345299 32)
;                                 (- COUNT 1))))
;         (DEFUN WP-NEW1-L_3 (U V W COUNT)
;                (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT)))
;                (IF (ZP COUNT)
;                    NIL
;                    (OR (AND (NOT (= (INT_EQUAL W 8281919193 32) 1))
;                             (WP-NEW1-L_END U V W (- COUNT 1)))
;                        (AND (= (INT_EQUAL W 8281919193 32) 1)
;                             (WP-NEW1-L_BAD U V W (- COUNT 1))))))
;         (DEFUN WP-NEW1-L_BAD (U V W COUNT)
;                (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT)))
;                (IF (ZP COUNT) NIL T))
;         (DEFUN WP-NEW1-L_END (U V W COUNT)
;                (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT)))
;                (IF (ZP COUNT) NIL NIL)))

;Note: This form will generate an error from ACL2 as given, because it
;contains irrelevant formals.~/
;"
)

(defxdoc weakest-preconditions-generator
  :parents (weakest-preconditions-generator)
  :short "Generate WP functions"
  :long "<p>*OVERVIEW*</p>

 <p>This book generates weakest precondition predicates, which are admitted as
 (possibly mutually recursive) ACL2 functions as described in the paper ``A
 Weakest Precondition Model for Assembly Language Programs'' by Bill Legato,
 dated January 28, 2003.</p>

 <p>The input program is given in a variation of Legato's format for assembly
 language programs. In this format each node of the program (where node roughly
 corresponds to program line) is represetned as a sequential substitution
 defining updates to state. Presently, state variables are inferred from the
 given substitutions and predicates and all functions are given as functions of
 full state with irrelevant formals ignored. (See :DOC IRRELEVANT-FORMALS)</p>

 <p>No particular program language is required. The right hand side of a
 substitution can be any function defined in the current ACL2 logical world,
 although we typically think of these operations as being low-level or
 primitive. Many of the examples provided with the book use pcode operations,
 for which a partial semantics has been provided in
 \"examples/pcode.lisp\".</p>

 <p>*GENERAL FORM* (run-wp main)</p>

 <p>Here main is the program to be analyzed, in the format as specified below
 in the section *PROGRAM FORMAT*.  (Also, see examples directory for some
 sample programs).</p>

 <p>A user of this book will generally want to specify one or more of the
 following options.</p>

 <p>*OPTIONS*</p>

 <p>:prefix - a prefix for the generated function names, which is appended to
 the node label when the WP for the node is generated. This is generally useful
 for providing meaningful function names and for avoiding function naming
 conflicts. If no prefix is specified, the default prefix for each function is
 \"wp-\".</p>

 <p>:count-var - a count variable to be decremented by the substitution at each
 node. This allows ACL2 to automatically calculate a measure for the (possibly)
 mutually recursive WP definitions. If the count variable is not unique from
 the state variables in main, run-wp will generate an error.</p>

 <p>:prog-mode - Default value is nil. If prog-mode is set to t the WP
 functions are defined in prog-mode, which allows ACL2 to skip proofs.</p>

 <p>:ccg - Default value is nil. If the ccg books are available and included in
 the current ACL2 environment then setting :ccg to t will attempt to use CCG
 analysis to automatically calculate a measure. (See
 http://acl2s.ccs.neu.edu/acl2s/doc/ for more details on CCG and The ACL2
 Sedan.)</p>

 <p>:mutrec - Default value is t. Uses a call tree analysis to determine which
 WP functions are mutually recursive, and defines those in a mutual-recursion
 form. The rest are defined as individual defuns. This should generally be on
 (unless it is acting buggy, in which case contact the author) as bogus mutual
 recursions can make ACL2 proofs more difficult.</p>

 <p>*PROGRAM FORMAT*</p>

 <p>A program consists of a list of nodes in the following format.</p>

 <p>(:node :label idx :pre annot-pre :subst sub :branches ((pred1 . idx1)
    ... (predn . idxn)) :post annot-post)</p>

 <p>where: idx is a unique node label (possibly corresponding to a program line
  number, e.g. l_1, l_2,...)  annot-pre is a predicate on state prior to
  execution of the line (i.e., before the given substituation on program state
  is applied) sub is a substitution representing execution as an alist branches
  specifies program control using (pred . idx) pairs, where pred is a condition
  on state and idx is the label of a node annot-post is a predicate on state
  after execution of the line</p>

 <p>*MISCELLANY*</p>

 <p>To generate a list of WP functions without admitting them, use
 run-wp-list:</p>

 <p>(run-wp-list main prefix count-var mutrec prog-mode)</p>

 <p>e.g.</p>

 <p>(ld \"examples/sum.lisp\") (run-wp-list (@@ new-prog) 'wp-new1 'count t
 nil)</p>

 <p>Generates:</p>

 <p>(MUT-REC (DEFUN WP-NEW1-L_1 (U V W COUNT) (DECLARE (XARGS :MEASURE
                 (ACL2-COUNT COUNT))) (IF (ZP COUNT) NIL (WP-NEW1-L_2 U
                 (INT_XOR U 12345 32) W (- COUNT 1)))) (DEFUN WP-NEW1-L_2 (U V
                 W COUNT) (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT))) (IF (ZP
                 COUNT) NIL (WP-NEW1-L_3 U V (INT_ADD V 2345345299 32) (- COUNT
                 1)))) (DEFUN WP-NEW1-L_3 (U V W COUNT) (DECLARE (XARGS
                 :MEASURE (ACL2-COUNT COUNT))) (IF (ZP COUNT) NIL (OR (AND (NOT
                 (= (INT_EQUAL W 8281919193 32) 1)) (WP-NEW1-L_END U V W (-
                 COUNT 1))) (AND (= (INT_EQUAL W 8281919193 32) 1)
                 (WP-NEW1-L_BAD U V W (- COUNT 1)))))) (DEFUN WP-NEW1-L_BAD (U
                 V W COUNT) (DECLARE (XARGS :MEASURE (ACL2-COUNT COUNT))) (IF
                 (ZP COUNT) NIL T)) (DEFUN WP-NEW1-L_END (U V W COUNT) (DECLARE
                 (XARGS :MEASURE (ACL2-COUNT COUNT))) (IF (ZP COUNT) NIL
                 NIL)))</p>

 <p>Note: This form will generate an error from ACL2 as given, because it
 contains irrelevant formals.</p>")
