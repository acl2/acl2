(in-package "ACL2")

#|

We introduce functions for loading the datastructure of the
stobj-based pathfinding program and prove that the loading and
calculating of this optimized program works just like the original
implementation.

See also "fpst.lisp".

Matt Wilding and David Greve
Updated February, 2003

|#

;; Assumes the "find path - stobj" program is loaded
(include-book "fpst")

(set-verify-guards-eagerness 2)

;; We want to prove the guards of the functions we need from J's
;; proof.  However, some of the functions are not guard-provable
;; because the guards weren't in place.  In this case, we add a
;; function with the same body and the needed guards, and use that
;; instead.

(defun myall-nodes (g)
  (declare (xargs :guard (alistp g)))
  (cond ((endp g) nil)
	(t (cons (car (car g))
		 (myall-nodes (cdr g))))))

(defthm myall-nodes-is-all-nodes
  (equal
   (myall-nodes g)
   (all-nodes g)))

; mygraph1p is just like J's graph1p, except that the node and the
; children are in-range naturals.
(defun mygraph1p (g nodes)
  (declare (xargs :guard (and (true-listp nodes) (alistp g))))
  (cond ((endp g) t)
	(t (and (consp (car g))
		(true-listp (cdr (car g)))
		(numberlistp (car g) (maxnode))       ; needed for stobj version
		(subsetp (cdr (car g)) nodes)
		(no-duplicatesp (cdr (car g)))
		(mygraph1p (cdr g) nodes)))))

(defthm mygraph1p-is-graph1p
  (implies
   (mygraph1p g nodes)
   (graph1p g nodes)))

(defun mygraphp (g)
  (declare (xargs :guard (alistp g)))
  (and (alistp g)
       (eqlable-listp (myall-nodes g))
       (no-duplicatesp (myall-nodes g))
       (mygraph1p g (myall-nodes g))))

(defthm mygraphp-is-graphp
  (implies
   (mygraphp g)
   (graphp g)))

(defun myneighbors (node g)
  (declare (xargs :guard (alistp g)))
  (cond ((endp g) nil)
	((equal node (car (car g)))
	 (cdr (car g)))
	(t (myneighbors node (cdr g)))))

(defthm myneighbors-is-neighbors
  (equal
   (myneighbors n g)
   (neighbors n g)))

(defthm consp-neighbors
  (implies
   (mygraph1p g l)
   (iff
    (consp (neighbors i g))
    (neighbors i g))))

(defthm gp-update-nth
  (implies
   (and
    (gp g)
    (listp v)
    (bounded-natp i max))
   (gp (update-nth i v g)))
  :hints (("goal" :in-theory (enable update-nth))))


;; Now, some functions that allow us to load the stobj with
;; values in the datastructures used by J's implementation.

(defun load-graph1 (g i st)
  (declare (xargs :stobjs st
		  :guard (and (stp st) (alistp g)
			      (bounded-natp i (1+ (maxnode)))
			      (mygraphp g))
		  :measure (max 0 (nfix (- (maxnode) i)))))
  (if (or (not (integerp i)) (not (< i (maxnode))))
      st
      (let
	  ((st (update-gi i (myneighbors i g) st)))
	(load-graph1 g (1+ i) st))))

(defun load-graph (g st)
  (declare (xargs :stobjs st
		  :guard (and (stp st) (alistp g) (mygraphp g))))
  (load-graph1 g 0 st))

(defun init-marks1 (i st)
  (declare (xargs :stobjs st
		  :guard (and (stp st) (bounded-natp i (1+ (maxnode))))
		  :measure (max 0 (nfix (- (maxnode) i)))))
  (if (or (not (integerp i)) (not (< i (maxnode))))
      st
      (let
	  ((st (update-marksi i 0 st)))
	(init-marks1 (1+ i) st))))

;; Some rules about our loading functions
(defthm stp-load-graph1
  (implies
   (and
    (stp st)
    (mygraphp g)
    (integerp i)
    (<= 0 i))
   (stp (load-graph1 g i st))))

(defthm stp-init-marks1
  (implies
   (and
    (stp st)
    (integerp i)
    (<= 0 i))
   (stp (init-marks1 i st))))

(defthm nth-init-marks1-other
  (implies
   (not (equal i (marksindex)))
   (equal (nth i (init-marks1 j st))
	  (nth i st))))

(defun init-marks (st)
  (declare (xargs :stobjs st :guard (stp st)))
  (init-marks1 0 st))

(defun load-st (g st)
  (declare (xargs :stobjs st
		  :guard (and (stp st) (alistp g) (mygraphp g))))
  (let ((st (load-graph g st)))
    (let ((st (init-marks st)))
      (let ((st (update-status 1 st)))
	(let ((st (update-stack nil st)))
	  st)))))

(defthm graph-equivp-only-on-g
  (implies
   (equal (nth (gindex) st1) (nth (gindex) st2))
   (equal
    (graph-equivp1 g st1 i)
    (graph-equivp1 g st2 i)))
  :rule-classes nil)

(defthm graph-equivp1-init-marks
  (equal
   (graph-equivp1 g (init-marks1 i st) i)
   (graph-equivp1 g st i))
  :hints (("goal" :use (:instance graph-equivp-only-on-g
				  (st1 (init-marks1 i st)) (st2 st)))))
(defthm graphp1-equal-graphs
  (implies
   (and
    (equal (nth (gindex) st1) (nth (gindex) st2))
    (stp st1)
    (stp st2))
   (iff
    (graphp1-st st1 i)
    (graphp1-st st2 i)))
  :hints (("goal" :in-theory (enable graphp1-st)))
  :rule-classes nil)

(defthm graphp1-st-lesser
  (implies
   (and
    (graphp1-st st i)
    (bounded-natp i j))
   (graphp1-st st j))
  :hints (("goal" :in-theory (enable graphp1-st))))

(defthm graphp1-st-init-marks
  (implies
   (and
    (stp st)
    (integerp i)
    (<= 0 i))
   (equal
    (graphp1-st (init-marks1 i st) i)
    (graphp1-st st i)))
   :hints (("goal" :use (:instance graphp1-equal-graphs
				   (st1 (init-marks1 i st)) (st2 st))
	    :in-theory (disable stp))))

(defthm nth-0-load-graph1-above
  (implies
   (and
    (bounded-natp i j)
    (integerp j))
  (equal
   (nth i (nth (gindex) (load-graph1 g j st)))
   (nth i (nth (gindex) st)))))

(defthm graph-equivp1-load-graph1
  (implies
   (bounded-natp i (maxnode))
   (graph-equivp1 g (load-graph1 g i st) i))
  :hints (("Subgoal *1/3'" :expand (:free (x) (LOAD-GRAPH1 G x ST)))
	  ("Subgoal *1/3''" :expand (:free (x n) (GRAPH-EQUIVP1 G x n)))))

(defthm nth-1-init-marks-above
  (implies
   (and
    (bounded-natp i j)
    (integerp j))
  (equal
   (nth i (nth (marksindex) (init-marks1 j st)))
   (nth i (nth (marksindex) st)))))

(defthm mark-equivp1-init-marks1
  (implies
   (and
    (integerp i)
    (<= 0 i))
   (mark-equivp1 nil (init-marks1 i st) i)))

(defthm equiv-load-st
  (equiv nil g nil (load-st g st))
  :hints (("goal" :in-theory (set-difference-theories
			      (enable graph-equivp mark-equivp)
			      '(graph-equivp1 mark-equivp1 init-marks1)))))

(defthm numberlistp-neighbors
  (implies
   (mygraph1p g n)
   (numberlistp (neighbors i g) (maxnode))))

(defthm graph1p-st-load-graph1
  (implies
   (and
    (mygraphp g)
    (integerp i)
    (<= 0 i))
  (graphp1-st (load-graph1 g i st) i))
  :hints (("goal" :in-theory (enable load-graph1 graphp1-st))))

(defun linear-find-st (a b g st)
  (declare (xargs :stobjs st
		  :guard (and (stp st)
			      (bounded-natp a (maxnode))
			      (bounded-natp b (maxnode))
			      (alistp g)
			      (mygraphp g))))
  (let ((st (load-st g st)))
    (let ((st (linear-find-next-step-st-mbe (list a) b st)))
      (if (not (equal (status st) 0))
	  (mv 'failure st)
	(mv (stack st) st)))))

(defthm nth-init-marks1
  (implies
   (and
    (integerp j)
    (integerp i)
    (<= 0 i)
    (<= j i)
    (< i (maxnode)))
  (equal (nth i (nth (marksindex) (init-marks1 j st)))
	 0))
  :hints (("goal" :expand ((INIT-MARKS1 I ST)))))

(defthm linear-find-next-step-st-mbe-base
  (implies
   (and
    (equal (nth i (nth (marksindex) st)) 0)
    (bounded-natp i (maxnode))
    (equal (stack st) nil))
   (equal (nth (stackindex) (linear-find-next-step-st-mbe (list i) i st)) (list i)))
  :hints (("goal" :expand (linear-find-next-step-st-mbe (list i) i st))))

(defthm nth-load-graph1
  (implies
   (and
    (integerp i)
    (<= 0 i)
    (not (equal i (gindex))))
   (equal (nth i (load-graph1 g j st))
	  (nth i st))))

;; ****************
;; Main lemma
;; ****************
;; Our implementation returns the same value as the original
;; list-based one when we load the stobj using the functions
;; of this file.
(defthm linear-find-st-linear-find-path
  (implies
   (and
    (bounded-natp a (maxnode))
    (bounded-natp b (maxnode))
    (mygraphp g)
    (stp st))
  (equal
   (car (linear-find-st a b g st))
   (linear-find-path a b g)))
  :hints (("goal" :use ((:instance implementations-same (stack nil) (mt nil) (c (list a))
				   (st (load-st g st)))
			equiv-load-st)
	   :in-theory (disable linear-find-path-is-find-path equiv-load-st stp))))

#|
ACL2 !>(assign g '((0 1 2) (1) (2 0 1 2 3) (3 1)))
 ((0 1 2) (1) (2 0 1 2 3) (3 1))
ACL2 !>(mygraphp (@ g))
T
ACL2 !>(stp st)
T
ACL2 !>(linear-find-st 0 3 (@ g) st)
((0 2 3) <st>)
ACL2 !>(linear-find-path 0 3 (@ g))
(0 2 3)

|#

;; Some functions for building graphs

;; Generate a graph with nodes numbered curr though last and edges
;; from each node to the list all
(defun completeg-helper (curr last all)
  (declare (xargs :verify-guards t))
  (declare (xargs :measure (nfix (- (1+ (nfix last)) (nfix curr)))))
  (if (<= (nfix curr) (nfix last))
      (cons
       (cons curr all)
       (completeg-helper (1+ (nfix curr)) last all))
    nil))

;; Generate a list of naturals from curr to last
(defun listofnats (curr last)
  (declare (xargs :verify-guards t
		  :measure (nfix (- (1+ (nfix last)) (nfix curr)))))
  (if (<= (nfix curr) (nfix last))
      (cons
       curr
       (listofnats (1+ (nfix curr)) last))
    nil))

;; Generate a complete graph with nodes 0 to size-1
(defun completeg (size)
  (declare (xargs :verify-guards t))
  (completeg-helper 0 (1- (nfix size)) (listofnats 0 (1- (nfix size)))))

;; Generate a "bad" graph with n nodes.  Nodes 0..n-1 are a complete
;; graph, and node n is disconnected
(defun badg (size)
  (declare (xargs :verify-guards t))
  (cons
   (list size)
   (completeg size)))

#|

The pathfinder can be run from the ACL2 read-eval-print loop.

First, load this book

   ACL2 !>(include-book
           "run-fpst")
   Loading /accts/dagreve/local/src/acl2-2.8a/books/arithmetic/equalities.o
   start address -T 1827ecc Finished loading /accts/dagreve/local/src/acl2-2.8a/books/arithmetic/equalities.o
   Loading /accts/dagreve/local/src/acl2-2.8a/books/arithmetic/rational-listp.o

   ...

   Summary
   Form:  ( INCLUDE-BOOK ; manual editing by Matt K. to avoid Makefile-deps dependency
            "run-fpst" ...)
   Rules: NIL
   Warnings:  None
   Time:  1.49 seconds (prove: 0.00, print: 0.00, other: 1.49)
    "/accts/dagreve/ACL/challenges/graph/run-fpst.lisp"

Next, load the datastructure with a graph.  In this example, we load a
graph with 1,000 nodes and 1,000,000 edges, which takes about a minute.

   ACL2 !>(load-st (badg 1000) st)
   <st>

We try to find a non-existent path so that the program traverses all
the edges.  This requires less than a second.

   ACL2 !>(linear-find-next-step-st-mbe (list 0) 1000 st)
   <st>
   ACL2 !>(status st)
   1

We reset the marks array and search for an existing path.  Note that
it's not guaranteed to be the shortest one, only a valid one.

   ACL2 !>(init-marks st)
   <st>
   ACL2 !>(linear-find-next-step-st-mbe (list 0) 6 st)
   <st>
   ACL2 !>(status st)
   0
   ACL2 !>(stack st)
   (0 1 2 3 4 5 6)

|#
