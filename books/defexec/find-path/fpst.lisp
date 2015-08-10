(in-package "ACL2")

#|

A Verified Pathfinder
---------------------

These files contain an optimized version of a program that searches
for a path in a graph.  It is the subject of 2 ACL2 workshop papers,
one in 2000 by Matt Wilding and one in 2003 by David Greve and Matt
Wilding, that describe using ACL2 features to build fast and
verifiable versions of these programs.

The initial version of this file introduced a stobj representing the
state that was proved equal to a (proved) pathfinding implementation
of J Moore's, and is documented in the 2000 paper.  Subsequently, the
proof was updated to work with the publically-released version of
Moore's proof distributed with the ACL2 book chapter in which Moore
wrote about this example.  An issue identified and discussed at length
in Wilding's 2000 paper is the need to add complexity to some programs
in order to prove termination.  In ACL2, sometimes this complexity
would not be necessary if there were some way to ensure that the
guards to the function would be met.  Wilding required an axiom in his
2000 example to prove that the fastest possible implementation of the
otherwise-proved program was correct.  The axiom was justified with an
informal argument, but its use highlighted a weakness in ACL2.

In 2003, Matt Kaufmann asked us to try out an experimental feature of
ACL2, MBE (which stands for "must be equal").  This feature allows the
introduction of executable versions of functions that can be justified
by appeal to their guards.  This led us to reimplement the pathfinding
program and associated proof yet again to demonstrate how this fast
implementation can now be proved correct with no assumptions.

This book certifies in experimental ACL2 2.8 in about 2 minutes.  See
the companion file "run-fpst.lisp" for functions that support the
running the pathfinding program.

Matt Wilding and David Greve
February 2003


Some original documentation for this program:

xx Stobj-Based Linear Find Path
xx
xx Matt Wilding
xx July 1999

xx J Moore developed an example in 1998 of a linear path search.  He
xx wrote the example of in some detail, and it is a wonderful example
xx of doing a small software proof using ACL2.  Subsequently, inspired
xx he writes in large part by our executable formal model work, J
xx added stobjs to ACL2.
xx
xx This file contains a linear path search program written in ACL2
xx that uses stobjs for data structures.  My goal in doing this is to
xx use stobjs in a context besides microprocessor models to explore
xx how practical this mechanism is for writing efficient, analyzable
xx code.  DSH suggested doing something softwarish with stobj last
xx January.
xx
xx We implement a pathfinding algorithm that employs stobjs.  It runs
xx fast and is proved correct.  Given a graph with numbered nodes and
xx edges, the program finds a path between two nodes if possible.
xx
xx For example, for a graph with nodes
xx
xx   0 (with edges to 1 and 2),
xx   1 (with no edges),
xx   2 (with edges to each of the nodes), and
xx   3 (with an edge to 1)
xx
xx the program finds a path between nodes 0 and 3:
xx
xx   ACL2 !>(assign g '((0 1 2) (1) (2 0 1 2 3) (3 1)))
xx    ((0 1 2) (1) (2 0 1 2 3) (3 1))
xx   ACL2 !>(linear-find-st 0 3 (@ g) st)
xx   ((0 2 3) <st>)
xx
xx J Moore proved a similar program correct in 1999.  He documented
xx his example in a chapter titled "An Exercise in Graph Theory" in
xx the book "Using the ACL2 Theorem Prover: ACL2 Case Studies",
xx published by Kluwer in 2000.  It is an interesting example of a
xx multiply-recursive program that has been proved correct using ACL2.

xx Matt Wilding reimplemented Moore's program using stobjs to
xx represent the state of the computation.  This optimization avoided
xx datastructure accesses that were not linear time operations.  ACL2
xx was used to verify that the optimized version calculates the same
xx path as the previously-verified version in Moore's paper.  This
xx example is documented in "Using a Single-Threaded Object to Speed a
xx Verified Graph Pathfinder" presented to the 2nd ACL2 Workshop in
xx 2000.

|#

; This example assumes J Moore's linear-find-path proof.
(include-book "graph/linear-find-path")
(set-well-founded-relation e0-ord-<)

(set-verify-guards-eagerness 2)

;; We introduce a version of J's lfns that does not do the irrelevant
;; check.  The irrelevancy of the subset check is something J points
;; out in the comments of his example, and he proves the neccessary
;; lemmas, but he doesn't bother to fix it.  We go ahead and get it
;; out of the way so it doesn't complicate our later proofs

(defthm linear-find-next-step-simpler
  (equal
   (linear-find-next-step c stack b g mt)
   (cond
   ((endp c) (mv 'failure mt))
   ((markedp (car c) mt)
    (linear-find-next-step (cdr c) stack b g mt))
   ((equal (car c) b)
    (mv (rev (cons b stack))
        mt))
   (t (mv-let (temp new-mt)
              (linear-find-next-step (neighbors (car c) g)
                                     (cons (car c) stack)
                                     b g
                                     (mark (car c) mt))
              (cond
               ((eq temp 'failure)
                (linear-find-next-step (cdr c) stack b g new-mt))
               (t (mv temp mt)))))))
  :rule-classes :definition)

(in-theory (disable linear-find-next-step))

;; We introduce a stobj that has many of the datastructures we need to
;; write our version of this program.  There are two operations that
;; we particularly want to optimize: detecting whether a node has been
;; marked, and finding the neighbors of a node.  We implement the
;; datastuctures that are involved in these operations, the graph and
;; the mark list, using stobj arrays.  We also add to the stobj a status
;; bit to indicate failure and success so as to avoid using mv-let.

;; Note that the stack is handled somewhat less efficiently because of
;; its constant-time operations.  We could speed things further by
;; implementing the stack as something other than a list to avoid gc.

;; maximum number of nodes in the graph
(defmacro maxnode () '2500)

;;
(defstobj st
  (g  :type (array list (2500)) :initially nil) ; list of edges
  (marks :type (array (integer 0 1) (2500)) :initially 0) ; visited?
  (stack :type (satisfies true-listp))          ; path
  (status :type (integer 0 1) :initially 0))    ; 0 = success, 1 = failure

;; indicies into datastructure
(defmacro gindex () 0)
(defmacro marksindex () 1)
(defmacro stackindex () 2)
(defmacro statusindex () 3)

;; Some miscellaneous rules that will be useful about st

(defthm <=-cancel
  (equal
   (<= a (+ y b))
   (<= (- a y) b))
  :rule-classes nil)

(defthm <-cancel
  (implies
   (syntaxp (quotep y))
   (equal
    (< (+ y b) a)
    (< b (+ (- a y)))))
  :hints (("goal" :use <=-cancel)))

(defmacro bounded-natp (a max)
  `(and (integerp ,a) (<= 0 ,a) (< ,a ,max)))

(defthm integerp-nth-marksp
  (implies
   (and
    (marksp l)
    (integerp i)
    (<= 0 i)
    (< i (len l)))
   (acl2-numberp (nth i l))))

;; We introduce the notion of the number of unmarked nodes in the
;; graph, which will be used as a measure function to prove
;; termination of our algorithm.

(defun number-unmarked1 (st i)
  (declare (xargs :stobjs st
		  :guard (and (stp st) (bounded-natp i (1+ (maxnode))))
		  :measure (max 0 (nfix (- (maxnode) i)))))
  (if (and (integerp i) (< i (maxnode)))
      (if (= (marksi i st) 1)
	(number-unmarked1 st (1+ i))
	(1+ (number-unmarked1 st (1+ i))))
    0))

(defun number-unmarked (st)
  (declare (xargs :stobjs st
		  :guard (stp st)))
  (number-unmarked1 st 0))

;; Some facts about number-unmarked

(defthm number-unmarked1-update-nth-other
  (implies
   (not (equal j (marksindex)))
   (equal
    (number-unmarked1 (update-nth j v st) i)
    (number-unmarked1 st i))))

(defthm number-unmarked1-above
  (implies
   (and
    (< i k)
    (bounded-natp i (maxnode)))
   (equal
    (number-unmarked1 (list nil (update-nth i 1 l)) k)
    (number-unmarked1 (list nil l) k))))

(defthm number-unmarked1-marked
  (implies
   (and
    (<= k i)
    (bounded-natp i (maxnode))
    (bounded-natp k (maxnode)))
   (equal
    (number-unmarked1 (list nil (update-nth i 1 l)) k)
    (if (equal (nth i l) 1)
	(number-unmarked1 (list nil l) k)
      (1- (number-unmarked1 (list nil l) k))))))

(defthm number-unmarked1-hack
  (equal
   (number-unmarked1 st k)
   (number-unmarked1 (list nil (nth (marksindex) st)) k))
  :rule-classes nil)

(defthm number-unmarked1-update-nth-1-update-nth
  (implies
   (and
    (<= k i)
    (bounded-natp i (maxnode))
    (bounded-natp k (maxnode)))
   (equal
    (number-unmarked1 (update-nth (marksindex) (update-nth i 1 (nth (marksindex) st)) st) k)
    (if (equal (nth i (nth (marksindex) st)) 1)
	(number-unmarked1 st k)
      (1- (number-unmarked1 st k)))))
  :hints (("goal"
	   :use ((:instance number-unmarked1-hack
			    (st (update-nth (marksindex) (update-nth i 1 (nth (marksindex) st)) st)))
		 number-unmarked1-hack))))

(defun measure-st (c st)
  (declare (xargs :stobjs st
		  :guard (stp st)))
  (cons
   (1+ (number-unmarked st))
   (len c)))

(defun numberlistp (l max)
  (declare (xargs :guard (integerp max)))
  (if (consp l)
      (and
       (bounded-natp (car l) max)
       (numberlistp (cdr l) max))
    (equal l nil)))

(defthm true-listp-numberlistp
  (implies
   (numberlistp l n)
   (true-listp l)))

;; A graph is an alist with nodes as keys and edge lists as values
(defun graphp1-st (st i)
  (declare (xargs :stobjs st
		  :measure (max 0 (nfix (- (maxnode) i)))))
  (if (and (bounded-natp i (maxnode)) (stp st))
      (and
       (numberlistp (gi i st) (maxnode))
       (graphp1-st st (1+ i)))
    t))

(defun graphp-st (st)
  (declare (xargs :stobjs st))
  (and
   (stp st)
   (graphp1-st st 0)))

;; We want to use a reverse function.  We might use "rev", but no
;; guard is proved for it.  Since we don't want to modify anything
;; outside this proof, we add our own.

(defun myrev (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (append (myrev (cdr x)) (list (car x)))))

(defthm true-listp-myrev
  (true-listp (myrev l)))

(defthm true-listp-update-nth-rewrite
  (implies
   (true-listp l)
   (true-listp (update-nth i v l))))

(defun repeat (n v)
  (if (and (integerp n) (< 0 n)) (cons v (repeat (1- n) v)) nil))

(defthm len-repeat
  (equal (len (repeat n v)) (nfix n)))

(defthm nlistp-update-nth
  (implies
   (not (consp l))
   (equal (update-nth i v l) (append (repeat i nil) (list v)))))

(defmacro coerce-node (x)
  `(let ((nx (nfix ,x))) (if (<= (maxnode) nx) 0 nx)))

(in-theory (disable update-nth nth))

(in-theory (disable number-unmarked1))

#|
;; Comment from the July, 1999 version of this proof:

xx ;; Finally, the stobj-based algorithm.

xx ;This is a good example of when we wish we could use the guards in
xx ;the logic.  The st argument is guarded with graphp-st, which
xx ;potentially provides us with an important fact needed for the
xx ;termination proof: when marking a previously-unmarked node, we are
xx ;in fact in the mark array's range.  However, guards are not usable
xx ;in a proof about the logic, so we are left to our own devices.
xx ;The most obvious thing to do is to guard the body of the function
xx ;by adding (graphp-st st) to it, but this is obviously very
xx ;inefficient.  My solution is to coerce the pointer to be in range
xx ;before its use: it'll slow down execution a bit, but during proof
xx ;with the assumption of correct type it'll be quickly simplified
xx ;away.

xx ;This problem would be eliminated by the addition of defbody to
xx ;ACL2, as J and Matt have talked about doing.

xx ;; Just as J in his example, we first introduce a version that has
xx ;; an irrelevant check in it that eases the measure proof.  After
xx ;; proving that the check is in fact irrelevant, we add the
xx ;; "real" definition.

xx ;; c is the list of neighbors being explored, b is the goal node

|#

;; Feb 2003 - We have updated this function to exploit MBE, an
;; experimental feature that is expected to be part of ACL2 2.8.  The
;; executable version omits the guards needed to prove termination.
;; When we prove the guards of this function, we will be obliged to
;; prove that, assuming the function arguments meet the assumed
;; guards, the two versions are identical.

(defun linear-find-next-step-st-mbe (c b st)
  (declare (xargs :stobjs st
                  :measure (measure-st c st)
                  :guard (and (graphp-st st)
                              (bounded-natp b (maxnode))
                              (numberlistp c (maxnode)))
                  :verify-guards nil))
  (mbe
   :logic
   (if (endp c) st
     (let ((cur  (coerce-node (car c)))
           (temp (number-unmarked st)))
       (cond
        ((equal (marksi cur st) 1)
         (linear-find-next-step-st-mbe (cdr c) b st))
        ((equal cur b)
         (let ((st (update-status 0 st)))
           (update-stack (myrev (cons (car c) (stack st))) st)))
        (t (let ((st (update-marksi cur 1 st)))
             (let ((st (update-stack (cons (car c) (stack st)) st)))
               (let ((st (linear-find-next-step-st-mbe (gi cur st) b st)))
                 (if (or (<= temp (number-unmarked st)) ; always nil
                         (equal (status st) 0))
                     st
                   (let ((st (update-stack (cdr (stack st)) st)))
                     (linear-find-next-step-st-mbe (cdr c) b st))))))))))
   :exec
    (if (endp c) st
      (cond
       ((equal (marksi (car c) st) 1)
        (linear-find-next-step-st-mbe (cdr c) b st))
       ((equal (car c) b)
        (let ((st (update-status 0 st)))
          (update-stack (myrev (cons b (stack st))) st)))
       (t (let ((st (update-marksi (car c) 1 st)))
            (let ((st (update-stack (cons (car c) (stack st)) st)))
              (let ((st (linear-find-next-step-st-mbe (gi (car c) st) b st)))
                (if (equal (status st) 0)
                    st
                  (let ((st (update-stack (cdr (stack st)) st)))
                    (linear-find-next-step-st-mbe (cdr c) b st)))))))))))

;; We prove a bunch of lemmas needed for the guard proof of lfns-st

(defthm true-listp-linear-find-next-step-st-mbe
  (implies
   (true-listp st)
   (true-listp (linear-find-next-step-st-mbe c b st))))

(defthm number-unmarked-positive
  (<= 0 (number-unmarked st))
  :rule-classes :linear)

(in-theory (disable number-unmarked))

(defthm marksp-append
  (implies
   (true-listp x)
   (equal
    (marksp (append x y))
    (and (marksp x) (marksp y)))))

(defthm marksp-repeat
  (equal
   (marksp (repeat n x))
   (or
    (zp n)
    (bounded-natp x 2))))

(defthm marksp1-update-nth
  (implies
   (and
    (integerp v) (<= 0 v) (<= v 1)
    (<= i (len l))
    (marksp l))
   (marksp (update-nth i v l)))
  :hints (("goal" :in-theory (enable update-nth))))

(defthm nth-0-linear-find-next-step-st-mbe
  (equal
   (nth (gindex) (linear-find-next-step-st-mbe c b st))
   (nth (gindex) st)))

(defthm marksp1-linear-find-next-step-st-mbe
  (implies
   (and
    (marksp (nth (marksindex) st))
    (equal (len (nth (marksindex) st)) (maxnode)))
   (and
    (marksp (nth (marksindex) (linear-find-next-step-st-mbe c b st)))
    (equal (len (nth (marksindex) (linear-find-next-step-st-mbe c b st)))
	   (maxnode)))))

(in-theory (disable len true-listp graphp1-st))

(defthm true-listp-cdr
  (implies
   (true-listp l)
   (true-listp (cdr l))))

(defthm true-listp-stack
  (implies
   (true-listp (nth (stackindex) st))
   (true-listp (nth (stackindex) (linear-find-next-step-st-mbe c b st)))))

(defthm integerp-status
  (implies
   (integerp (nth (statusindex) st))
   (integerp (nth (statusindex) (linear-find-next-step-st-mbe c b st)))))

(defthm status-linear1
  (implies
   (<= 0 (nth (statusindex) st))
   (<= 0 (nth (statusindex) (linear-find-next-step-st-mbe c b st))))
  :rule-classes (:linear :rewrite))

(defthm status-linear2
  (implies
   (not (< 1 (nth (statusindex) st)))
   (not (< 1 (nth (statusindex) (linear-find-next-step-st-mbe c b st)))))
  :rule-classes (:linear :rewrite))

(defthm len-linear-find-next-step-st-mbe
  (implies
   (equal (len st) 4)
   (equal (len (linear-find-next-step-st-mbe c b st)) 4)))

(defthm stp-linear-find-next-step-st-mbe
  (implies
   (stp st)
   (stp (linear-find-next-step-st-mbe c b st))))

(defthm stp-update-nth
  (implies
   (stp st)
   (and
    (equal (stp (update-nth (gindex) v st))
	   (and
	    (gp v)
	    (equal (len v) (maxnode))))
    (equal (stp (update-nth (marksindex) v st))
	   (and
	    (marksp v)
	    (equal (len v) (maxnode))))
    (equal (stp (update-nth (stackindex) v st))
	   (stackp v))
    (equal (stp (update-nth (statusindex) v st))
	   (statusp v)))))

(defthm neighbors-graphp-st
  (implies
   (and
    (graphp1-st st i)
    (<= i j)
    (< j (maxnode))
    (bounded-natp i (maxnode))
    (bounded-natp j (maxnode))
    (stp st))
   (numberlistp (nth j (nth (gindex) st)) (maxnode)))
  :hints (("goal" :in-theory (enable graphp1-st))))

(defthm graphp1-st-update-nth-other
  (implies
   (and
    (graphp1-st st i)
    (stp st)
    (not (equal j 0))
    (bounded-natp j 5))
   (graphp1-st (update-nth j marks st) i))
  :hints (("goal" :in-theory (enable graphp1-st))))

(defthm graphp-st-update-nth-other
  (implies
   (and
    (graphp-st st)
    (stp st)
    (not (equal j 0))
    (bounded-natp j 5))
   (equal
    (graphp-st (update-nth j marks st))
    (stp (update-nth j marks st))))
  :hints (("goal" :in-theory (enable graphp-st))))

(defthm graphp1-st-linear-find-next-step-st-mbe
  (implies
   (and
    (graphp1-st st i)
    (stp st))
   (graphp1-st (linear-find-next-step-st-mbe c b st) i)))

(defthm graphp-st-linear-find-next-step-st-mbe
  (implies
   (graphp-st st)
   (graphp-st (linear-find-next-step-st-mbe c b st))))

(defthm consp-of-truelistp
  (implies
   (true-listp l)
   (iff (consp l) l)))

(defthm len-append
  (equal (len (append x y)) (+ (len x) (len y)))
  :hints (("goal" :in-theory (enable len))))

(defthm len-myrev
  (equal (len (myrev x)) (len x))
  :hints (("goal" :in-theory (enable len))))

(defthm len-stack
  (<= (len (nth (stackindex) st))
      (len (nth (stackindex) (linear-find-next-step-st-mbe c b st))))
  :hints (("Subgoal *1/3.1" :expand (LINEAR-FIND-NEXT-STEP-ST-MBE C 0 ST))
	  ("goal" :in-theory (enable len))))

(defthm len-linear
  (<= 0 (len l))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable len))))

(defthm len-bound-hack
  (equal
   (< 0 (len l))
   (not (equal (len l) 0))))

(defthm equal-len-0
  (equal
   (equal (len l) 0)
   (not (consp l)))
  :hints (("goal" :in-theory (enable len))))

(defthm stack-hack
  (implies
   (and
    (nth (stackindex) st)
    (true-listp (nth (stackindex) st)))
   (nth (stackindex) (linear-find-next-step-st-mbe c b st)))
  :hints (("goal" :use len-stack
	   :in-theory (set-difference-theories (enable len)
					       '(len-stack)))))
(defthm linear-unmarked-not-increased
   (>= (number-unmarked1 st 0)
       (number-unmarked1 (linear-find-next-step-st-mbe c b st) 0))
  :rule-classes :linear)

;; The simpler version of the algorithm is equivalent to the one we
;; just proved.

(defthm linear-find-next-step-st-mbe-simpler
  (implies
   (and
    (graphp-st st)
    (bounded-natp b (maxnode))
    (numberlistp c (maxnode)))
   (equal
    (linear-find-next-step-st-mbe c b st)
    (if (endp c) st
      (cond
       ((equal (marksi (car c) st) 1)
	(linear-find-next-step-st-mbe (cdr c) b st))
       ((equal (car c) b)
	(let ((st (update-status 0 st)))
	  (update-stack (myrev (cons b (stack st))) st)))
       (t (let ((st (update-marksi (car c) 1 st)))
	    (let ((st (update-stack (cons (car c) (stack st)) st)))
	      (let ((st (linear-find-next-step-st-mbe (gi (car c) st) b st)))
		(if (equal (status st) 0)
		    st
		  (let ((st (update-stack (cdr (stack st)) st)))
		    (linear-find-next-step-st-mbe (cdr c) b st)))))))))))
  :hints (("goal" :in-theory (enable number-unmarked)))
  :rule-classes nil)

;; We verify the guards of our program, which includes an obligation
;; to show that the unguarded executable version is identical to the
;; logical version of the definition body.
(verify-guards linear-find-next-step-st-mbe
	       :hints (("goal" :use linear-find-next-step-st-mbe-simpler)))


;; Now we prove that our stobj representation and J's alist
;; representation are equivalence.  "equivalent" means...

(defun graph-equivp1 (alist st i)
  (declare (xargs :measure (max 0 (- (maxnode) (nfix i)))
		  :verify-guards nil
		  :stobjs st))
  (if (< (nfix i) (maxnode))
      (and
       (equal (neighbors i alist) (gi i st))
       (graph-equivp1 alist st (1+ (nfix i))))
    t))

(defun graph-equivp (alist st)
  (declare (xargs :verify-guards nil
		  :stobjs st))
  (graph-equivp1 alist st 0))

(defun mark-equivp1 (list st i)
  (declare (xargs :measure (max 0 (- (maxnode) (nfix i)))
		  :verify-guards nil
		  :stobjs st))
  (if (< (nfix i) (maxnode))
      (and
       (iff (member i list) (equal (marksi i st) 1))
       (mark-equivp1 list st (1+ (nfix i))))
    t))

(defun mark-equivp (list st)
  (declare (xargs :verify-guards nil
		  :stobjs st))
  (mark-equivp1 list st 0))

(defun equiv (stack g mt st)
  (declare (xargs :stobjs st
		  :verify-guards nil))
  (and
   (equal stack (stack st))
   (graph-equivp g st)
   (mark-equivp mt st)))

(in-theory (disable graph-equivp mark-equivp))

(defthm stack-of-failed-search
  (implies
   (not (equal (nth (statusindex) (linear-find-next-step-st-mbe c b st)) 0))
   (equal (nth (stackindex) (linear-find-next-step-st-mbe c b st)) (stack st)))
  :hints (("goal" :in-theory (enable number-unmarked))))

(defthm graph-equivp1-update-nth-other
  (implies
   (not (zp i))
   (equal (graph-equivp1 g (update-nth i v st) j)
	  (graph-equivp1 g st j))))

(defthm graph-equivp-update-nth-other
  (implies
   (not (zp i))
   (equal (graph-equivp g (update-nth i v st))
	  (graph-equivp g st)))
  :hints (("goal" :in-theory (enable graph-equivp))))

(defthm graph-equivp-linear-find-next-step-st-mbe
   (equal (graph-equivp g (linear-find-next-step-st-mbe c b st))
	  (graph-equivp g st))
  :hints (("goal" :in-theory (enable linear-find-next-step-st-mbe))))

(defthm mark-equivp1-update-nth-other
  (implies
   (not (equal i (marksindex)))
   (equal (mark-equivp1 g (update-nth i v st) j)
	  (mark-equivp1 g st j))))

(defthm mark-equivp-update-nth-other
  (implies
   (not (equal i (marksindex)))
   (equal (mark-equivp g (update-nth i v st))
	  (mark-equivp g st)))
  :hints (("goal" :in-theory (enable mark-equivp))))

(set-irrelevant-formals-ok :warn)

;; We need to show ACL2 how to induct on the merged definitions
;; This is pretty tricky due to the multiply recursive nature of
;; the program.

; Because a recursive call of lfns contains a value that is a function
; of another recursive call, the inductive schema definition appears
; in the proof obligations that get generated.  We've arranged for the
; schema definition to compute exactly what the stobj version does so
; that the induction we use is the right one.

(defun induct-equiv (c b st stack g mt)
  (declare (xargs :stobjs st
		  :measure (measure-st c st)
		  :guard (and (graphp-st st)
			      (bounded-natp b (maxnode))
			      (numberlistp c (maxnode)))
		  :verify-guards nil
		  :hints (("goal" :in-theory (enable number-unmarked len)))))
  (if (endp c) st
    (let ((cur (coerce-node (car c)))
	  (temp (number-unmarked st)))  ; note for "irrelevant" check
      (cond
       ((equal (marksi cur st) 1)
	(induct-equiv (cdr c) b st stack g mt))
       ((equal cur b)
	(let ((st (update-status 0 st)))
	  (update-stack (myrev (cons (car c) (stack st))) st)))
       (t (let ((st (update-marksi cur 1 st)))
	    (let ((st (update-stack (cons (car c) (stack st)) st)))
	      (let ((st (induct-equiv (gi cur st) b st (cons (car c) stack)
				      g (cons (car c) mt))))
		(if (or (<= temp (number-unmarked st))  ; always nil
			(equal (status st) 0))
		    st
		  (let ((st (update-stack (cdr (stack st)) st)))
		    (mv-let (temp2 new-mt)
			    (linear-find-next-step (neighbors (car c) g)
						   (cons (car c) stack)
						   b g
						   (mark (car c) mt))
			    (declare (ignore temp2))
			    (induct-equiv (cdr c) b st stack g new-mt))))))))))))

(defthm induct-equiv-is-lfns-st
  (equal
   (induct-equiv c b st stack g mt)
   (linear-find-next-step-st-mbe c b st))
  :hints (("goal" :induct (induct-equiv c b st stack g mt)
	   :in-theory (set-difference-theories
		       (enable induct-equiv linear-find-next-step-st-mbe number-unmarked)
		       '(FIND-NEXT-STEP-AVOIDING-CONS
			 STEP1 REV binary-append step2)))))

(defthm nth-mark-equivp1
  (implies
   (and
    (mark-equivp1 mt st i)
    (bounded-natp i (maxnode))
    (bounded-natp j (maxnode))
    (<= i j))
   (iff
    (equal (nth j (nth (marksindex) st)) 1)
    (member j mt))))

(defthm nth-mark-equivp
  (implies
   (and
    (mark-equivp mt st)
    (bounded-natp j (maxnode)))
   (iff
    (equal (nth j (nth (marksindex) st)) 1)
    (member j mt)))
   :hints (("goal" :in-theory (set-difference-theories (enable mark-equivp)
						       '(mark-equivp1)))))
(defthm mark-equivp1-above1
  (implies
   (and
    (< i j)
    (integerp i)
    (integerp j))
   (equal
    (mark-equivp1 (cons i mt) st j)
    (mark-equivp1 mt st j))))

(defthm mark-equivp1-above2
  (implies
   (and
    (< i j)
    (bounded-natp i (maxnode))
    (integerp j))
   (equal
    (mark-equivp1 mt (update-nth (marksindex) (update-nth i 1 (nth (marksindex) st)) st) j)
    (mark-equivp1 mt st j))))

(defthm mark-equivp1-add
  (implies
   (and
    (mark-equivp1 mt st j)
    (<= j i)
    (bounded-natp j (maxnode))
    (integerp i))
   (mark-equivp1 (cons i mt) (update-nth (marksindex) (update-nth i 1 (nth (marksindex) st)) st) j))
  :hints (("goal" :expand
	   (:free (x)
		  (mark-equivp1 (cons x mt)
				(update-nth (marksindex) (update-nth x 1 (nth (marksindex) st))
					    st)
				x)))))

(defthm mark-equivp-add
  (implies
   (and
    (mark-equivp mt st)
    (integerp i)
    (<= 0 i))
   (mark-equivp (cons i mt) (update-nth (marksindex) (update-nth i 1 (nth (marksindex) st)) st)))
   :hints (("goal" :in-theory (set-difference-theories (enable mark-equivp)
						       '(mark-equivp1)))))
(defthm nth-graph-equivp1
  (implies
   (and
    (graph-equivp1 g st i)
    (bounded-natp i (maxnode))
    (bounded-natp j (maxnode))
    (<= i j))
   (equal
    (neighbors j g)
    (gi j st))))

(defthm nth-graph-equivp
  (implies
   (and
    (graph-equivp g st)
    (bounded-natp j (maxnode)))
   (equal
    (neighbors j g)
    (gi j st)))
  :hints (("goal" :in-theory (enable graph-equivp))))

(defthm graphp-st-means-stp
  (implies
   (graphp-st st)
   (stp st))
  :rule-classes :forward-chaining)

(defthm true-listp-cons
  (equal
   (true-listp (cons a b))
   (true-listp b))
  :hints (("goal" :in-theory (enable true-listp))))

(defthm myrev-is-rev
  (equal (myrev x) (rev x)))

;;; The stobj implementation of lfp works just like the original
;;; list-based one.

(defthm implementations-same
  (implies
   (and
    (equiv stack g mt st)
    (graphp-st st)
    (not (equal (status st) 0))
    (numberlistp c (maxnode))
    (numberlistp stack (maxnode))
    (bounded-natp b (maxnode)))
   (let ((st (linear-find-next-step-st-mbe c b st)))
     (mv-let (temp marks) (linear-find-next-step c stack b g mt)
	      (or
	       (and (not (equal (status st) 0)) (equal temp 'failure) (mark-equivp marks st))
	       (and (equal (status st) 0) (not (equal temp 'failure)) (equal temp (stack st)))))))
  :hints (("goal" :in-theory (enable linear-find-next-step-st-mbe linear-find-next-step
				     number-unmarked)
	   :induct (induct-equiv c b st stack g mt)))
  :rule-classes nil)