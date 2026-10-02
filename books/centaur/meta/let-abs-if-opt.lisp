; Centaur Meta-reasoning Library
; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
; SPDX-License-Identifier: BSD-3-Clause
; 
; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holder nor the names of
;   its contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Author: Sol Swords <sol.swords@arm.com>

(in-package "CMR")

(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "bindinglist")
(include-book "clause-processors/generalize" :dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(include-book "substitute")
(include-book "std/stobjs/1d-arr" :dir :system)
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "clause-processors/join-thms" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
;; (local (include-book "std/alists/alist-equiv" :dir :system))

(local (in-theory (disable pseudo-termp pseudo-term-listp
                           nth update-nth (tau-system))))
(local (std::add-default-post-define-hook :fix))



;; Let-abstraction "optimizing" ifs.
;; Suppose we have a lambda-free term, fully beta-reduced.
;; We want to let-abstract so that:
;;  (goal 1): each function call is computed under the maximally specific set of IF tests.
;;  (goal 2): each function call is computed the minimal number of times possible
;; These two goals can be in conflict: e.g., suppose we have
;; (list (if A (foo x) y)
;;       (if B (foo x) z))
;; To satisfy goal 2, we should bind (foo x) to a variable outside of both
;; IFs. However, this violates goal 1 since now (foo x) is computed even in
;; cases where A and B are both false.

;; We prioritize goal 1 over goal 2 because goal 1 is relevant, in a couple of
;; ways, to function as well as performance, whereas goal 2 is only relevant to
;; performance.
;;  - Guards: If the guard of (foo x) is satisfied whenever A or B is true, but
;;    otherwise perhaps not, then binding (foo x) outside of the IFs introduces
;;    a guard violation.
;;  - Conditional rewrite rules: If there are conditional rules for rewriting
;;    (foo x) whenever A or B holds but otherwise not, then binding (foo x)
;;    outside the IFs introduces an occurrence that is less likely to be
;;    rewritten to the desired normal form.

;; Can we define a reasonably simple recursive algorithm that satisfies goal 1
;; always and goal 2 when it doesn't conflict with goal 1?

;; Both goals can be accomplished for execution purposes by departing from a
;; simple term representation with LETs and using memoization on a DAG.  I.e.,
;; when evaluating a function call, check to see if the same call has been
;; evaluated already and reuse its value if so, otherwise evaluate its
;; arguments, evaluate the function, and store the result of the evaluation. On
;; an IF, first evaluate the test, then only evaluate the branch that is
;; required.

;; While this is optimal for execution, it's not optimal for rewriting/symbolic
;; simulation.  E.g., when evaluating (list (if A (foo x) y) (foo x)), we
;; should symbolically simulate (foo x) first and use its result when we
;; encounter it both on the if branch and on the second argument of the
;; list. Instead, we would first encounter (foo x) on the if branch and rewrite
;; it under assumption A, then encounter it again outside the IF. At this point
;; we have a stored value for (foo x) if A holds, so we rewrite something like
;; (if A stored-value (foo x)), which means we need to rewrite (foo x) a second
;; time under the opposite assumption. So we need to be more strategic in order
;; to optimize for rewriting.


;; We've landed on the following strategy. Below, we keep notes on how we
;; finally got there.

;; We process a lambda-free term into a DAG consisting of constant, variable,
;; and function call nodes. Then we record optimization information for each IF
;; in ascending topological order, which will let us define an evaluation order
;; for the DAG which satisfies the two goals.

;; Let the set of nodes unconditionally reachable from a node be those that can
;; be reached by traversing any edges but IF branches (then/else pointers).

;; Record for each IF the set of nodes that are:
;;  - unconditionally reachable from both branches of the IF
;;  - not unconditionally reachable from any other such node.
;; Such nodes are to be evaluated before descending into either IF branch. They
;; are also considered reachable from the IF without traversing a branch, for
;; purposes of computing the same information for subsequent IFs.


;; To evaluate (or symbolically simulate) such a DAG in a way that satisfies
;; the two goals:

;; Let EvaluatedNodes map nodes to values, starting out empty.
;; Define the procedure EvalTop(node, EvaluatedNodes):
;;    Collect the nodes unconditionally reachable from node without traversing any mapped in EvaluatedNodes.
;;    Topologically sort this list. For each node' in the list, run EvaluatedNodes := Eval(node', EvaluatedNodes).
;;    Return EvaluatedNodes[node].
;; Define Eval(node, EvaluatedNodes):
;;    Compute value as follows:
;;      - if node is a constant, the constant value
;;      - if node is a variable, the variable's assigned value
;;      - if node is a function call, the function applied to the values stored in EvaluatedNodes for its arguments
;;           (note: since we proceed in topological order, these are all bound)
;;      - if node is an IF, let testvalue be the value stored in EvaluatedNodes for the test (must be bound)
;;           then for each branch that needs to be evaluated accordingly, run branchval := EvalTop(branch, EvaluatedNodes);
;;           value is then if(testval, thenval, elseval).
;;   Return ( node : value ) :: EvaluatedNodes.
;; Note that EvaluatedNodes is updated by Eval but not by EvalTop, which only
;; returns the value. Thus node values computed under a particular IF condition
;; aren't saved outside of that IF branch.




;; Background/derivation of this scheme:

;; Assume we have a data structure representing our terms which is essentially
;; a DAG with sub-DAGs inside if branches. To evaluate a DAG, every node
;; of the DAG (each representing a function call) will be evaluated, in some
;; topological order.  However, we also have special IF nodes where the test is
;; a normal pointer to another dag node, but the then and else branches are
;; sub-DAGs. The sub-DAGs may reference nodes of the outer DAG, but neither the
;; outer DAG nor another sub-DAG may reference nodes of a sub-DAG. To evaluate
;; an IF, the test is evaluated as a normal DAG dependency, then the sub-DAG
;; indicated by the test is recursively evaluated (including any outer DAG
;; nodes it points to). This allows us to maintain the distinction between
;; function calls inside and outside IF branches: when evaluating the DAG, any
;; node of the outer DAG will be evaluated unconditionally, but any node within
;; a sub-DAG will only be evaluated if the guarding IF test comes out the right
;; way.

;; A slightly different representation for this basic idea: suppose we have a
;; flat DAG and IF nodes with test, then, and else pointers, but additionally a
;; list of "externals".  The sub-DAGs beginning at THEN and ELSE are local to
;; the given branch but that ends when a node in the list of externals is
;; reached. To evaluate the IF, the test and externals are first both evaluated
;; unconditionally, then the THEN or ELSE depending on the result from the
;; test.

;; Suppose we start with a flat DAG where IF nodes have no externals. Traverse
;; inside out. At each IF node, mark the intersection frontier of the two
;; branches and add all such nodes to the IF's externals. Additionally, we
;; enforce the following rule at the top level of the term and at any IF branch:

;;  - Let the unconditionally reachable set at node x be those reachable from x
;; without traversing IF nodes' then and else branches.

;;  - For any IF node unconditionally reachable from node x, the intersection
;; frontier of the THEN node and the unconditionally reachable nodes of x is a
;; subset of the externals, and likewise for the ELSE node.

;; Note since this rule only adds nodes to the externals that are already
;; unconditionally reachable, this doesn't require a fixpoint operation, just a
;; single pass over all IF nodes in the unconditionally reachable set once the
;; unconditionally reachable set is determined.

;; Note also that the externals always represent acyclic edges; all externals
;; of an IF are reachable from either the THEN or ELSE nodes.

;; This seems nice and elegant except that a given IF node might be pointed to
;; by multiple outer IF nests, and might therefore need to have different sets
;; of externals for different contexts. A refinement: Have "externals" (maybe a
;; better name is "pre-evals") for each IF as a whole as well as for each
;; branch of each IF.  For the IF as a whole, this will be the intersection
;; frontier between the two branches.  For the branches, these will be the
;; intersection frontier of the unconditionally reachable nodes of the branch
;; with the branches reachable from the branch.  These are all local properties
;; not dependent on context.

;; Actually, though, recording the "pre-evals" for the branches of each IF can
;; be avoided by ordering the evaluation of the reachable nodes. Suppose when
;; we enter an IF branch, we first sort all the unconditionally reachable nodes
;; and evaluate them in order.  Then by the time we reach any IF, all
;; unconditionally reachable nodes that might be reached by either of the
;; branches have already been evaluated.  Therefore we can get away with just
;; recording the intersection frontier between the two branches as pre-evals
;; for each IF.



(fty::deftagsum ifopt-node
  (:quote (val))
  (:var   ((name pseudo-var-p)))
  (:fncall ((fn pseudo-fnsym-p) (args nat-listp)))
  (:if ((test natp) (then natp) (else natp)
        (pre-evals nat-listp)))
  :layout :list)



(make-event
 (let ((default (ifopt-node-quote nil)))
   `(stobjs::def-1d-arr ifoptdag
      :slotname ifopt-node
      :pred ifopt-node-p
      :fix ifopt-node-fix
      :default-val ,default)))

(define nat-list-boundedp ((n natp) (x nat-listp))
  (if (atom x)
      t
    (and (< (lnfix (car x)) (lnfix n))
         (nat-list-boundedp n (cdr x))))
  ///
  (defthmd nat-list-boundedp-monotonic
    (implies (and (nat-list-boundedp n x)
                  (<= (nfix n) (nfix m)))
             (nat-list-boundedp m x)))
  (defthm nat-list-boundedp-nil
    (nat-list-boundedp next nil)))

             
(define nat-list-max ((x nat-listp))
  :returns (max integerp)
  (if (atom x)
      -1
    (max (nfix (car x))
         (nat-list-max (cdr x))))
  ///
  (defretd nat-list-max-when-nat-list-boundedp
    (implies (nat-list-boundedp n x)
             (< (nat-list-max x) (nfix n)))
    :hints(("Goal" :in-theory (enable nat-list-boundedp)))
    :rule-classes :linear)

  (defret <fn>-lower-bound
    (<= -1 max)
    :rule-classes :linear))

(define ifopt-node-boundedp ((n natp) (x ifopt-node-p))
  (b* ((n (lnfix n)))
    (ifopt-node-case x
      (:fncall (nat-list-boundedp n x.args))
      (:if (and (< x.test n)
                (< x.then n)
                (< x.else n)
                (nat-list-boundedp n x.pre-evals)))
      (:otherwise t)))
  ///
  (defthmd ifopt-node-boundedp-monotonic
    (implies (and (ifopt-node-boundedp n x)
                  (<= (nfix n) (nfix m)))
             (ifopt-node-boundedp m x))
    :hints(("Goal" :in-theory (enable nat-list-boundedp-monotonic))))

  (defthm ifopt-node-boundedp-of-default
    (ifopt-node-boundedp n '(:quote nil))))

(define ifopt-node-max ((x ifopt-node-p))
  :returns (max integerp)
  (ifopt-node-case x
    (:fncall (nat-list-max x.args))
    (:if (max x.test
              (max x.then
                   (max x.else
                        (nat-list-max x.pre-evals)))))
    (:otherwise -1))
  ///
  (defret <fn>-lower-bound
    (<= -1 max)
    :rule-classes :linear))

(define ifoptdag-orderedp-aux ((n natp) ifoptdag)
  :measure (nfix (- (ifopt-nodes-length ifoptdag) (nfix n)))
  :returns (ok)
  (b* (((when (mbe :logic (zp (- (ifopt-nodes-length ifoptdag) (nfix n)))
                   :exec (<= (ifopt-nodes-length ifoptdag) n)))
        t))
    (and (< (ifopt-node-max (get-ifopt-node n ifoptdag)) (lnfix n))
         (ifoptdag-orderedp-aux (1+ (lnfix n)) ifoptdag)))
  ///
  (defretd <fn>-implies
    (implies (and ok
                  (<= (nfix n) (nfix k)))
             (< (ifopt-node-max (nth k ifoptdag)) (nfix k)))
    :hints(("Goal" :in-theory (acl2::enable* acl2::arith-equiv-forwarding)
            :induct t))
    :rule-classes :linear)

  (defret <fn>-of-resize
    (implies (ifoptdag-orderedp-aux n ifoptdag)
             (ifoptdag-orderedp-aux n (resize-list ifoptdag size '(:quote nil)))))

  (defret <fn>-of-update-nth
    (implies (and (ifoptdag-orderedp-aux n ifoptdag)
                  (< (ifopt-node-max node) (nfix m)))
             (ifoptdag-orderedp-aux n (update-nth m node ifoptdag)))
    :hints(("Goal" :in-theory (acl2::enable* acl2::arith-equiv-forwarding)))))

(define ifoptdag-orderedp (ifoptdag)
  :returns (ok)
  (ifoptdag-orderedp-aux 0 ifoptdag)
  ///
  (defret <fn>-implies
    (implies ok
             (< (ifopt-node-max (nth k ifoptdag)) (nfix k)))
    :hints (("goal" :use ((:instance ifoptdag-orderedp-aux-implies
                           (n 0)))
             :in-theory (enable ifopt-node-boundedp-monotonic)))
    :rule-classes :linear)

  (defret <fn>-of-resize
    (implies (ifoptdag-orderedp ifoptdag)
             (ifoptdag-orderedp (resize-list ifoptdag size '(:quote nil)))))

  (defret <fn>-of-update-nth
    (implies (and (ifoptdag-orderedp ifoptdag)
                  (< (ifopt-node-max node) (nfix m)))
             (ifoptdag-orderedp (update-nth m node ifoptdag))))

  (defret nat-list-boundedp-args-when-<fn>
    (implies (and ok
                  (ifopt-node-case (nth k ifoptdag) :fncall))
             (< (nat-list-max (ifopt-node-fncall->args (nth k ifoptdag))) (nfix k)))
    :hints(("Goal" :use ((:instance <fn>-implies))
            :in-theory (e/d (ifopt-node-max)
                            (<fn>-implies <fn>))))
    :rule-classes :linear)

  (defret if-arg-bounds-when-<fn>
    (implies (and ok
                  (ifopt-node-case (nth k ifoptdag) :if))
             (and (< (ifopt-node-if->test (nth k ifoptdag)) (nfix k))
                  (< (ifopt-node-if->then (nth k ifoptdag)) (nfix k))
                  (< (ifopt-node-if->else (nth k ifoptdag)) (nfix k))))
    :hints(("Goal" :use ((:instance <fn>-implies))
            :in-theory (e/d (ifopt-node-max)
                            (<fn>-implies <fn>))))
    :rule-classes :linear)

  (defret if-pre-eval-bounds-when-<fn>
    (implies (and ok
                  (ifopt-node-case (nth k ifoptdag) :if))
             (< (nat-list-max (ifopt-node-if->pre-evals (nth k ifoptdag))) (nfix k)))
    :hints(("Goal" :use ((:instance <fn>-implies))
            :in-theory (e/d (ifopt-node-max)
                            (<fn>-implies <fn>))))
    :rule-classes :linear))


(defines ifoptdag-to-term
  :ruler-extenders (cons :lambdas)
  :flag-local nil
  (define ifoptdag-to-term ((n natp)
                            (ifoptdag))
    :guard (and (< n (ifopt-nodes-length ifoptdag))
                (ifoptdag-orderedp ifoptdag))
    :well-founded-relation acl2::nat-list-<
    :measure (list n 2 0)
    :hints(("Goal" :expand ((nat-list-max args)
                            (ifopt-node-max node))))
    :returns (res pseudo-termp)
    :verify-guards nil
    (b* ((node (get-ifopt-node n ifoptdag)))
      (if (mbt (< (ifopt-node-max node) (lnfix n)))
          (ifopt-node-to-term node ifoptdag)
        (pseudo-term-quote nil))))
  
  (define ifopt-node-to-term ((node ifopt-node-p) ifoptdag)
    :guard (and (< (ifopt-node-max node) (ifopt-nodes-length ifoptdag))
                (ifoptdag-orderedp ifoptdag))
    :measure (list (+ 1 (ifopt-node-max node)) 1 0)
    :returns (res pseudo-termp)
    (ifopt-node-case node
        :quote (pseudo-term-quote node.val)
        :var (pseudo-term-var node.name)
        :fncall (b* ((args (ifoptdag-to-termlist node.args ifoptdag)))
                  (pseudo-term-call node.fn args))
        :if (b* ((test (ifoptdag-to-term node.test ifoptdag))
                 (then (ifoptdag-to-term node.then ifoptdag))
                 (else (ifoptdag-to-term node.else ifoptdag)))
              (pseudo-term-call 'if (list test then else)))))
                 
  (define ifoptdag-to-termlist ((args nat-listp)
                                (ifoptdag))
    :guard (and (< (nat-list-max args) (ifopt-nodes-length ifoptdag))
                (ifoptdag-orderedp ifoptdag))
    :returns (res pseudo-term-listp)
    :measure (list (+ 1 (nat-list-max args)) 0 (+ 1 (len args)))
    (if (atom args)
        nil
      (cons (ifoptdag-to-term (car args) ifoptdag)
            (ifoptdag-to-termlist (cdr args) ifoptdag))))
  ///
  (verify-guards ifoptdag-to-term
    :hints(("Goal" :expand ((nat-list-max args)
                            (ifopt-node-max node)))))

  (fty::deffixequiv-mutual ifoptdag-to-term)

  (std::defret-mutual ifoptdag-to-term-of-update-greater
    (defret <fn>-of-update-greater
      (implies (< (nfix n) (nfix k))
               (equal (let ((ifoptdag (update-nth k newnode ifoptdag))) <call>)
                      res))
      :hints ('(:expand ((:free (ifoptdag) <call>))))
      :fn ifoptdag-to-term)
    (defret <fn>-of-update-greater
      (implies (< (ifopt-node-max node) (nfix k))
               (equal (let ((ifoptdag (update-nth k newnode ifoptdag))) <call>)
                      res))
      :hints ('(:expand ((:free (ifoptdag) <call>)
                         (ifopt-node-max node))))
      :fn ifopt-node-to-term)
    (defret <fn>-of-update-greater
      (implies (< (nat-list-max args) (nfix k))
               (equal (let ((ifoptdag (update-nth k newnode ifoptdag))) <call>)
                      res))
      :hints ('(:expand ((:free (ifoptdag) <call>)
                         (nat-list-max args))))
      :fn ifoptdag-to-termlist))

  (std::defret-mutual ifoptdag-to-term-of-resize
    (defret <fn>-of-resize
      (implies (<= (len ifoptdag) (nfix k))
               (equal (let ((ifoptdag (resize-list ifoptdag k '(:quote nil)))) <call>)
                      res))
      :hints ('(:expand ((:free (ifoptdag) <call>))))
      :fn ifoptdag-to-term)
    (defret <fn>-of-resize
      (implies (<= (len ifoptdag) (nfix k))
               (equal (let ((ifoptdag (resize-list ifoptdag k '(:quote nil)))) <call>)
                      res))
      :hints ('(:expand ((:free (ifoptdag) <call>))))
      :fn ifopt-node-to-term)
    (defret <fn>-of-resize
      (implies (<= (len ifoptdag) (nfix k))
               (equal (let ((ifoptdag (resize-list ifoptdag k '(:quote nil)))) <call>)
                      res))
      :hints ('(:expand ((:free (ifoptdag) <call>))))
      :fn ifoptdag-to-termlist)))
                   
         





(fty::defmap ifoptdag-memo :key-type pseudo-term :val-type natp :true-listp t)

(define ifoptdag-memo-boundedp ((n natp) (x ifoptdag-memo-p))
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (pseudo-termp (caar x)))))
             (< (lnfix (cdar x)) (lnfix n)))
         (ifoptdag-memo-boundedp n (cdr x))))
  ///
  (defthmd ifoptdag-memo-boundedp-implies-lookup
    (implies (and (ifoptdag-memo-boundedp n x)
                  (<= (nfix n) (nfix m))
                  (pseudo-termp k)
                  (hons-assoc-equal k x))
             (< (nfix (cdr (hons-assoc-equal k x))) (nfix m))))

  (defthmd ifoptdag-memo-boundedp-implies-lookup-no-fix
    (implies (and (ifoptdag-memo-boundedp n x)
                  (<= (nfix n) (nfix m))
                  (pseudo-termp k)
                  (natp (cdr (hons-assoc-equal k x))))
             (< (cdr (hons-assoc-equal k x)) (nfix m))))

  (defthmd ifoptdag-memo-boundedp-monotonic
    (implies (and (ifoptdag-memo-boundedp n x)
                  (<= (nfix n) (nfix m)))
             (ifoptdag-memo-boundedp m x)))

  (local (in-theory (enable ifoptdag-memo-fix))))
                  



(fty::defmap ifoptdag-hash :key-type ifopt-node :val-type natp :true-listp t)

(define ifoptdag-hash-boundedp ((n natp) (x ifoptdag-hash-p))
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (ifopt-node-p (caar x)))))
             (< (lnfix (cdar x)) (lnfix n)))
         (ifoptdag-hash-boundedp n (cdr x))))
  ///
  (defthmd ifoptdag-hash-boundedp-implies-lookup
    (implies (and (ifoptdag-hash-boundedp n x)
                  (<= (nfix n) (nfix m))
                  (ifopt-node-p k)
                  (hons-assoc-equal k x))
             (< (nfix (cdr (hons-assoc-equal k x))) (nfix m))))

  (defthmd ifoptdag-hash-boundedp-implies-lookup-no-fix
    (implies (and (ifoptdag-hash-boundedp n x)
                  (<= (nfix n) (nfix m))
                  (ifopt-node-p k)
                  (natp (cdr (hons-assoc-equal k x))))
             (< (cdr (hons-assoc-equal k x)) (nfix m))))

  (defthmd ifoptdag-hash-boundedp-monotonic
    (implies (and (ifoptdag-hash-boundedp n x)
                  (<= (nfix n) (nfix m)))
             (ifoptdag-hash-boundedp m x)))

  (local (in-theory (enable ifoptdag-hash-fix))))

(define ifoptdag-hash-correct ((x ifoptdag-hash-p)
                               ifoptdag)
  :guard (ifoptdag-hash-boundedp (ifopt-nodes-length ifoptdag) x)
  :guard-hints (("goal" :in-theory (enable ifoptdag-hash-boundedp)))
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (ifopt-node-p (caar x)))))
             (equal (caar x) (get-ifopt-node (cdar x) ifoptdag)))
         (ifoptdag-hash-correct (cdr x) ifoptdag)))
  ///
  (defthmd lookup-when-ifoptdag-hash-correct
    (implies (and (ifoptdag-hash-correct x ifoptdag)
                  (hons-assoc-equal k x)
                  (ifopt-node-p k))
             (ifopt-node-equiv (nth (cdr (hons-assoc-equal k x)) ifoptdag)
                               k)))

  (defthm ifoptdag-hash-correct-of-acons
    (implies (and (ifoptdag-hash-correct x ifoptdag)
                  (equal (ifopt-node-fix (nth n ifoptdag)) node))
             (ifoptdag-hash-correct (cons (cons node n) x) ifoptdag)))

  (defthm ifoptdag-hash-correct-of-update-greater
    (implies (and (ifoptdag-hash-boundedp bound x)
                  (ifoptdag-hash-correct x ifoptdag)
                  (<= (nfix bound) (nfix n)))
             (ifoptdag-hash-correct x (update-nth n v ifoptdag)))
    :hints(("Goal" :in-theory (enable ifoptdag-hash-boundedp))))

  (defthm ifoptdag-hash-correct-of-resize
    (implies (and (ifoptdag-hash-correct x ifoptdag)
                  (<= (len ifoptdag) (nfix n)))
             (ifoptdag-hash-correct x (resize-list ifoptdag n '(:quote nil))))
    :hints(("Goal" :in-theory (enable ifoptdag-hash-boundedp)
            :induct (len x))))
  
  (local (in-theory (enable ifoptdag-hash-fix))))
                  

;; (fty::defmap ifoptdag-subst :key-type pseudo-var :val-type natp :true-listp t)

;; (define ifoptdag-subst-boundedp ((n natp) (x ifoptdag-subst-p))
;;   (if (atom x)
;;       t
;;     (and (or (not (mbt (and (consp (car x))
;;                             (pseudo-var-p (caar x)))))
;;              (< (lnfix (cdar x)) (lnfix n)))
;;          (ifoptdag-subst-boundedp n (cdr x))))
;;   ///
;;   (defthmd ifoptdag-subst-boundedp-implies-lookup
;;     (implies (and (ifoptdag-subst-boundedp n x)
;;                   (<= (nfix n) (nfix m))
;;                   (pseudo-var-p k)
;;                   (hons-assoc-equal k x))
;;              (< (nfix (cdr (hons-assoc-equal k x))) (nfix m))))

;;   (defthmd ifoptdag-subst-boundedp-monotonic
;;     (implies (and (ifoptdag-subst-boundedp n x)
;;                   (<= (nfix n) (nfix m)))
;;              (ifoptdag-subst-boundedp m x)))

;;   (local (in-theory (enable ifoptdag-subst-fix))))

(define ifopt-node-quoteh (val)
  :enabled t
  (hons-copy (ifopt-node-quote val))
  ///
  (memoize 'ifopt-node-quoteh))

(define ifopt-node-varh ((name pseudo-var-p))
  :enabled t
  (hons-copy (ifopt-node-var name))
  ///
  (memoize 'ifopt-node-varh))

(define ifopt-node-fncallh ((fn pseudo-fnsym-p)
                            (args nat-listp))
  :enabled t
  (hons-copy (ifopt-node-fncall fn args)))

(local (defthm assoc-is-hons-assoc
         (implies k
                  (equal (assoc-equal k a)
                         (hons-assoc-equal k a)))))

;; (local (defthm hons-assoc-of-append
;;          (equal (hons-assoc-equal k (append x y))
;;                 (or (hons-assoc-equal k x)
;;                     (hons-assoc-equal k y)))))

(local (defthm hons-assoc-equal-of-base-ev-alist
         (equal (hons-assoc-equal k (base-ev-alist subst a))
                (let ((look (hons-assoc-equal k (pseudo-term-subst-fix subst))))
                  (and look
                       (cons k (base-ev (cdr look) a)))))
         :hints(("Goal" :in-theory (enable base-ev-alist
                                           pseudo-term-subst-fix)))))


(local (defthm base-ev-alist-of-pair-vars
         (equal (base-ev-alist (pair-vars vars vals) env)
                (pair-vars vars (base-ev-list vals env)))
         :hints(("Goal" :in-theory (enable base-ev-alist pair-vars)))))

(defines lambda-free-term-p
  (define lambda-free-term-p ((x pseudo-termp))
    :measure (pseudo-term-count x)
    (pseudo-term-case x
      :const t
      :var t
      :lambda nil
      :fncall (lambda-free-termlist-p x.args)))
  (define lambda-free-termlist-p ((x pseudo-term-listp))
    :measure (pseudo-term-list-count x)
    (if (atom x)
        t
      (and (lambda-free-term-p (car x))
           (lambda-free-termlist-p (cdr x)))))
  ///
  (memoize 'lambda-free-term-p)
  (deffixequiv-mutual lambda-free-term-p))

(define lambda-free-term-subst-p ((x pseudo-term-subst-p))
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (pseudo-var-p (caar x)))))
             (lambda-free-term-p (cdar x)))
         (lambda-free-term-subst-p (cdr x))))
  ///
  (defthm lookup-when-lambda-free-term-subst-p
    (implies (and (lambda-free-term-subst-p x)
                  (pseudo-var-p k))
             (lambda-free-term-p (cdr (hons-assoc-equal k x)))))

  (defthm lambda-free-term-subst-p-of-pair-vars
    (implies (lambda-free-termlist-p vals)
             (lambda-free-term-subst-p (pair-vars vars vals)))
    :hints(("Goal" :in-theory (enable pair-vars lambda-free-termlist-p))))
  
  (local (in-theory (enable pseudo-term-subst-fix))))




(defines beta-reduce-term
  (define beta-reduce-term ((x pseudo-termp)
                            (subst pseudo-term-subst-p))
    :measure (pseudo-term-count x)
    :returns (new-x pseudo-termp)
    :verify-guards nil
    (pseudo-term-case x
      :const (pseudo-term-fix x)
      :var (b* ((look (hons-assoc-equal x.name (pseudo-term-subst-fix subst))))
             (if look (cdr look) (pseudo-term-quote nil)))
      :lambda (b* ((args (beta-reduce-termlist x.args subst))
                   (new-subst (pair-vars x.formals args)))
                (beta-reduce-term x.body new-subst))
      :fncall (b* ((args (beta-reduce-termlist x.args subst)))
                (pseudo-term-fncall x.fn args))))

  (define beta-reduce-termlist ((x pseudo-term-listp)
                                (subst pseudo-term-subst-p))
    :measure (pseudo-term-list-count x)
    :returns (new-x (and (pseudo-term-listp new-x)
                         (equal (len new-x) (len x))))
    (if (atom x)
        nil
      (cons (beta-reduce-term (car x) subst)
            (beta-reduce-termlist (cdr x) subst))))
  ///
  ;; (local (defthm pseudo-term-subst-p-of-pairlis
  ;;          (implies (and (symbol-listp 
  
  (verify-guards beta-reduce-term)

  (local (defthm base-ev-alist-of-pair-vars
           (equal (base-ev-alist (pair-vars vars vals) env)
                  (pair-vars vars (base-ev-list vals env)))
           :hints(("Goal" :in-theory (enable base-ev-alist pair-vars)))))
  
  (std::defret-mutual eval-of-<fn>
    (defret eval-of-<fn>
      (equal (base-ev new-x a)
             (base-ev x (base-ev-alist subst a)))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable acl2::base-ev-of-fncall-args))))
      :fn beta-reduce-term)
    (defret eval-of-<fn>
      (equal (base-ev-list new-x a)
             (base-ev-list x (base-ev-alist subst a)))
      :hints ('(:expand (<call>)))
      :fn beta-reduce-termlist))

  (std::defret-mutual lambda-free-term-p-of-<fn>
    (defret lambda-free-term-p-of-<fn>
      (implies (lambda-free-term-subst-p subst)
               (lambda-free-term-p new-x))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   `(:expand (,(car (last clause))))))
      :fn beta-reduce-term)
    (defret lambda-free-termlist-p-of-<fn>
      (implies (lambda-free-term-subst-p subst)
               (lambda-free-termlist-p new-x))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   `(:expand (,(car (last clause))))))
      :fn beta-reduce-termlist)))

(defines beta-reduce-term-top
   (define beta-reduce-term-top ((x pseudo-termp))
    :measure (pseudo-term-count x)
    :returns (new-x pseudo-termp)
    :verify-guards nil
    (pseudo-term-case x
      :const (pseudo-term-fix x)
      :var (pseudo-term-fix x)
      :lambda (b* ((args (beta-reduce-termlist-top x.args))
                   (new-subst (pair-vars x.formals args)))
                (beta-reduce-term x.body new-subst))
      :fncall (b* ((args (beta-reduce-termlist-top x.args)))
                (pseudo-term-fncall x.fn args))))

  (define beta-reduce-termlist-top ((x pseudo-term-listp))
    :measure (pseudo-term-list-count x)
    :returns (new-x (and (pseudo-term-listp new-x)
                         (equal (len new-x) (len x))))
    (if (atom x)
        nil
      (cons (beta-reduce-term-top (car x))
            (beta-reduce-termlist-top (cdr x)))))
  ///
  ;; (local (defthm pseudo-term-subst-p-of-pairlis
  ;;          (implies (and (symbol-listp 
  
  (verify-guards beta-reduce-term-top)
  
  (std::defret-mutual eval-of-<fn>
    (defret eval-of-<fn>
      (equal (base-ev new-x a)
             (base-ev x a))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable acl2::base-ev-of-fncall-args))))
      :fn beta-reduce-term-top)
    (defret eval-of-<fn>
      (equal (base-ev-list new-x a)
             (base-ev-list x a))
      :hints ('(:expand (<call>)))
      :fn beta-reduce-termlist-top))

  (std::defret-mutual lambda-free-term-p-of-<fn>
    (defret lambda-free-term-p-of-<fn>
      (lambda-free-term-p new-x)
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   `(:expand (,(car (last clause))))))
      :fn beta-reduce-term-top)
    (defret lambda-free-termlist-p-of-<fn>
      (lambda-free-termlist-p new-x)
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   `(:expand (,(car (last clause))))))
      :fn beta-reduce-termlist-top)))

(define ifoptdag-base-ev-memo-correct ((x ifoptdag-memo-p) ifoptdag a)
  :verify-guards nil
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (Car x))
                            (pseudo-termp (caar x)))))
             (equal (base-ev (caar x) a)
                    (base-ev (ifoptdag-to-term (cdar x) ifoptdag) a)))
         (ifoptdag-base-ev-memo-correct (cdr x) ifoptdag a)))
  ///
  (defthm ifoptdag-base-ev-memo-correct-implies-lookup
    (implies (and (ifoptdag-base-ev-memo-correct x ifoptdag a)
                  (hons-assoc-equal k x)
                  (pseudo-termp k))
             (equal (base-ev (ifoptdag-to-term (cdr (hons-assoc-equal k x)) ifoptdag) a)
                    (base-ev k a))))

  (defthm ifoptdag-base-ev-memo-correct-of-acons
    (implies (and (ifoptdag-base-ev-memo-correct x ifoptdag a)
                  (equal (base-ev (ifoptdag-to-term i ifoptdag) a) (base-ev k a)))
             (ifoptdag-base-ev-memo-correct (cons (cons k i) x) ifoptdag a)))

  (defthm ifoptdag-base-ev-memo-correct-of-update-greater
    (implies (and (ifoptdag-memo-boundedp bound x)
                  (ifoptdag-base-ev-memo-correct x ifoptdag a)
                  (<= (nfix bound) (nfix n)))
             (ifoptdag-base-ev-memo-correct x (update-nth n v ifoptdag) a))
    :hints(("Goal" :in-theory (enable ifoptdag-memo-boundedp))))

  (defthm ifoptdag-base-ev-memo-correct-of-resize-list
    (implies (and (ifoptdag-base-ev-memo-correct x ifoptdag a)
                  (<= (len ifoptdag) (nfix n)))
             (ifoptdag-base-ev-memo-correct x (resize-list ifoptdag n '(:quote nil)) a))
    :hints (("goal" :induct (len x))))
  
  (local (in-theory (enable ifoptdag-memo-fix))))

(define ifoptdag-add-node ((node ifopt-node-p)
                           (next natp)
                           ifoptdag)
  :returns (new-ifoptdag)
  (b* ((next (lnfix next))
       (ifoptdag (if (< next (ifopt-nodes-length ifoptdag))
                     ifoptdag
                   (resize-ifopt-nodes (max 16 (* 2 next)) ifoptdag))))
    (set-ifopt-node next node ifoptdag))
  ///
  (defret size-bound-of-<fn>
    (< (nfix next) (len new-ifoptdag))
    :rule-classes :linear)

  (defret nth-of-<fn>
    (ifopt-node-equiv (nth n new-ifoptdag)
                      (if (equal (nfix n) (nfix next))
                          node
                        (nth n ifoptdag))))

  (defret nth-of-<fn>-new
    (equal (nth next new-ifoptdag)
           (ifopt-node-fix node)))

  (defret ifoptdag-orderedp-of-<fn>
    (implies (and (ifoptdag-orderedp ifoptdag)
                  (< (ifopt-node-max node) (nfix next)))
             (ifoptdag-orderedp new-ifoptdag)))

  (defret ifoptdag-hash-correct-of-<fn>
    (implies (and (ifoptdag-hash-correct hash ifoptdag)
                  (ifoptdag-hash-boundedp next hash))
             (ifoptdag-hash-correct hash new-ifoptdag)))

  (defret ifoptdag-base-ev-memo-correct-of-<fn>
    (implies (and (ifoptdag-base-ev-memo-correct memo ifoptdag a)
                  (ifoptdag-memo-boundedp next memo))
             (ifoptdag-base-ev-memo-correct memo new-ifoptdag a)))

  (defret ifoptdag-to-term-of-<fn>
    (implies (< (nfix n) (nfix next))
             (equal (ifoptdag-to-term n new-ifoptdag)
                    (ifoptdag-to-term n ifoptdag))))

  (defret ifopt-node-to-term-of-<fn>
    (implies (< (ifopt-node-max oldnode) (nfix next))
             (equal (ifopt-node-to-term oldnode new-ifoptdag)
                    (ifopt-node-to-term oldnode ifoptdag))))

  (defret ifoptdag-to-termlist-of-<fn>
    (implies (< (nat-list-max ns) (nfix next))
             (equal (ifoptdag-to-termlist ns new-ifoptdag)
                    (ifoptdag-to-termlist ns ifoptdag)))))


(define ifoptdag-add-hashed-node ((node ifopt-node-p)
                                  (next natp)
                                  (hash ifoptdag-hash-p)
                                  ifoptdag)
  :returns (mv (idx natp :rule-classes :type-prescription)
               (new-next natp :rule-classes :type-prescription)
               (new-hash ifoptdag-hash-p)
               (new-ifoptdag))
  :guard (<= next (ifopt-nodes-length ifoptdag))
  (b* ((node (ifopt-node-fix node))
       (hash (ifoptdag-hash-fix hash))
       (next (lnfix next))
       (look (hons-get node hash))
       ((when look)
        (mv (cdr look) next hash ifoptdag))
       (ifoptdag (ifoptdag-add-node node next ifoptdag))
       (hash (hons-acons node next hash)))
    (mv next (1+ next) hash ifoptdag))
  ///
  (defret next-bound-of-<fn>
    (<= (nfix next) new-next)
    :rule-classes :linear)

  (defret idx-bound-of-<fn>
    (implies (ifoptdag-hash-boundedp next hash)
             (< idx new-next))
    :hints(("Goal" :in-theory (enable ifoptdag-hash-boundedp-implies-lookup)))
    :rule-classes ((:linear :trigger-terms (idx new-next))))

  (defret ifoptdag-orderedp-of-<fn>
    (implies (and (ifoptdag-orderedp ifoptdag)
                  (< (ifopt-node-max node) (nfix next)))
             (ifoptdag-orderedp new-ifoptdag)))

  (defret ifoptdag-hash-boundedp-of-<fn>
    (implies (ifoptdag-hash-boundedp next hash)
             (ifoptdag-hash-boundedp new-next new-hash))
    :hints(("Goal" :in-theory (enable ifoptdag-hash-boundedp))))

  (defret len-of-<fn>
    (implies (<= (nfix next) (len ifoptdag))
             (<= (nfix new-next) (len new-ifoptdag)))
    :rule-classes :linear)

  (defret nth-of-<fn>-new-idx
    (implies (ifoptdag-hash-correct hash ifoptdag)
             (ifopt-node-equiv (nth idx new-ifoptdag)
                               node))
    :hints(("Goal" :in-theory (enable lookup-when-ifoptdag-hash-correct))))

  (defret nth-of-<fn>-old-idx
    (implies (< (nfix n) (nfix next))
             (ifopt-node-equiv (nth n new-ifoptdag)
                               (nth n ifoptdag))))

  (defret ifoptdag-hash-correct-of-<fn>
    (implies (and (ifoptdag-hash-correct hash ifoptdag)
                  (ifoptdag-hash-boundedp next hash))
             (ifoptdag-hash-correct new-hash new-ifoptdag))
    :hints(("Goal" :in-theory (enable ifoptdag-hash-correct))))

  (defret ifoptdag-base-ev-memo-correct-of-<fn>
    (implies (and (ifoptdag-base-ev-memo-correct memo ifoptdag a)
                  (ifoptdag-memo-boundedp next memo))
             (ifoptdag-base-ev-memo-correct memo new-ifoptdag a)))

  (defret ifoptdag-to-term-of-<fn>
    (implies (< (nfix n) (nfix next))
             (equal (ifoptdag-to-term n new-ifoptdag)
                    (ifoptdag-to-term n ifoptdag))))

  (defret ifoptdag-to-term-of-<fn>-result
    (implies (and (< (ifopt-node-max node) (nfix next))
                  (ifoptdag-hash-correct hash ifoptdag)
                  (ifoptdag-orderedp ifoptdag))
             (equal (ifoptdag-to-term idx new-ifoptdag)
                    (ifopt-node-to-term node ifoptdag)))
    :hints(("Goal" :use (;; (:instance lookup-when-ifoptdag-hash-correct
                         ;;  (k (ifopt-node-fix node)) (x hash))
                         (:instance ifoptdag-orderedp-implies
                          (k (cdr (hons-assoc-equal (ifopt-node-fix node) hash)))))
            :in-theory (e/d (lookup-when-ifoptdag-hash-correct)
                            (ifoptdag-orderedp-implies)))
           (and stable-under-simplificationp
                (b* ((lit (car (last clause))))
                  (case-match lit
                    (('equal ('ifoptdag-to-term . args) &)
                     `(:expand ((ifoptdag-to-term . ,args)))))))))

  

  (defret ifopt-node-to-term-of-<fn>
    (implies (< (ifopt-node-max oldnode) (nfix next))
             (equal (ifopt-node-to-term oldnode new-ifoptdag)
                    (ifopt-node-to-term oldnode ifoptdag))))
  
  (defret ifoptdag-to-termlist-of-<fn>
    (implies (< (nat-list-max ns) (nfix next))
             (equal (ifoptdag-to-termlist ns new-ifoptdag)
                    (ifoptdag-to-termlist ns ifoptdag))))

  ;; (defret nat-list-boundedp-args-of-ifopt-node-fncall
  ;;   :pre-bind ((node (ifopt-node-fncall fn args)))
  ;;   (implies (and (< (nat-list-max args) (nfix next))
  ;;                 (ifoptdag-hash-correct hash ifoptdag)
  ;;                 (ifoptdag-orderedp ifoptdag))
  ;;            (< (nat-list-max args) (nfix idx)))
  ;;   :hints (("goal" :use ((:instance ifoptdag-orderedp-implies
  ;;                          (k (cdr (hons-assoc-equal (ifopt-node-fncall fn args) hash)))))
  ;;            :in-theory (e/d (ifopt-node-boundedp
  ;;                             lookup-when-ifoptdag-hash-correct)
  ;;                            (ifoptdag-orderedp-implies
  ;;                             <fn>)))))
  )
  






(defines term-to-ifoptdag
  (define term-to-ifoptdag-nomemo ((x pseudo-termp)
                                   (next natp)
                                   (memo ifoptdag-memo-p)
                                   (hash ifoptdag-hash-p)
                                   ifoptdag)
    :measure (acl2::two-nats-measure (pseudo-term-count x) 0)
    :guard (and (lambda-free-term-p x)
                (ifoptdag-memo-boundedp next memo)
                (ifoptdag-hash-boundedp next hash)
                (ifoptdag-orderedp ifoptdag)
                (<= next (ifopt-nodes-length ifoptdag)))
    :verify-guards nil
    :returns (mv (res natp :rule-classes :type-prescription)
                 (new-next natp :rule-classes :type-prescription)
                 (new-memo ifoptdag-memo-p)
                 (new-hash ifoptdag-hash-p)
                 (new-ifoptdag))
    (b* ((memo (ifoptdag-memo-fix memo))
         (hash (ifoptdag-hash-fix hash))
         (next (lnfix next)))
      (pseudo-term-case x
        :const (b* (((mv res next hash ifoptdag)
                     (ifoptdag-add-hashed-node (ifopt-node-quoteh x.val) next hash ifoptdag)))
                 (mv res next memo hash ifoptdag))
        :var (b* (((mv res next hash ifoptdag)
                   (ifoptdag-add-hashed-node (ifopt-node-varh x.name) next hash ifoptdag)))
               (mv res next memo hash ifoptdag))
        :call (b* (((mv args next memo hash ifoptdag)
                    (termlist-to-ifoptdag x.args next memo hash ifoptdag))
                   ((mv res next hash ifoptdag)
                    (ifoptdag-add-hashed-node (ifopt-node-fncallh x.fn args) next hash ifoptdag)))
                (mv res next memo hash ifoptdag)))))

  (define term-to-ifoptdag ((x pseudo-termp)
                            (next natp)
                            (memo ifoptdag-memo-p)
                            (hash ifoptdag-hash-p)
                            ifoptdag)
    :measure (acl2::two-nats-measure (pseudo-term-count x) 1)
    :guard (and (lambda-free-term-p x)
                (ifoptdag-memo-boundedp next memo)
                (ifoptdag-hash-boundedp next hash)
                (ifoptdag-orderedp ifoptdag)
                (<= next (ifopt-nodes-length ifoptdag)))
    :returns (mv (res natp :rule-classes :type-prescription)
                 (new-next natp :rule-classes :type-prescription)
                 (new-memo ifoptdag-memo-p)
                 (new-hash ifoptdag-hash-p)
                 (new-ifoptdag))
    (b* ((memo (ifoptdag-memo-fix memo))
         (x (pseudo-term-fix x))
         (look (hons-get x memo))
         ((when look)
          (mv (cdr look)
              (lnfix next)
              memo
              (ifoptdag-hash-fix hash)
              ifoptdag))
         ((mv res next memo hash ifoptdag)
          (term-to-ifoptdag-nomemo x next memo hash ifoptdag))
         (memo (hons-acons x res memo)))
      (mv res next memo hash ifoptdag)))

  (define termlist-to-ifoptdag ((x pseudo-term-listp)
                                (next natp)
                                (memo ifoptdag-memo-p)
                                (hash ifoptdag-hash-p)
                                ifoptdag)
    :measure (acl2::two-nats-measure (pseudo-term-list-count x) 0)
    :guard (and (lambda-free-termlist-p x)
                (ifoptdag-memo-boundedp next memo)
                (ifoptdag-hash-boundedp next hash)
                (ifoptdag-orderedp ifoptdag)
                (<= next (ifopt-nodes-length ifoptdag)))
    :returns (mv (res (and (nat-listp res) (equal (len res) (len x))))
                 (new-next natp :rule-classes :type-prescription)
                 (new-memo ifoptdag-memo-p)
                 (new-hash ifoptdag-hash-p)
                 (new-ifoptdag))
    (b* (((when (atom x))
          (mv nil
              (lnfix next)
              (ifoptdag-memo-fix memo)
              (ifoptdag-hash-fix hash)
              ifoptdag))
         ((mv fst next memo hash ifoptdag)
          (term-to-ifoptdag (car x) next memo hash ifoptdag))
         ((mv rst next memo hash ifoptdag)
          (termlist-to-ifoptdag (cdr x) next memo hash ifoptdag)))
      (mv (cons fst rst) next memo hash ifoptdag)))
  ///

  (local (in-theory (disable term-to-ifoptdag
                             term-to-ifoptdag-nomemo
                             termlist-to-ifoptdag)))
  
  (std::defret-mutual len-of-<fn>
    (defret len-of-<fn>
      (implies (<= (nfix next) (len ifoptdag))
               (<= (nfix new-next) (len new-ifoptdag)))
      :hints ('(:expand (<call>)))
      :rule-classes :linear
      :fn term-to-ifoptdag-nomemo)
    (defret len-of-<fn>
      (implies (<= (nfix next) (len ifoptdag))
               (<= (nfix new-next) (len new-ifoptdag)))
      :hints ('(:expand (<call>)))
      :rule-classes :linear
      :fn term-to-ifoptdag)
    (defret len-of-<fn>
      (implies (<= (nfix next) (len ifoptdag))
               (<= (nfix new-next) (len new-ifoptdag)))
      :hints ('(:expand (<call>)))
      :rule-classes :linear
      :fn termlist-to-ifoptdag))

  (std::defret-mutual next-bound-of-<fn>
    (defret next-bound-of-<fn>
      (<= (nfix next) new-next)
      :hints ('(:expand (<call>)))
      :rule-classes :linear
      :fn term-to-ifoptdag-nomemo)
    (defret next-bound-of-<fn>
      (<= (nfix next) new-next)
      :hints ('(:expand (<call>)))
      :rule-classes :linear
      :fn term-to-ifoptdag)
    (defret next-bound-of-<fn>
      (<= (nfix next) new-next)
      :hints ('(:expand (<call>)))
      :rule-classes :linear
      :fn termlist-to-ifoptdag))

  (local (in-theory (enable ifoptdag-memo-boundedp-monotonic
                            ifoptdag-memo-boundedp-implies-lookup
                            ifoptdag-hash-boundedp-implies-lookup)))
  
  (std::defret-mutual invars-of-<fn>
    (defret invars-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash))
               (and (< res new-next)
                    (ifoptdag-orderedp new-ifoptdag)
                    (ifoptdag-memo-boundedp new-next new-memo)
                    (ifoptdag-hash-boundedp new-next new-hash)
                    (implies (ifoptdag-hash-correct hash ifoptdag)
                             (ifoptdag-hash-correct new-hash new-ifoptdag))))
      :hints ('(:expand (<call>)
                :in-theory (enable ifopt-node-max)
                ))
      :fn term-to-ifoptdag-nomemo)
    (defret invars-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash))
               (and (< res new-next)
                    (ifoptdag-orderedp new-ifoptdag)
                    (ifoptdag-memo-boundedp new-next new-memo)
                    (ifoptdag-hash-boundedp new-next new-hash)
                    (implies (ifoptdag-hash-correct hash ifoptdag)
                             (ifoptdag-hash-correct new-hash new-ifoptdag))))
      :hints ('(:expand (<call>
                         (:free (next a b)
                          (ifoptdag-memo-boundedp next (cons a b))))))
      :fn term-to-ifoptdag)
    (defret invars-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash))
               (and (< (nat-list-max res) new-next)
                    (ifoptdag-orderedp new-ifoptdag)
                    (ifoptdag-memo-boundedp new-next new-memo)
                    (ifoptdag-hash-boundedp new-next new-hash)
                    (implies (ifoptdag-hash-correct hash ifoptdag)
                             (ifoptdag-hash-correct new-hash new-ifoptdag))))
      :hints ('(:expand (<call>
                         (:free (bound a b) (nat-list-max (cons a b))))))
      :fn termlist-to-ifoptdag))

  (defret res-bound-of-<fn>
    (implies (and (ifoptdag-orderedp ifoptdag)
                  (ifoptdag-memo-boundedp next memo)
                  (ifoptdag-hash-boundedp next hash))
             (< res new-next))
    :rule-classes :linear
    :fn term-to-ifoptdag-nomemo)

  (defret res-bound-of-<fn>
    (implies (and (ifoptdag-orderedp ifoptdag)
                  (ifoptdag-memo-boundedp next memo)
                  (ifoptdag-hash-boundedp next hash))
             (< res new-next))
    :rule-classes :linear
    :fn term-to-ifoptdag)

  (defret nat-list-boundedp-of-<fn>
    (implies (and (ifoptdag-orderedp ifoptdag)
                  (ifoptdag-memo-boundedp next memo)
                  (ifoptdag-hash-boundedp next hash))
             (< (nat-list-max res) new-next))
    :rule-classes :linear
    :fn termlist-to-ifoptdag)

      
  (verify-guards term-to-ifoptdag
    :hints (("goal" :expand ((lambda-free-term-p x)
                             (lambda-free-termlist-p x)))))

  (std::defret-mutual ifoptdag-to-term-of-<fn>
    (defret ifoptdag-to-term-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (< (nfix n) (nfix next)))
               (equal (ifoptdag-to-term n new-ifoptdag)
                      (ifoptdag-to-term n ifoptdag)))
      :hints ('(:expand (<call>
                         (lambda-free-term-p x))
                :in-theory (enable ifopt-node-boundedp)))
      :fn term-to-ifoptdag-nomemo)
    (defret ifoptdag-to-term-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (< (nfix n) (nfix next)))
               (equal (ifoptdag-to-term n new-ifoptdag)
                      (ifoptdag-to-term n ifoptdag)))
      :hints ('(:expand (<call>
                         (:free (next a b)
                          (ifoptdag-memo-boundedp next (cons a b))))))
      :fn term-to-ifoptdag)
    (defret ifoptdag-to-term-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (< (nfix n) (nfix next)))
               (equal (ifoptdag-to-term n new-ifoptdag)
                      (ifoptdag-to-term n ifoptdag)))
      :hints ('(:expand (<call>
                         (:free (bound a b) (nat-list-boundedp bound (cons a b))))))
      :fn termlist-to-ifoptdag))

  (std::defret-mutual ifopt-node-to-term-of-<fn>
    (defret ifopt-node-to-term-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (< (ifopt-node-max n) (nfix next)))
               (equal (ifopt-node-to-term n new-ifoptdag)
                      (ifopt-node-to-term n ifoptdag)))
      :hints ('(:expand (<call>
                         (lambda-free-term-p x))
                :in-theory (enable ifopt-node-boundedp)))
      :fn term-to-ifoptdag-nomemo)
    (defret ifopt-node-to-term-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (< (ifopt-node-max n) (nfix next)))
               (equal (ifopt-node-to-term n new-ifoptdag)
                      (ifopt-node-to-term n ifoptdag)))
      :hints ('(:expand (<call>
                         (:free (next a b)
                          (ifoptdag-memo-boundedp next (cons a b))))))
      :fn term-to-ifoptdag)
    (defret ifopt-node-to-term-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (< (ifopt-node-max n) (nfix next)))
               (equal (ifopt-node-to-term n new-ifoptdag)
                      (ifopt-node-to-term n ifoptdag)))
      :hints ('(:expand (<call>
                         (:free (bound a b) (nat-list-boundedp bound (cons a b))))))
      :fn termlist-to-ifoptdag))
  
  (std::defret-mutual ifoptdag-to-termlist-of-<fn>
    (defret ifoptdag-to-termlist-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (< (nat-list-max ns) (nfix next)))
               (equal (ifoptdag-to-termlist ns new-ifoptdag)
                      (ifoptdag-to-termlist ns ifoptdag)))
      :hints ('(:expand (<call>
                         (lambda-free-term-p x))
                :in-theory (enable ifopt-node-boundedp)))
      :fn term-to-ifoptdag-nomemo)
    (defret ifoptdag-to-termlist-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (< (nat-list-max ns) (nfix next)))
               (equal (ifoptdag-to-termlist ns new-ifoptdag)
                      (ifoptdag-to-termlist ns ifoptdag)))
      :hints ('(:expand (<call>
                         (:free (next a b)
                          (ifoptdag-memo-boundedp next (cons a b))))))
      :fn term-to-ifoptdag)
    (defret ifoptdag-to-termlist-of-<fn>
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (< (nat-list-max ns) (nfix next)))
               (equal (ifoptdag-to-termlist ns new-ifoptdag)
                      (ifoptdag-to-termlist ns ifoptdag)))
      :hints ('(:expand (<call>
                         (:free (bound a b) (nat-list-boundedp bound (cons a b))))))
      :fn termlist-to-ifoptdag))

  (std::defret-mutual <fn>-correct
    (defret <fn>-correct
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (ifoptdag-hash-correct hash ifoptdag)
                    (ifoptdag-base-ev-memo-correct memo ifoptdag a)
                    (lambda-free-term-p x))
               (and (ifoptdag-base-ev-memo-correct new-memo new-ifoptdag a)
                    (equal (base-ev (ifoptdag-to-term res new-ifoptdag) a)
                           (base-ev x a))))
      :hints ('(:expand (<call>
                         (lambda-free-term-p x))
                :in-theory (enable ifopt-node-max
                                   ifopt-node-to-term
                                   acl2::base-ev-of-fncall-args))
              (and stable-under-simplificationp
                   '(:use ((:instance nat-list-boundedp-of-termlist-to-ifoptdag
                            (x (pseudo-term-call->args x))
                            (next (nfix next))
                            (memo (ifoptdag-memo-fix memo))
                            (hash (ifoptdag-hash-fix hash))))
                     :in-theory (disable nat-list-boundedp-of-termlist-to-ifoptdag
                                         invars-of-termlist-to-ifoptdag))))
      :fn term-to-ifoptdag-nomemo)
    (defret <fn>-correct
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (ifoptdag-hash-correct hash ifoptdag)
                    (ifoptdag-base-ev-memo-correct memo ifoptdag a)
                    (lambda-free-term-p x))
               (and (ifoptdag-base-ev-memo-correct new-memo new-ifoptdag a)
                    (equal (base-ev (ifoptdag-to-term res new-ifoptdag) a)
                           (base-ev x a))))
      :hints ('(:expand (<call>
                         (:free (next a b)
                          (ifoptdag-memo-boundedp next (cons a b))))))
      :fn term-to-ifoptdag)
    (defret <fn>-correct
      (implies (and (ifoptdag-orderedp ifoptdag)
                    (ifoptdag-memo-boundedp next memo)
                    (ifoptdag-hash-boundedp next hash)
                    (ifoptdag-hash-correct hash ifoptdag)
                    (ifoptdag-base-ev-memo-correct memo ifoptdag a)
                    (lambda-free-termlist-p x))
               (and (ifoptdag-base-ev-memo-correct new-memo new-ifoptdag a)
                    (equal (base-ev-list (ifoptdag-to-termlist res new-ifoptdag) a)
                           (base-ev-list x a))))
      :hints ('(:expand (<call>
                         (lambda-free-termlist-p x)
                         (ifoptdag-to-termlist nil ifoptdag)
                         (:free (a b ifoptdag) (ifoptdag-to-termlist (cons a b) ifoptdag))
                         (:free (a b) (nat-list-max (cons a b))))))
      :fn termlist-to-ifoptdag))
  )


(fty::defmap ifopt-nodeset :key-type natp :val-type acl2::any :true-listp t)

(define ifopt-nodeset->list ((x ifopt-nodeset-p))
  :Returns (lst nat-listp)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x)) (natp (caar x))))
        (cons (caar x) (ifopt-nodeset->list (cdr x)))
      (ifopt-nodeset->list (cdr x))))
  ///
  (local (in-theory (enable ifopt-nodeset-fix))))
             

(defines ifoptdag-traverse-uncond
  :ruler-extenders (:lambdas)
  (define ifoptdag-traverse-uncond ((n natp)
                                    ifoptdag
                                    (omit ifopt-nodeset-p)
                                    (seen ifopt-nodeset-p))
    :guard (and (< n (ifopt-nodes-length ifoptdag))
                (ifoptdag-orderedp ifoptdag))
    :well-founded-relation acl2::nat-list-<
    :measure (list n 2 0)
    :hints(("Goal" :expand ((nat-list-max args)
                            (ifopt-node-max node))))
    :returns (new-seen ifopt-nodeset-p)
    :verify-guards nil
    (b* ((seen (ifopt-nodeset-fix seen))
         (omit (ifopt-nodeset-fix omit))
         ((when (or (hons-get (lnfix n) omit)
                    (hons-get (lnfix n) seen)))
          seen)
         (seen (hons-acons (lnfix n) t seen))
         (node (get-ifopt-node n ifoptdag))
         ((unless (mbt (< (ifopt-node-max node) (lnfix n))))
          seen))
      (ifopt-node-traverse-uncond node ifoptdag omit seen)))

  (define ifopt-node-traverse-uncond ((node ifopt-node-p)
                                      ifoptdag
                                      (omit ifopt-nodeset-p)
                                      (seen ifopt-nodeset-p))
    :guard (and (< (ifopt-node-max node) (ifopt-nodes-length ifoptdag))
                (ifoptdag-orderedp ifoptdag))
    :measure (list (+ 1 (ifopt-node-max node)) 1 0)
    :returns (new-seen ifopt-nodeset-p)
    (b* ((seen (ifopt-nodeset-fix seen)))
      (ifopt-node-case node
        :quote seen
        :var seen
        :fncall (ifoptdag-traverse-uncond-list node.args ifoptdag omit seen)
        :if (b* ((seen (ifoptdag-traverse-uncond node.test ifoptdag omit seen)))
              (ifoptdag-traverse-uncond-list node.pre-evals ifoptdag omit seen)))))
  
  (define ifoptdag-traverse-uncond-list ((args nat-listp)
                                         (ifoptdag)
                                         (omit ifopt-nodeset-p)
                                         (seen ifopt-nodeset-p))
    :guard (and (< (nat-list-max args) (ifopt-nodes-length ifoptdag))
                (ifoptdag-orderedp ifoptdag))
    :returns (new-seen ifopt-nodeset-p)
    :measure (list (+ 1 (nat-list-max args)) 0 (+ 1 (len args)))
    (if (atom args)
        (ifopt-nodeset-fix seen)
      (B* ((seen (ifoptdag-traverse-uncond (car args) ifoptdag omit seen)))
        (ifoptdag-traverse-uncond-list (cdr args) ifoptdag omit seen))))
  ///
  (verify-guards ifoptdag-traverse-uncond
    :hints(("Goal" :expand ((nat-list-max args)
                            (ifopt-node-max node)))))

  (std::defret-mutual max-of-<fn>
    (defret max-of-<fn>
      (implies (ifoptdag-orderedp ifoptdag)
               (<= (nat-list-max (ifopt-nodeset->list new-seen))
                   (max (nat-list-max (ifopt-nodeset->list seen))
                        (nfix n))))
      :hints ('(:expand (<call>
                         (:free (a b) (ifopt-nodeset->list (cons a b)))
                         (:free (a b) (nat-list-max (cons a b))))))
      :fn ifoptdag-traverse-uncond)
    (defret max-of-<fn>
      (implies (ifoptdag-orderedp ifoptdag)
               (<= (nat-list-max (ifopt-nodeset->list new-seen))
                   (max (nat-list-max (ifopt-nodeset->list seen))
                        (ifopt-node-max node))))
      :hints ('(:expand (<call>
                         (ifopt-node-max node)
                         (:free (a b) (ifopt-nodeset->list (cons a b))))))
      :fn ifopt-node-traverse-uncond)
    (defret max-of-<fn>
      (implies (ifoptdag-orderedp ifoptdag)
               (<= (nat-list-max (ifopt-nodeset->list new-seen))
                   (max (nat-list-max (ifopt-nodeset->list seen))
                        (nat-list-max args))))
      :hints ('(:expand (<call>
                         (nat-list-max args))))
      :fn ifoptdag-traverse-uncond-list))

  (fty::deffixequiv-mutual ifoptdag-traverse-uncond))


(defines ifoptdag-intersect-uncond
  :ruler-extenders (:lambdas)
  (define ifoptdag-intersect-uncond ((n natp)
                                     ifoptdag
                                     (omit ifopt-nodeset-p)
                                     (intersect ifopt-nodeset-p)
                                     (seen ifopt-nodeset-p)
                                     (boundary nat-listp))
    :guard (and (< n (ifopt-nodes-length ifoptdag))
                (ifoptdag-orderedp ifoptdag))
    :well-founded-relation acl2::nat-list-<
    :measure (list n 2 0)
    :hints(("Goal" :expand ((nat-list-max args)
                            (ifopt-node-max node))))
    :returns (mv (new-seen ifopt-nodeset-p)
                 (new-boundary nat-listp))
    :verify-guards nil
    (b* ((seen (ifopt-nodeset-fix seen))
         (omit (ifopt-nodeset-fix omit))
         (boundary (mbe :logic (acl2::nat-list-fix boundary) :exec boundary))
         ((when (or (hons-get (lnfix n) omit)
                    (hons-get (lnfix n) seen)))
          (mv seen boundary))
         (seen (hons-acons (lnfix n) t seen))
         ((when (hons-get (lnfix n) intersect))
          (mv seen (cons (lnfix n) boundary)))
         (node (get-ifopt-node n ifoptdag))
         ((unless (mbt (< (ifopt-node-max node) (lnfix n))))
          (mv seen boundary)))
      (ifopt-node-intersect-uncond node ifoptdag omit intersect seen boundary)))

  (define ifopt-node-intersect-uncond ((node ifopt-node-p)
                                       ifoptdag
                                       (omit ifopt-nodeset-p)
                                       (intersect ifopt-nodeset-p)
                                       (seen ifopt-nodeset-p)
                                       (boundary nat-listp))
    :guard (and (< (ifopt-node-max node) (ifopt-nodes-length ifoptdag))
                (ifoptdag-orderedp ifoptdag))
    :measure (list (1+ (ifopt-node-max node)) 1 0)
    :returns (mv (new-seen ifopt-nodeset-p)
                 (new-boundary nat-listp))
    (b* ((seen (ifopt-nodeset-fix seen))
         (boundary (mbe :logic (acl2::nat-list-fix boundary) :exec boundary)))
      (ifopt-node-case node
        :quote (mv seen boundary)
        :var (mv seen boundary)
        :fncall (ifoptdag-intersect-uncond-list node.args ifoptdag omit intersect seen boundary)
        :if (b* (((mv seen boundary)
                  (ifoptdag-intersect-uncond node.test ifoptdag omit intersect seen boundary)))
              (ifoptdag-intersect-uncond-list node.pre-evals ifoptdag omit intersect seen boundary)))))
                 
  (define ifoptdag-intersect-uncond-list ((args nat-listp)
                                          (ifoptdag)
                                          (omit ifopt-nodeset-p)
                                          (intersect ifopt-nodeset-p)
                                          (seen ifopt-nodeset-p)
                                          (boundary nat-listp))
    :guard (and (< (nat-list-max args) (ifopt-nodes-length ifoptdag))
                (ifoptdag-orderedp ifoptdag))
    :returns (mv (new-seen ifopt-nodeset-p)
                 (new-boundary nat-listp))
    :measure (list (+ 1 (nat-list-max args)) 0 (+ 1 (len args)))
    (if (atom args)
        (mv (ifopt-nodeset-fix seen)
            (mbe :logic (acl2::nat-list-fix boundary) :exec boundary))
      (B* (((mv seen boundary) (ifoptdag-intersect-uncond (car args) ifoptdag omit intersect seen boundary)))
        (ifoptdag-intersect-uncond-list (cdr args) ifoptdag omit intersect seen boundary))))
  ///
  (verify-guards ifoptdag-intersect-uncond
    :hints(("Goal" :expand ((nat-list-max args)
                            (ifopt-node-max node)))))
  

  (std::defret-mutual max-seen-of-<fn>
    (defret max-seen-of-<fn>
      (implies (ifoptdag-orderedp ifoptdag)
               (<= (nat-list-max (ifopt-nodeset->list new-seen))
                   (max (nat-list-max (ifopt-nodeset->list seen))
                        (nfix n))))
      :hints ('(:expand (<call>
                         (:free (a b) (ifopt-nodeset->list (cons a b)))
                         (:free (a b) (nat-list-max (cons a b))))))
      :fn ifoptdag-intersect-uncond
      :rule-classes :linear)
    (defret max-seen-of-<fn>
      (implies (ifoptdag-orderedp ifoptdag)
               (<= (nat-list-max (ifopt-nodeset->list new-seen))
                   (max (nat-list-max (ifopt-nodeset->list seen))
                        (ifopt-node-max node))))
      :hints ('(:expand (<call>
                         (ifopt-node-max node)
                         (:free (a b) (ifopt-nodeset->list (cons a b))))))
      :fn ifopt-node-intersect-uncond
      :rule-classes :linear)
    (defret max-seen-of-<fn>
      (implies (ifoptdag-orderedp ifoptdag)
               (<= (nat-list-max (ifopt-nodeset->list new-seen))
                   (max (nat-list-max (ifopt-nodeset->list seen))
                        (nat-list-max args))))
      :hints ('(:expand (<call>
                         (nat-list-max args))))
      :fn ifoptdag-intersect-uncond-list
      :rule-classes :linear))

  (std::defret-mutual max-boundary-of-<fn>
    (defret max-boundary-of-<fn>
      (implies (ifoptdag-orderedp ifoptdag)
               (<= (nat-list-max new-boundary)
                   (max (nat-list-max boundary)
                        (nfix n))))
      :hints ('(:expand (<call>
                         (:free (a b) (ifopt-nodeset->list (cons a b)))
                         (:free (a b) (nat-list-max (cons a b))))))
      :fn ifoptdag-intersect-uncond
      :rule-classes :linear)
    (defret max-boundary-of-<fn>
      (implies (ifoptdag-orderedp ifoptdag)
               (<= (nat-list-max new-boundary)
                   (max (nat-list-max boundary)
                        (ifopt-node-max node))))
      :hints ('(:expand (<call>
                         (ifopt-node-max node)
                         (:free (a b) (ifopt-nodeset->list (cons a b))))))
      :fn ifopt-node-intersect-uncond
      :rule-classes :linear)
    (defret max-boundary-of-<fn>
      (implies (ifoptdag-orderedp ifoptdag)
               (<= (nat-list-max new-boundary)
                   (max (nat-list-max boundary)
                        (nat-list-max args))))
      :hints ('(:expand (<call>
                         (nat-list-max args))))
      :fn ifoptdag-intersect-uncond-list
      :rule-classes :linear))

  (fty::deffixequiv-mutual ifoptdag-intersect-uncond))

(define ifoptdag-optimize-if-node ((test natp)
                                   (then natp)
                                   (else natp)
                                   (ifoptdag))
  :returns (node ifopt-node-p)
  :guard (and (< test (ifopt-nodes-length ifoptdag))
              (< then (ifopt-nodes-length ifoptdag))
              (< else (ifopt-nodes-length ifoptdag))
              (ifoptdag-orderedp ifoptdag))
  (b* ((then-seen (ifoptdag-traverse-uncond then ifoptdag nil nil))
       ((mv else-seen intersect)
        (ifoptdag-intersect-uncond else ifoptdag nil then-seen nil nil)))
    (fast-alist-free then-seen)
    (fast-alist-free else-seen)
    (make-ifopt-node-if
     :test test :then then :else else :pre-evals intersect))
  ///
  (defret ifopt-node-boundedp-of-<fn>
    (implies (ifoptdag-orderedp ifoptdag)
             (equal (ifopt-node-max node)
                    (max (nfix test) (max (nfix then) (nfix else)))))
    :hints (("goal" :in-theory (enable ifopt-node-max))))

  (defret ifopt-node-to-term-of-<fn>
    (equal (ifopt-node-to-term node ifoptdag)
           (pseudo-term-fncall 'if
                               (list (ifoptdag-to-term test ifoptdag)
                                     (ifoptdag-to-term then ifoptdag)
                                     (ifoptdag-to-term else ifoptdag))))
    :hints (("goal" :expand ((:free (pre-evals)
                              (ifopt-node-to-term (ifopt-node-if test then else pre-evals) ifoptdag)))))))

(local (defthmd equal-of-len
         (implies (syntaxp (quotep n))
                  (equal (equal (len x) n)
                         (cond ((equal n 0) (atom x))
                               ((zp n) nil)
                               ((consp x)
                                (equal (len (cdr x)) (1- n))))))))

(define ifoptdag-optimize-maybe-if-node ((node ifopt-node-p)
                                         (ifoptdag))
  :returns (new-node ifopt-node-p)
  :guard (and (< (ifopt-node-max node) (ifopt-nodes-length ifoptdag))
              (ifoptdag-orderedp ifoptdag))
  :guard-hints (("goal" :in-theory (e/d (ifopt-node-max
                                         nat-list-max
                                         equal-of-len)
                                        (len
                                         ifoptdag-orderedp-implies
                                         acl2::natp-when-gte-0))
                 :do-not-induct t))
  (ifopt-node-case node
    :fncall (if (and (eq node.fn 'if)
                     (eql (len node.args) 3))
                (ifoptdag-optimize-if-node
                 (first node.args)
                 (second node.args)
                 (third node.args)
                 ifoptdag)
              (ifopt-node-fix node))
    :otherwise (ifopt-node-fix node))
  ///

  (local (defthm natp-implies-greater-than-neg1
           (implies (natp x)
                    (< -1 x))))
  
  (defret ifopt-node-boundedp-of-<fn>
    (implies (ifoptdag-orderedp ifoptdag)
             (equal (ifopt-node-max new-node)
                    (ifopt-node-max node)))
    :hints (("goal" :in-theory (e/d (nat-list-max
                                     equal-of-len)
                                    (len
                                     ifoptdag-orderedp-implies
                                     acl2::natp-when-gte-0))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((ifopt-node-max node))))))

  (defret ifopt-node-to-term-of-<fn>
    (equal (ifopt-node-to-term new-node ifoptdag)
           (ifopt-node-to-term node ifoptdag))
    :hints (("goal" :in-theory (e/d (equal-of-len) (len)))
            (and stable-under-simplificationp
                 '(:expand ((ifopt-node-to-term node ifoptdag))
                   :in-theory (enable ifoptdag-to-termlist))))))

(define ifoptdag-optimize-node ((n natp) ifoptdag)
  :guard (and (< n (ifopt-nodes-length ifoptdag))
              (ifoptdag-orderedp ifoptdag))
  :returns new-ifoptdag
  (set-ifopt-node
   n (ifoptdag-optimize-maybe-if-node
      (get-ifopt-node n ifoptdag) ifoptdag)
   ifoptdag)
  ///
  
  (defret ifoptdag-orderedp-of-<fn>
    (implies (ifoptdag-orderedp ifoptdag)
             (ifoptdag-orderedp new-ifoptdag))
    :hints (("goal" :in-theory (e/d (equal-of-len
                                     ifopt-node-max
                                     nat-list-max)
                                    (len ifoptdag-orderedp-implies
                                         ACL2::NATP-WHEN-GTE-0)))
            (and stable-under-simplificationp
                 '(:use ((:instance ifoptdag-orderedp-implies
                          (k n)))))))

  (local (in-theory (acl2::enable* acl2::arith-equiv-forwarding)))

  (defthm-ifoptdag-to-term-flag
    (defthm ifoptdag-to-term-of-ifoptdag-optimize-node
      (implies (ifoptdag-orderedp ifoptdag)
               (equal (ifoptdag-to-term n (ifoptdag-optimize-node k ifoptdag))
                      (ifoptdag-to-term n ifoptdag)))
      :hints ('(:expand ((:free (ifoptdag) (ifoptdag-to-term n ifoptdag)))))
      :flag ifoptdag-to-term)
    (defthm ifopt-node-to-term-of-ifoptdag-optimize-node
      (implies (ifoptdag-orderedp ifoptdag)
               (equal (ifopt-node-to-term node (ifoptdag-optimize-node k ifoptdag))
                      (ifopt-node-to-term node ifoptdag)))
      :hints ('(:expand ((:free (ifoptdag) (ifopt-node-to-term node ifoptdag)))))
      :flag ifopt-node-to-term)
    (defthm ifoptdag-to-termlist-of-ifoptdag-optimize-node
      (implies (ifoptdag-orderedp ifoptdag)
               (equal (ifoptdag-to-termlist args (ifoptdag-optimize-node k ifoptdag))
                      (ifoptdag-to-termlist args ifoptdag)))
      :hints ('(:expand ((:free (ifoptdag) (ifoptdag-to-termlist args ifoptdag)))))
      :flag ifoptdag-to-termlist))

  (defret len-of-<fn>
    (implies (< (nfix n) (len ifoptdag))
             (equal (len new-ifoptdag) (len ifoptdag)))))



(define ifoptdag-optimize-aux ((n natp) ifoptdag)
  :returns (new-ifoptdag)
  :guard (ifoptdag-orderedp ifoptdag)
  :measure (nfix (- (ifopt-nodes-length ifoptdag) (nfix n)))
  (b* (((when (mbe :logic (zp (- (ifopt-nodes-length ifoptdag) (nfix n)))
                   :exec (<= (ifopt-nodes-length ifoptdag) n)))
        ifoptdag)
       (ifoptdag (ifoptdag-optimize-node n ifoptdag)))
    (ifoptdag-optimize-aux (1+ (lnfix n)) ifoptdag))
  ///
  (defret ifoptdag-orderedp-of-<fn>
    (implies (ifoptdag-orderedp ifoptdag)
             (ifoptdag-orderedp new-ifoptdag)))

  (defret len-of-<fn>
    (equal (len new-ifoptdag)
           (len ifoptdag)))

  (defret ifoptdag-to-term-of-<fn>
    (implies (ifoptdag-orderedp ifoptdag)
             (equal (ifoptdag-to-term k new-ifoptdag)
                    (ifoptdag-to-term k ifoptdag))))

  (defret ifopt-node-to-term-of-<fn>
    (implies (ifoptdag-orderedp ifoptdag)
             (equal (ifopt-node-to-term node new-ifoptdag)
                    (ifopt-node-to-term node ifoptdag))))
  
  (defret ifoptdag-to-termlist-of-<fn>
    (implies (ifoptdag-orderedp ifoptdag)
             (equal (ifoptdag-to-termlist args new-ifoptdag)
                    (ifoptdag-to-termlist args ifoptdag))))
  
  (local (defthm nfix-lemma
           (not (equal n (+ 1 (nfix n))))
           :hints(("Goal" :in-theory (enable nfix)))))
  )

(define ifoptdag-optimize (ifoptdag)
  :returns (new-ifoptdag)
  :guard (ifoptdag-orderedp ifoptdag)
  (ifoptdag-optimize-aux 0 ifoptdag)
  ///
  (defret ifoptdag-orderedp-of-<fn>
    (implies (ifoptdag-orderedp ifoptdag)
             (ifoptdag-orderedp new-ifoptdag)))

  (defret len-of-<fn>
    (equal (len new-ifoptdag)
           (len ifoptdag)))

  (defret ifoptdag-to-term-of-<fn>
    (implies (ifoptdag-orderedp ifoptdag)
             (equal (ifoptdag-to-term k new-ifoptdag)
                    (ifoptdag-to-term k ifoptdag))))

  (defret ifopt-node-to-term-of-<fn>
    (implies (ifoptdag-orderedp ifoptdag)
             (equal (ifopt-node-to-term node new-ifoptdag)
                    (ifopt-node-to-term node ifoptdag))))
  
  (defret ifoptdag-to-termlist-of-<fn>
    (implies (ifoptdag-orderedp ifoptdag)
             (equal (ifoptdag-to-termlist args new-ifoptdag)
                    (ifoptdag-to-termlist args ifoptdag)))))


;; TODO: compile from ifoptdag to term
