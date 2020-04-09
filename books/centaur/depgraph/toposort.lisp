; Basic Dependency Graphs
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "DEPGRAPH")
(include-book "std/util/define" :dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(include-book "std/typed-lists/cons-listp" :dir :system)
(include-book "misc/hons-help" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/testing/assert" :dir :system))

(local (in-theory (disable acl2::alist-keys-member-hons-assoc-equal)))

(local (defthm hons-assoc-equal-under-iff
         (iff (hons-assoc-equal a x)
              (member-equal a (alist-keys x)))
         :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

(define topologically-ordered-p-aux (nodes graph seen)
  :returns (mv ordered-p seen)
  :parents (topologically-ordered-p)
  (b* (((when (atom nodes))
        (mv t seen))
       (node1 (car nodes))
       (deps1 (cdr (hons-get node1 graph)))
       ((unless (fal-all-boundp deps1 seen))
        (mv nil seen))
       (seen  (hons-acons node1 t seen)))
    (topologically-ordered-p-aux (cdr nodes) graph seen)))

(define topologically-ordered-p
  :parents (depgraph)
  :short "@(call topologically-ordered-p) determines if a list of @('nodes') is
topologically ordered with respect to a @('graph')."
  ((nodes "List of nodes to check.")
   (graph "Alist that binds nodes to their dependents."))
  :returns ordered-p
  :long "<p>We check that, for every node @('a') in the list of @('nodes'), the
dependents of @('a') come before @('a').</p>

<p>This is a weak check in a couple of ways: we don't require that the
@('nodes') are unique, and we don't check that every node in the graph is among
the @('nodes').</p>

<p>We can determine if the nodes are topologically sorted in linear time,
assuming constant-time hashing.</p>"

  (b* ((seen          (len nodes))
       ((mv ans seen) (topologically-ordered-p-aux nodes graph seen)))
    (fast-alist-free seen)
    ans))

(define dependency-chain-p
  :parents (depgraph)
  :short "@(call dependency-chain-p) determines if a list of @('nodes') indeed
follows a set of dependencies in @('graph')."

  ((nodes "List of nodes to check.")
   (graph "Alist that binds nodes to their dependents."))
  :returns depchain-p

  :long "<p>Say @('nodes') is @('(n1 n2 ... nk)').  We check that @('n2') is a
dependent of @('n1'), @('n3') is a dependent of @('n2'), and so forth.  This is
mainly used as a sanity check on any loops we claim to have found.</p>"

  (b* (((when (atom nodes))
        t)
       ((when (atom (cdr nodes)))
        t)
       (node1 (first nodes))
       (node2 (second nodes))
       (deps1 (cdr (hons-get node1 graph))))
    (and (hons-member-equal node2 deps1)
         (dependency-chain-p (cdr nodes) graph))))

(define toposort-measure (queue seen graph)
  (declare (xargs :guard t))
  (two-nats-measure (len (set-difference-equal (alist-keys graph) (alist-keys seen)))
                    (len queue)))

(define toposort-aux
  :parents (toposort)
  :short "Main depth-first topological sorting routine."

  ((queue "All the nodes we have left to explore.  Initially this is
           just @('(alist-keys graph').")
   (seen  "Fast alist that binds nodes to their <i>status</i> (see below).")
   (graph "Fast alist that binds nodes to the lists of their dependents.
           Remains constant as we recur."))
  :returns
  (mv (successp "We return successfully only if we're able to explore all of the
                 nodes in the queue without finding a loop.")
      (seen     "Final @('seen') fast alist, from which we can extract the
                 topological order or a loop."))
  :measure (toposort-measure queue seen graph)
  :verify-guards nil

  :long "<p>The <i>status</i> of each node is either:</p>

<ul>
<li>unbound, if we haven't started it yet, or bound to</li>
<li>@(':started') if we are currently exploring its dependents, or</li>
<li>@(':finished') if we are done exploring it.</li>
</ul>

<p>On success, a topologically sorted list of nodes can be extracted from
@('seen') by looking at the @(':finished') nodes using @(see
extract-topological-order).  On failure, the loop we found can be extracted
from @('seen') by looking at the @(':started') nodes with @(see
extract-topological-loop).</p>"

  (b* (((when (atom queue))
        (mv t seen))

       (orig-seen-al seen) ;; stupid termination hack

       (node   (car queue))
       (status (hons-get node seen))
       ((when (eq (cdr status) :finished))
        ;; We've already looked at this node and dealt with it, so just keep
        ;; going to the other nodes.
        (toposort-aux (cdr queue) seen graph))

       ((when status)
        ;; I originally wrote (eq (cdr status) :started) here, but to ensure
        ;; termination it is useful to treat anything that is bound to anything
        ;; other than :finished as if it's bound to :started, so now we just
        ;; check if there is any binding at all.

        ;; We found a loop!  Add this node to seen even though it's already
        ;; there, since that way we can see where to stop in our loop
        ;; extraction code.
        (mv nil (hons-acons node :started seen)))

       ;; Else, we haven't seen the node yet.  Mark it as seen and go explore
       ;; its dependents.
       (deps-look (hons-get node graph))
       ((unless deps-look)
        ;; The graph has no binding for this node, so the node doesn't exist.
        ;; Checking for this is important for termination.
        (er hard? 'toposort-aux "No binding for ~x0." node)
        (toposort-aux (cdr queue) seen graph))

       (seen (hons-acons node :started seen))
       (deps (cdr deps-look))
       ((mv deps-okp seen) (toposort-aux deps seen graph))
       ((unless deps-okp) (mv nil seen))

       ;; Successfully explored the dependents, so mark the node as done and
       ;; keep going with the queue.
       (seen (hons-acons node :finished seen))
       ((unless (mbt (o< (toposort-measure (cdr queue) seen graph)
                         (toposort-measure queue orig-seen-al graph))))
        ;; Can't get here
        (mv nil seen)))
    (toposort-aux (cdr queue) seen graph))

  :prepwork
  ((local (defthm len-sd-cons-right-1
            (implies (member-equal a y)
                     (equal (len (set-difference-equal x (cons a y)))
                            (len (set-difference-equal x y))))
            :hints(("Goal" :induct (len x)))))

   (local (defthm len-sd-cons-right-2
            (implies (not (member-equal a y))
                     (< (len (set-difference-equal x (cons a y)))
                        (+ 1 (len (set-difference-equal x y)))))
            :rule-classes ((:rewrite) (:linear))
            :hints(("Goal" :induct (len x)))))

   (local (defthm len-sd-cons-right-3
            (implies (and (not (member-equal a y))
                          (member-equal a x))
                     (< (len (set-difference-equal x (cons a y)))
                        (len (set-difference-equal x y))))
            :rule-classes ((:rewrite) (:linear))
            :hints(("Goal" :induct (len x)))))

   (local (defthm equal-of-len-sd-cons-right
            (equal (equal (len (set-difference-equal x (cons a y)))
                          (len (set-difference-equal x y)))
                   (if (or (not (member-equal a x))
                           (member-equal a y))
                       t
                     nil))
            :hints(("Goal" :induct (len x)))))

   (local (defthm len-sd-cons-right-strong
            (equal (< (len (set-difference-equal x (cons a y)))
                      (len (set-difference-equal x y)))
                   (if (and (member-equal a x)
                            (not (member-equal a y)))
                       t
                     nil))
            :hints(("Goal" :induct (len x)))))

   (local (defthm len-sd-cons-right-weak
            (<= (len (set-difference-equal x (cons a y)))
                (len (set-difference-equal x y)))
            :rule-classes ((:rewrite) (:linear))
            :hints(("Goal" :induct (len x)))))

   (local (defthm len-sd-when-subset
            (implies (subsetp-equal y z)
                     (<= (len (set-difference-equal x z))
                         (len (set-difference-equal x y))))
            :rule-classes ((:rewrite) (:linear))
            :hints(("Goal" :induct (len x)))))

   (local (defthm len-sd-cons-right-when-subset
            (implies (and (member-equal a x)
                          (not (member-equal a y))
                          (subsetp-equal y z))
                     (< (len (set-difference-equal x (cons a z)))
                        (len (set-difference-equal x y))))
            :rule-classes ((:rewrite) (:linear))
            :hints(("Goal" :induct (len x)))))

   (local (defthm len-sd-cons-right-when-subset-2
            ;; Same as above, but alternate hyp order for free-var matching
            (implies (and (subsetp-equal y z)
                          (member-equal a x)
                          (not (member-equal a y)))
                     (< (len (set-difference-equal x (cons a z)))
                        (len (set-difference-equal x y))))
            :rule-classes ((:rewrite) (:linear))))

   (local (in-theory (enable toposort-measure))))

  ///
  (local (defthm l0
           (implies (member-equal k (alist-keys seen))
                    (member-equal k (alist-keys (mv-nth 1 (toposort-aux queue seen graph)))))))

  (local (defthm l1
           (subsetp-equal (alist-keys seen)
                          (alist-keys (mv-nth 1 (toposort-aux queue seen graph))))
           :hints((set-reasoning))))

  (local (defthm l2
           (subsetp-equal (alist-keys seen)
                          (alist-keys (mv-nth 1 (toposort-aux queue (cons (cons key :started) seen) graph))))
           :rule-classes ((:forward-chaining
                           :trigger-terms ((toposort-aux queue (cons (cons key :started) seen) graph))))
           :hints((set-reasoning))))

  (verify-guards toposort-aux)

  (defthm cons-listp-of-toposort-aux
    (implies (cons-listp seen)
             (cons-listp (mv-nth 1 (toposort-aux queue seen graph))))
    :hints(("Goal" :in-theory (disable ;consp-when-member-equal-of-cons-listp
                                       ;cons-listp-when-subsetp-equal
                                       ))))

  (defthm subsetp-equal-of-alist-keys-of-toposort-aux
    (implies (subsetp-equal (alist-keys seen) (alist-keys graph))
             (subsetp-equal (alist-keys (mv-nth 1 (toposort-aux queue seen graph)))
                            (alist-keys graph))))

  (defthm toposort-aux-consp-on-failure
    (implies (not (mv-nth 0 (toposort-aux queue seen graph)))
             (consp (mv-nth 1 (toposort-aux queue seen graph))))))



(define extract-topological-order ((seen cons-listp) acc)
  :parents (toposort)
  :short "Extract the topological order from successful applications of @(see
toposort-aux)."
  :returns nodelist
  (cond ((atom seen)
         acc)
        ((eq (cdar seen) :finished)
         (extract-topological-order (cdr seen) (cons (caar seen) acc)))
        (t
         ;; this was a :started node, so ignore it
         (extract-topological-order (cdr seen) acc)))
  ///

  (defthm true-listp-of-extract-topological-order
    (implies (true-listp acc)
             (true-listp (extract-topological-order seen acc))))

  (encapsulate
    ()
    (local (defthm l0
             (implies (member-equal a acc)
                      (member-equal a (extract-topological-order seen acc)))))

    (local (defthm l1
             (implies (and (member-equal a (extract-topological-order seen acc))
                           (not (member-equal a acc)))
                      (member-equal a (alist-keys seen)))))

    (defthm subsetp-equal-of-extract-topological-order
      (subsetp-equal (extract-topological-order seen acc)
                     (append (alist-keys seen)
                             acc))
      :hints((set-reasoning))))


  "<p>Now we prove a completeness theorem that shows extract-topological-order
   will get us at least everything that was in the queue.</p>"

  (local (defun eto (seen)
           ;; non-tail-recursive version of extract-topological-order, for reasoning
           (cond ((atom seen)
                  nil)
                 ((eq (cdar seen) :finished)
                  (cons (caar seen) (eto (cdr seen))))
                 (t
                  (eto (cdr seen))))))

  (local (defthm extract-topological-order-is-eto
           (equal (extract-topological-order seen acc)
                  (revappend (eto seen) acc))
           :hints(("Goal" :in-theory (enable extract-topological-order)))))

  (local (defthm member-equal-eto-when-finished
           (implies (equal (cdr (hons-get name seen)) :finished)
                    (member-equal name (eto seen)))))

  (local (defthm toposort-aux-grows-eto
           (implies (member-equal node (eto seen))
                    (member-equal node (eto (mv-nth 1 (toposort-aux queue seen graph)))))
           :hints(("Goal" :in-theory (enable toposort-aux)))))

  (local (defthm member-equal-eto-when-in-queue
           (implies (and (mv-nth 0 (toposort-aux queue seen graph))
                         (subsetp-equal queue (alist-keys graph))
                         (member-equal node queue))
                    (member-equal node (eto (mv-nth 1 (toposort-aux queue seen graph)))))
           :hints(("Goal"
                   :induct (toposort-aux queue seen graph)
                   :in-theory (enable toposort-aux)))))

  (local (defthm queue-is-subset-of-eto
           (implies (and (mv-nth 0 (toposort-aux queue seen graph))
                         (subsetp-equal queue (alist-keys graph)))
                    (subsetp-equal queue (eto (mv-nth 1 (toposort-aux queue seen graph)))))
           :hints((acl2::witness :ruleset (acl2::subsetp-witnessing)))))

  (defthm extract-topological-order-includes-queue
    (implies (and (mv-nth 0 (toposort-aux queue seen graph))
                  (subsetp-equal queue (alist-keys graph)))
             (subsetp-equal queue (extract-topological-order (mv-nth 1 (toposort-aux queue seen graph)) nil))))


  "<p>And a uniqueness theorem that shows the extracted elements are at least
   duplicate-free.</p>"

  (local (defthm seen-remain-seen
           (implies (member-equal node (alist-keys seen))
                    (member-equal node (alist-keys (mv-nth 1 (toposort-aux queue seen graph)))))
           :hints(("Goal" :in-theory (enable toposort-aux)))))

  (local (defthm only-unseen-can-become-finished
           (implies (and (member-equal node (alist-keys seen))
                         (not (member-equal node (eto seen))))
                    (not (member-equal node (eto (mv-nth 1 (toposort-aux queue seen graph))))))
           :hints(("Goal"
                   :induct (toposort-aux queue seen graph)
                   :do-not '(generalize fertilize)
                   :in-theory (enable toposort-aux)))))

  (local (defthm eto-members-are-seen
           (implies (member-equal node (eto seen))
                    (member-equal node (alist-keys seen)))))

  (local (defthm stupid-consequence
           (implies (not (member-equal node (alist-keys seen)))
                    (not (member-equal
                          node
                          (eto (mv-nth 1 (toposort-aux deps (cons (cons node :started) seen) graph))))))
           :hints(("goal"
                   :use ((:instance only-unseen-can-become-finished
                                    (queue deps)
                                    (seen (cons (cons node :started) seen))))))))

  (local (defthm toposort-aux-grows-eto-without-dupes
           (implies (no-duplicatesp-equal (eto seen))
                    (no-duplicatesp-equal (eto (mv-nth 1 (toposort-aux queue seen graph)))))
           :hints(("Goal"
                   :do-not '(generalize fertilize)
                   :in-theory (enable toposort-aux)))))

  (defthm no-duplicatesp-equal-of-extract-topological-order
    (implies (no-duplicatesp-equal (extract-topological-order seen nil))
             (no-duplicatesp-equal (extract-topological-order (mv-nth 1 (toposort-aux queue seen graph)) nil)))))



(define extract-topological-loop
  :parents (toposort)
  :short "Extract the topological loop from failed applications of @(see
toposort-aux)."

  ((seen      "A copy of the seen alist that we're recurring through."
              cons-listp)
   (stop      "The node that we looped back to, so we know when to stop (and won't
               include nodes that we were exploring before getting to the looping
               node, i.e., the \"handle\" of a \"lasso\").")
   (acc       "Accumulator for nodes that really are in the loop.")
   (full-seen "Fast copy of the full seen alist so we can tell if nodes were finished or not."))
  :returns
  (final-acc "List of all the nodes in the loop.")
  (cond ((atom seen)
         (prog2$ (er hard? 'extract-topological-loop
                     "Should never hit the end of seen!")
                 acc))
        ((eq (cdar seen) :started)
         (b* ((name      (caar seen))
              (finishedp (eq (cdr (hons-get name full-seen)) :finished))
              ;; This node is only part of the loop if we saw it but didn't
              ;; finish it.
              (acc       (if finishedp acc (cons name acc))))
           (if (hons-equal name stop)
               acc
             (extract-topological-loop (cdr seen) stop acc full-seen))))
        (t
         (extract-topological-loop (cdr seen) stop acc full-seen)))
  ///
  (defthm true-listp-of-extract-topological-loop
    (implies (true-listp acc)
             (true-listp (extract-topological-loop seen stop acc full-seen))))

  (local (defthm l0
           (implies (member-equal a acc)
                    (member-equal a (extract-topological-loop seen stop acc full-seen)))))

  (local (defthm l1
           (implies (and (member-equal a (extract-topological-loop seen stop acc full-seen))
                         (not (member-equal a acc)))
                    (member-equal a (alist-keys seen)))))

  (defthm subsetp-equal-of-extract-topological-loop
    (subsetp-equal (extract-topological-loop seen stop acc full-seen)
                   (append (alist-keys seen)
                           acc))
    :hints((set-reasoning))))


(define toposort
  :parents (depgraph)
  :short "General-purpose, depth-first topological sort for dependency graphs."

  ((graph "Alist that binds nodes to the lists of nodes they (directly) depend
           on.  See below."))
  :returns
  (mv (successp "True when the graph is loop-free and hence can be topologically
                 sorted, or @('nil') when there is a loop."
                booleanp :rule-classes :type-prescription)
      (result   "On success: a list of nodes in topological order, guaranteed
                 equivalent to @('(alist-keys graph)') and in dependency order.
                 On failure: a list of nodes that have a dependency loop."
                true-listp :rule-classes :type-prescription))

  :long "<p>We implement a depth-first topological sort of the graph.  If the
graph is loop-free, this produces @('(mv t nodes)'), where @('nodes') are set
equivalent to @('(alist-keys graph)') and are in dependency order.  Otherwise
the graph has loops; we will find some loop and return @('(mv nil loop)'),
where @('loop') is a list of nodes such as @('(a b c a)'), where @('a') depends
on @('b'), which depends on @('c'), which depends on @('a').</p>

<p>The graph is as described in @(see depgraph), but note:</p>

<ul>

<li>@('graph') is expected to be complete, i.e., every node that is ever listed
as a dependent should be bound in @('graph'); we will <b>cause a hard error</b>
if this is not the case.</li>

<li>@('graph') should (typically) not contain nodes that depend on themselves;
any such nodes form trivial self-loops and will cause topological ordering to
fail.</li>

</ul>

<h3>Usage Notes</h3>

<p>In rare cases you may actually be able to directly use this to sort some
structures in a dependency order.  But most of the time, we imagine that you
will need to:</p>

<ol>
<li>Extract a dependency graph in the expected \"toposort format\",</li>
<li>Run toposort to get a topological ordering (or find a loop), and finally</li>
<li>Reorder your data according to the ordering that has been produced.</li>
</ol>

<p>It might sometimes be more efficient to write custom topological sorts for
various data structures.  But that's a lot of work.  We think that the
translation steps are usually cheap enough that in most cases, the above
strategy is the easiest way to topologically sort your data.</p>"

  :prepwork
  ((local (defthm consp-of-first-when-alistp
            (implies (alistp x)
                     (equal (consp (car x))
                            (if x t nil)))))

   (local (defthm consp-of-first-when-cons-listp
            (implies (cons-listp x)
                     (equal (consp (car x))
                            (consp x))))))

  (b* (((with-fast graph))
       (keys               (alist-keys graph))
       ((mv successp seen) (toposort-aux keys (len keys) graph))
       ((unless successp)
        (b* ((loop (extract-topological-loop (cdr seen) (caar seen) (list (caar seen)) seen)))
          (fast-alist-free seen)
          ;; These errors should never occur unless there's a programming error.
          ;; BOZO eventually prove them away.
          (or (dependency-chain-p loop graph)
              (er hard? 'toposort "failed to produce a valid dependency chain!"))
          (or (hons-equal (car loop) (car (last loop)))
              (er hard? 'toposort "failed to produce a loop!"))
          (mv nil loop)))
       (nodes (extract-topological-order seen nil)))
    (fast-alist-free seen)
    (or (topologically-ordered-p nodes graph)
        (er hard? 'toposort "failed to produce a topological ordering!"))
    (mv t nodes))
  ///

  #|| If the below theorems fail, this may be useful for debugging:

  (add-untranslate-pattern
  (mv-nth '1 (TOPOSORT-AUX (ALIST-KEYS GRAPH)
  (LEN (ALIST-KEYS GRAPH))
  GRAPH))
  <FINAL-SEEN>)

  ||#

  (local (make-event
          (let* ((aux  `(toposort-aux (alist-keys graph)
                                      (len (alist-keys graph))
                                      graph))
                 (seen `(mv-nth 1 ,aux)))
            `(defthm l1
               (implies (mv-nth 0 (toposort graph))
                        (subsetp-equal (mv-nth 1 (toposort graph))
                                       (alist-keys graph)))
               :hints(("Goal"
                       :in-theory (disable subsetp-equal-of-extract-topological-order)
                       :use ((:instance subsetp-equal-of-extract-topological-order
                                        (seen ,seen)
                                        (acc nil)))))))))

  (local (defthm l2
           (implies (and (consp x)
                         (cons-listp x))
                    (set-equiv (cons (caar x) (alist-keys (cdr x)))
                                (alist-keys x)))))

  (local (make-event
          (let* ((aux  `(toposort-aux (alist-keys graph)
                                      (len (alist-keys graph))
                                      graph))
                 (seen `(mv-nth 1 ,aux)))
            `(defthm l3
               (implies (not (mv-nth 0 (toposort graph)))
                        (subsetp-equal (mv-nth 1 (toposort graph))
                                       (alist-keys graph)))
               :hints(("Goal"
                       :in-theory (disable subsetp-equal-of-extract-topological-loop)
                       :use ((:instance subsetp-equal-of-extract-topological-loop
                                        (seen (cdr ,seen))
                                        (stop (caar ,seen))
                                        (acc  (list (caar ,seen)))
                                        (full-seen ,seen))))
                      (acl2::witness :ruleset (acl2::subsetp-witnessing)))))))


  "<p>We always know, regardless of success, that the nodes we return in our
   ordering or in our loop must be members of the graph:</p>"

  (defthm subsetp-equal-of-toposort
    (subsetp-equal (mv-nth 1 (toposort graph))
                   (alist-keys graph))
    :hints(("Goal"
            :in-theory (disable toposort)
            :cases ((mv-nth 0 (toposort graph))))))


  (local (defthm completeness-of-toposort
           (implies (mv-nth 0 (toposort graph))
                    (subsetp-equal (alist-keys graph)
                                   (mv-nth 1 (toposort graph))))
           :hints(("Goal"
                   :in-theory (disable extract-topological-order-includes-queue)
                   :use ((:instance extract-topological-order-includes-queue
                                    (queue (alist-keys graph))
                                    (seen (len (alist-keys graph)))
                                    (graph graph)))))))

  "<p>On success, we know something even better, namely that our ordering
   contains <i>all</i> of the nodes of the graph:</p>"

  (defthm toposort-set-equiv
    (implies (mv-nth 0 (toposort graph))
             (set-equiv (mv-nth 1 (toposort graph))
                         (alist-keys graph)))
    :hints(("Goal" :in-theory (e/d (set-equiv)
                                   (toposort)))))


  "<p>And incidentally, on success, our ordering contains no duplicates:</p>"

  (defthm no-duplicatesp-equal-of-toposort
    (implies (mv-nth 0 (toposort graph))
             (no-duplicatesp-equal (mv-nth 1 (toposort graph))))
    :hints(("Goal"
            :in-theory (e/d (extract-topological-order)
                            (no-duplicatesp-equal-of-extract-topological-order))
            :use ((:instance no-duplicatesp-equal-of-extract-topological-order
                             (queue (alist-keys graph))
                             (seen  (len (alist-keys graph)))))))))


(local
 (progn

;; Some basic unit tests.  It's okay if these particular orders change, as long
;; as they're still valid.



   (assert!
    (mv-let (successp order)
      (toposort '((a . (b c d))
                  (b . (c d e))
                  (c . (d e))
                  (d . (e))
                  (e . nil)))
      (and successp
           (equal order '(e d c b a)))))


   (assert!
    (mv-let (successp loop)
      (toposort '((a . (b c d))
                  (b . (c d e))
                  (c . (d e))
                  (d . (e))
                  (e . (a))))
      (and (not successp)
           (equal loop '(a b c d e a)))))

   (assert!
    (mv-let (successp loop)
      (toposort  '((a . (b c d))
                   (b . (e f g))
                   (e . nil)
                   (c . (g))
                   (d . nil)
                   (g . (f a))
                   (f . nil)))
      (and (not successp)
           (equal loop '(a b g a)))))

   (assert!
    (mv-let (successp order)
      (toposort  '((a . (b c d))
                   (b . (e f g))
                   (e . nil)
                   (c . (g))
                   (d . nil)
                   (g . (f d))
                   (f . nil)))
      (and successp
           (equal order '(e f d g b c a)))))))
