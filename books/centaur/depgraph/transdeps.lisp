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
(include-book "std/osets/top" :dir :system)
(include-book "misc/hons-help" :dir :system)
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "centaur/misc/osets-witnessing" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/alists/top" :dir :system))

(local (set::use-osets-reasoning))

(local (in-theory (disable cardinality
                           set::expand-cardinality-of-union
                           set::expand-cardinality-of-difference)))

(local (defthm cardinalty-<-by-proper-subset
              (iff (< (cardinality x) (cardinality y))
                   (if (subset x y)
                       (not (subset y x))
                     (hide (< (cardinality x) (cardinality y)))))
              :hints (("goal" :expand ((:free (x) (hide x)))))))

(define transdeps-allnodes (graph)
  :parents (transdeps)
  :short "Overapproximation of all of the nodes in the graph."
  :long "<p>Never executed.  We just use this for termination.  It's possibly
an overapproximation because of shadowed pairs in the graph.</p>"
  :returns (nodes setp)
  (mergesort (append (alist-keys graph)
                     (flatten (alist-vals graph)))))

(define transdeps-direct-for-node (node graph)
  :returns (deps setp)
  :parents (transdeps)
  :short "Memoized.  Get the set of dependencies for a single node."
  (mbe :logic
       (mergesort (cdr (hons-get node graph)))
       :exec
       (b* ((look (cdr (hons-get node graph))))
         (if (setp look)
             look
           (mergesort look))))
  ///
  (memoize 'transdeps-direct-for-node)

  (local (defthm l0
           (implies (member a (cdr (hons-assoc-equal node graph)))
                    (member a (flatten (alist-vals graph))))
           :hints(("Goal" :induct (len graph)))))

  (defthm transdeps-direct-for-node-in
    (implies (in a (transdeps-direct-for-node node graph))
             (in a (transdeps-allnodes graph)))
    :hints(("Goal" :in-theory (enable transdeps-allnodes))))

  (defthm transdeps-direct-for-node-subset
    (subset (transdeps-direct-for-node node graph)
            (transdeps-allnodes graph))
    :hints(("Goal" :in-theory (enable transdeps-allnodes)))))


(define transdeps-direct-for-nodes ((nodes setp) graph)
  :returns (deps setp)
  :parents (transdeps)
  :short "Get the set of direct dependencies for a set of nodes."
  :verify-guards nil
  (if (emptyp nodes)
      nil
    (union (transdeps-direct-for-node (head nodes) graph)
           (transdeps-direct-for-nodes (tail nodes) graph)))
  ///
  (verify-guards transdeps-direct-for-nodes)

  (defthm transdeps-direct-for-nodes-in
    (implies (in a (transdeps-direct-for-nodes nodes graph))
             (in a (transdeps-allnodes graph))))

  (defthm transdeps-direct-for-nodes-subset
    (subset (transdeps-direct-for-nodes nodes graph)
            (transdeps-allnodes graph))))


(define transdeps-aux
  :parents (transdeps)
  :short "Main algorithm for collecting transitive dependencies."

  ((curr setp "Nodes we're currently exploring.")
   (prev setp "Nodes we've previously explored.")
   (orig setp "Nodes that we were originally looking for.")
   (graph))
  :guard (and (subset curr (union orig (transdeps-allnodes graph)))
              (subset prev (union orig (transdeps-allnodes graph))))
  :returns (deps setp)

  :long "<p>We are trying to compute the set of all nodes that are necessary
for curr and prev.  At each step, we assume that all of prev's dependencies are
already found within (curr U prev), so we are really only looking for \"new\"
dependencies of the nodes in curr.  If all of these new are already in curr U
prev, we have reached a fixed point and we can stop.  Otherwise, we need to
explore these new dependencies, but we can expand @('prev') with everything in
@('curr') so we know not to look there anymore.</p>

<p>The list of orig nodes is a termination hack of sorts.  Without this, we
would need to do something to ensure that the curr/prev lists don't contain
nodes that aren't found anywhere in the graph.  By also knowing what the
original nodes were, we can include them in the measure.</p>"

  :verify-guards nil
  :measure (cardinality (difference (union orig (transdeps-allnodes graph))
                                    (union curr prev)))

  (b* ((new       (transdeps-direct-for-nodes curr graph))
       (curr+prev (union curr prev))

       ;; Termination helper.  Never gets executed.
       ((unless (mbt (subset curr+prev (union orig (transdeps-allnodes graph)))))
        curr+prev)

       ;; Fixed point reached.  Return the set we've built so far.
       ((when (subset new curr+prev))
        curr+prev))

    ;; New nodes added.  Continue adding their dependencies.
    (transdeps-aux (difference new curr+prev) curr+prev orig graph))

  ///
  (verify-guards transdeps-aux)

  (defthm transdeps-aux-in
    (implies (and (in a (transdeps-aux curr prev orig graph))
                  (subset curr (union orig (transdeps-allnodes graph)))
                  (subset prev (union orig (transdeps-allnodes graph))))
             (in a (union orig (transdeps-allnodes graph)))))

  (defthm transdeps-aux-subset
    (implies (and (subset curr (union orig (transdeps-allnodes graph)))
                  (subset prev (union orig (transdeps-allnodes graph))))
             (subset (transdeps-aux curr prev orig graph)
                     (union orig (transdeps-allnodes graph))))))


(define transdeps
  :parents (depgraph)
  :short "Compute the transitive dependencies for a list of nodes."
  ((nodes "The list of nodes to compute dependencies for.")
   (graph "Alist that binds nodes to the lists of nodes they (directly) depend
           on.  See below."))
  :returns
  (deps true-listp "The ordered set of nodes that @('nodes') depend on.  Always
                    includes @('nodes') themselves.")

  :long "<p>We implement a general-purpose, transitive closure operation for
dependency graph reachability.  We determine all nodes in the @('graph') that
are reachable from the starting @('nodes').</p>

<p>After calling this function you may wish to use @(see transdeps-free) to
clear out the relevant memo tables.</p>"

  (let ((orig (mergesort nodes)))
    (with-fast-alist graph
      (transdeps-aux orig nil orig graph)))
  ///
  (more-returns (deps setp))

  (defthm transdeps-subset
    (subset (transdeps nodes graph)
            (union (mergesort nodes) (transdeps-allnodes graph)))
    :hints(("Goal"
            :in-theory (disable transdeps-aux-subset)
            :use ((:instance transdeps-aux-subset
                   (curr (mergesort nodes))
                   (prev nil)
                   (orig (mergesort nodes))
                   (graph graph)))))))


(define transdeps-free ()
  :parents (transdeps)
  :short "Free memo tables associated with @(see transdeps)."
  (progn$
   (clear-memoize-table 'transdeps-direct-for-node)
   nil))
