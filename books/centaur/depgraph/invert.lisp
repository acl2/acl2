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
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/testing/assert-bang" :dir :system))

(define invert-inner-loop
  :parents (invert)
  :short "Add a parent dependency to each of its children."
  ((parent   "A node in the original graph.")
   (children "List of nodes that parent depends on, in the original graph.")
   (acc      "New, inverted graph we are building.  Fast alist."))
  :returns
  (acc "Extended by adding parent as a dependency of each child.")
  (b* (((when (atom children))
        acc)
       (child1       (car children))
       (curr-parents (cdr (hons-get child1 acc)))
       (new-parents  (cons parent curr-parents))
       (acc          (hons-acons child1 new-parents acc)))
    (invert-inner-loop parent (cdr children) acc))
  ///
  (defthm invert-inner-loop-correct
    (iff (member par (cdr (hons-assoc-equal child (invert-inner-loop parent children orig-alist))))
         (or (member par (cdr (hons-assoc-equal child orig-alist)))
             (and (equal par parent)
                  (member child children))))))

(define invert-outer-loop
  :parents (invert)
  :short "Add all parent dependencies to all children."
  ((nodes "The parent nodes we still need to process.  Originally the @(see
           alist-keys) of @('graph').  We use this instead of recurring down
           @('graph') to properly avoid shadowed pairs.")
   (graph "The graph we're inverting, remains constant.")
   (acc   "The new, inverted graph we're building."))
  :returns
  (acc "Extended by adding parents for each child for the remaining nodes.")
  (b* (((when (atom nodes))
        acc)
       (parent1   (car nodes))
       (children1 (cdr (hons-get parent1 graph)))
       (acc       (invert-inner-loop parent1 children1 acc)))
    (invert-outer-loop (cdr nodes) graph acc))
  ///
  (defthm invert-outer-loop-when-atom
    (implies (atom nodes)
             (equal (invert-outer-loop nodes graph acc)
                    acc)))

  (local (defthm l1
           (let ((new-acc (invert-outer-loop nodes graph acc)))
             (implies (member par (cdr (hons-assoc-equal child acc)))
                      (member par (cdr (hons-assoc-equal child new-acc)))))))

  (local (defthm l2
           (let ((new-acc (invert-outer-loop nodes graph acc)))
             (implies (and (member par nodes)
                           (member child (cdr (hons-assoc-equal par graph))))
                      (member par (cdr (hons-assoc-equal child new-acc)))))))

  (defthm invert-outer-loop-correct
    (let ((new-acc (invert-outer-loop nodes graph acc)))
      (iff (member par (cdr (hons-assoc-equal child new-acc)))
           (or (member par (cdr (hons-assoc-equal child acc)))
               (and (member par nodes)
                    (member child (cdr (hons-assoc-equal par graph)))))))))

(define invert
  :parents (depgraph)
  :short "Invert a dependency graph."
  ((graph "Alist that binds nodes to the list of nodes they (directly) depend on."))
  :returns
  (inverted-graph "<b>Fast</b> alist that binds nodes to the list of nodes
                   that (directly) depend on them.")

  :long "<p>See the discussion of graph representation in @(see depgraph).
This basically changes the directions of arrows in the graph.  For instance, if
our original graph was:</p>

@({
      A ----->  B ---> C        ((A . (B))
                |      |         (B . (C D))
                |      |         (C . (D))
                v      |         (D . NIL))
                D <----+
})

<p>Then inverting the graph just changes the directions of all the arrows,
e.g., we would have:</p>

@({
      A <-----  B <--- C        ((A . NIL)
                ^      ^         (B . (A))
                |      |         (C . (B))
                |      |         (D . (C B)))
                D -----+
})

<p>We are careful to ensure that every node is bound in the resulting graph,
e.g., we'll have a binding for @('A') even though it is a leaf node.</p>"

  (b* ((nodes (alist-keys graph))
       (acc
        ;; Kind of silly, but ensures that all parents are bound in the
        ;; result, even if they don't have any children.
        (make-fast-alist (pairlis$ nodes nil)))
       (acc
        ;; Main part of the processing, extend all children with their
        ;; parents.
        (with-fast-alist graph
          (invert-outer-loop nodes graph acc))))
    ;; The resulting acc typically has many duplicates, so shrink it to make it
    ;; nicer.
    (fast-alist-clean acc))
  ///
  (local (defthm l0
           (not (cdr (hons-assoc-equal child (pairlis$ nodes nil))))
           :hints(("Goal" :in-theory (enable pairlis$)))))

  (defthm invert-correct
    (iff (member parent (cdr (hons-assoc-equal child (invert graph))))
         (member child (cdr (hons-assoc-equal parent graph))))
    :hints(("Goal"
            :in-theory (disable invert-outer-loop-correct)
            :use ((:instance invert-outer-loop-correct
                   (par   parent)
                   (child child)
                   (nodes (alist-keys graph))
                   (acc   (make-fast-alist (pairlis$ (alist-keys graph) nil)))))))))

(local (progn

(assert!
 (equal (fast-alist-free
         (invert '((a . (b))
                   (b . (c d))
                   (c . (d))
                   (d . nil))))
        '((a . ())
          (b . (a))
          (c . (b))
          (d . (c b)))))

))
