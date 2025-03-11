; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "defs")
(include-book "binary-tree")
(include-book "jenkins-hash")
(include-book "total-order")
(include-book "bst-order")
(include-book "bst")
(include-book "heap-order")
(include-book "heap")
(include-book "set")
(include-book "in")
(include-book "cardinality")
(include-book "rotate")
(include-book "subset")
(include-book "pick-a-point")
(include-book "double-containment")
(include-book "insert")
(include-book "join")
(include-book "delete")
(include-book "split")
(include-book "union")
(include-book "intersect")
(include-book "diff")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; It is not recommended to include this book. Instead, the defs.lisp book
;; should be included and then any additional theorems books as needed (perhaps
;; only locally included.)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ set
  :parents (acl2::kestrel-books)
  :short "A tree-based implementation of finite sets."
  :long
  (xdoc::topstring
    (xdoc::p
      "This implementation of finite sets offers practically logarithmic
       worst-case performance for the core set operations (@(tsee in), @(tsee
       insert), @(tsee delete)) while also insisting on a canonical internal
       structure which allows @(tsee equal) to represent true set
       equivalence.")
    (xdoc::section
      "Differences from @(csee set::std/osets)"
      (xdoc::p
        "This library closely follows @(see set::std/osets). The first major
         difference, from an external user-perspective, is performance. Below
         are the practical worst-case complexities of core operations:")
      ;; TODO: technically, these also scale multiplicatively with the size of
      ;;   the elements, since bst< and heap< are O(n). If we stored the hash
      ;;   values in the nodes, heap< could be O(1) average case. If we
      ;;   switched orders, this could be a nice improvement (since bst< is
      ;;   called more than heap<).
      (xdoc::ul
        (xdoc::li
          "@(tsee setp) &mdash; @($O(n^2)$) (Note: the current implementation
           is inefficient. This should eventually be @($O(n)$) once we
           introduce a more efficient binary search tree property check via an
           @(tsee mbe).)")
        (xdoc::li
          "@(tsee in) &mdash; @($O(\\log(n))$)")
        (xdoc::li
          "@(tsee insert) &mdash; @($O(\\log(n))$)")
        (xdoc::li
          "@(tsee delete) &mdash; @($O(\\log(n))$)")
        (xdoc::li
          "@(tsee union) &mdash; @($O(n\\log(m/n))$)")
        (xdoc::li
          "@(tsee intersect) &mdash; @($O(n\\log(m/n))$)")
        (xdoc::li
          "@(tsee diff) &mdash; @($O(n\\log(m/n))$)"))
      (xdoc::p
        "The other major difference is in how one iterates over or traverses a
         set. In @(see set::std/osets), @(tsee std::head) provides the minimal
         element of a nonempty set, and @(tsee std::tail) provides the rest.
         For treesets, @(tsee head) provides the hash-maximal element of a
         nonempty set. Instead of @(tsee std::tail), we have @(tsee left) and
         @(tsee right), providing two disjoint subsets with all elements less
         than and all elements greater than the head, respectively.")
      (xdoc::p
        "In practice, the @(tsee std::head)/@(tsee head) values are typically
         considered arbitrary elements of the set (and this perspective is
         encouraged). So the only meaningful difference is the tree-traversal
         with @(tsee left) and @(tsee right) in contrast to the flat list
         traversal of @(tsee std::tail). Alternatively, one may use @(tsee
         to-list) to get a flat list to iterate over more easily.")))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ implementation
  :parents (set)
  :short "Implementation details of @(see set)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "Here we describe the internal representation of sets.  Users of the
       library should not depend on these details, opting instead to use the
       \"primitive\" operators abstractly.")
    (xdoc::p
      "Sets are represented internally as treaps (= \"tree\" + \"heap\").
       Treaps are binary search trees with an additional max heap constraint
       (see @(tsee bst-p) and @(tsee heapp), respectively).  Crucially, the max
       heap property is maintained with respect to a different order than that
       which is used for the binary search tree property.")
    (xdoc::p
      "The binary search tree property uses the @(tsee bst<) order, which is
       just a wrapper around @(tsee <<). The binary search tree property is
       what delivers logarithmic average-case complexity of our basic
       operations.")
    (xdoc::p
      "The max heap property uses the new @(tsee heap<) total order. This
       ensures that the tree has a canonical structure and that the tree is
       practically balanced. Treaps are only expected to be balanced in
       practice if the heap order and the binary search tree order are largely
       uncorrelated. That is, the heap order appears \"random\" with respect to
       the binary search tree order. To accomplish this, the @(tsee heap<)
       order is based on a non-cryptographic hash of its arguments.")
    (xdoc::section
      "References"
      (xdoc::ul
        (xdoc::li
          (xdoc::a "https://www.cs.cmu.edu/~scandal/papers/treaps-spaa98.pdf"))
        (xdoc::li
          (xdoc::a "https://en.wikipedia.org/wiki/Treap")))))
  :order-subtopics t)
