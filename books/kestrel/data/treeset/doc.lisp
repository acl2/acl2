; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "internal/doc")
(include-book "top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This book is used only for the manual. It is not intended to be included by
;; ordinary books.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ treeset
  :parents (data::data-lib)
  :short "A tree-based implementation of ordered finite sets."
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
      ;;   the elements, since << is O(n). Same for the hash.
      (xdoc::ul
        (xdoc::li
          "@(tsee setp) &mdash; @($O(n)$)")
        (xdoc::li
          "@(tsee in) &mdash; @($O(\\log(n))$)")
        (xdoc::li
          "@(tsee insert) &mdash; @($O(\\log(n))$)")
        (xdoc::li
          "@(tsee delete) &mdash; @($O(\\log(n))$)")
        (xdoc::li
          "@(tsee union) &mdash; @($O(m\\log(n/m))$)")
        (xdoc::li
          "@(tsee intersect) &mdash; @($O(m\\log(n/m))$)")
        (xdoc::li
          "@(tsee diff) &mdash; @($O(m\\log(n/m))$)"))
      (xdoc::p
        "(where @($m < n$)).")
      (xdoc::p
        "For the binary functions, when @($n$) and @($m$) are approximately the
         same, this results in an effective @($O(n)$) complexity. When @($m$)
         is much smaller than @($n$), the complexity is effectively
         @($O(\\log(n))$).")
      (xdoc::p
        "The other major difference is in how one iterates over the elements of
         a set. In @(see set::std/osets), one uses @(tsee set::head) and
         @(tsee set::tail). While there are corresponding functions on
         @(see treeset)s (@(tsee min) and @(tsee tail)), it would be
         inefficient to use them for iteration. Instead, one should use an
         @(see iterator). This requires an initial step to create the
         @(see iterator) (via @(tsee iter)), but once one has an iterator, one
         can call @(tsee value) and @(tsee next) as you would @(tsee set::head)
         and @(tsee set::tail). If you are going to iterate over the entire
         set (i.e. you don't need to ``exit early''), you could also use
         @('to-oset'). All these methods of iteration take @($O(n)$) time.")))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ implementation
  :parents (treeset)
  :short "Implementation details of @(see treeset)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "Here we describe the internal representation of sets. Users of the
       library should not depend on these details, opting instead to use the
       \"primitive\" operators abstractly. If you require a theorem which is
       not yet provided, it is recommended to take a proof over
       @(csee set::std/osets) and apply it to @(see treeset)s via the
       isomorphism.")
    (xdoc::p
      "Sets are represented internally as treaps (= \"tree\" + \"heap\").
       Treaps are binary search trees with an additional max heap constraint
       (see @(tsee bstp) and @(tsee heapp), respectively).  Crucially, the max
       heap property is maintained with respect to a different order than that
       which is used for the binary search tree property.")
    (xdoc::p
      "The binary search tree property uses the @(tsee <<) order. The binary
       search tree property is what delivers logarithmic average-case
       complexity of our basic operations.")
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
          (xdoc::ahref "https://www.cs.cmu.edu/~scandal/papers/treaps-spaa98.pdf"
                       "https://www.cs.cmu.edu/~scandal/papers/treaps-spaa98.pdf"))
        (xdoc::li
          (xdoc::ahref "https://en.wikipedia.org/wiki/Treap"
                       "https://en.wikipedia.org/wiki/Treap")))))
  :order-subtopics t)
