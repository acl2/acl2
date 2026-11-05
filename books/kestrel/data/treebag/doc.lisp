; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This book is used only for the manual. It is not intended to be included by
;; ordinary books.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ treebag
  :parents (data::data-lib)
  :short "A tree-based implementation of finite multisets."
  :long
  (xdoc::topstring
    (xdoc::p
      "A @(see treebag) is a finite multiset, or bag: a collection of values
       in which a value may occur any number of times. It is represented as
       a "
      (xdoc::seetopic "acl2::treemap" "treemap")
      " from each value occurring in the bag to its number of occurrences,
       which is always positive.")
    (xdoc::p
      "The core operations are:")
    (xdoc::table_
      (xdoc::tr
        (xdoc::td "@(tsee bagp)")
        (xdoc::td "@($O(n)$)"))
      (xdoc::tr
        (xdoc::td "@(tsee count)")
        (xdoc::td "@($O(\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee in)")
        (xdoc::td "@($O(\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee cardinality)")
        (xdoc::td "@($O(n)$)"))
      (xdoc::tr
        (xdoc::td "@(tsee subbag)")
        (xdoc::td "@($O(m\\log(n/m))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee insert), @(tsee insert-many)")
        (xdoc::td "@($O(\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee delete), @(tsee delete-many)")
        (xdoc::td "@($O(\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee sum)")
        (xdoc::td "@($O(m\\log(n/m))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee union)")
        (xdoc::td "@($O(m\\log(n/m))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee intersect)")
        (xdoc::td "@($O(m\\log(n/m))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee diff)")
        (xdoc::td "@($O(m\\log(n/m))$)")))
    (xdoc::p
      "(where @($m$) and @($n$) are numbers of distinct elements, and @($m
       \\leq n$) for @(tsee subbag), @(tsee sum), @(tsee union), @(tsee
       intersect), and @(tsee diff))."))
  :order-subtopics t)
