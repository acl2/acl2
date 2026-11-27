; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "internal/doc")
(include-book "cursor/internal/doc")
(include-book "top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This book is used only for the manual. It is not intended to be included by
;; ordinary books.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tmap
  :parents (data::data-lib)
  :short "A tree-based implementation of ordered finite maps."
  :long
  (xdoc::topstring
    (xdoc::p
      "This library generalizes the finite sets of the "
      (xdoc::seetopic "acl2::tset" "tset")
      " library to finite maps. Just as "
      (xdoc::seetopic "acl2::tset" "tset")
      "s are isomorphic to "
      (xdoc::seetopic "set::std/osets" "osets")
      ", @(see tmap)s are isomorphic to "
      (xdoc::seetopic "omap::omaps" "omaps")
      ".")
    (xdoc::p
      "The core operations are:")
    (xdoc::table_
      (xdoc::tr
        (xdoc::td "@(tsee mapp)")
        (xdoc::td "@($O(n)$)"))
      (xdoc::tr
        (xdoc::td "@(tsee keys)")
        (xdoc::td "@($O(n)$)"))
      (xdoc::tr
        (xdoc::td "@(tsee values)")
        (xdoc::td "@($O(n\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee in)")
        (xdoc::td "@($O(\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee lookup)")
        (xdoc::td "@($O(\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee submap)")
        (xdoc::td "@($O(m\\log(n/m))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee update)")
        (xdoc::td "@($O(\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee delete)")
        (xdoc::td "@($O(\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee update*)")
        (xdoc::td "@($O(m\\log(n/m))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee restrict)")
        (xdoc::td "@($O(m\\log(n/m))$)")))
    (xdoc::p
      "(where @($m < n$)).")
    (xdoc::p
      "To iterate over the entries of a map, use a @(see cursor). In "
      (xdoc::seetopic "omap::omaps" "omaps")
      ", one uses @(tsee omap::head) and @(tsee omap::tail). While there are
       corresponding functions on @(see tmap)s (@(tsee min) and @(tsee
       delete)), it would be inefficient to use them for iteration. Instead,
       create a @(see cursor) with @(tsee seek-min), then read each entry with
       @(tsee entry-key) and @(tsee entry-val) (or @(tsee entry)) and move on
       with @(tsee next). To walk the other way, start from @(tsee seek-max)
       and use @(tsee prev). If you are going to iterate over the entire map
       (i.e. you don't need to ``exit early''), you could also use @(tsee
       to-omap). All these methods of iteration take @($O(n)$) time."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ implementation
  :parents (tmap)
  :short "Implementation details of @(see tmap)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "The representation of @(see tmap)s is a straightforward
       generalization from "
      (xdoc::seetopic "acl2::tset" "tset")
      "s. Node values are replaced with
       key/value pairs, and all invariants (i.e., @(tsee bstp) and @(tsee
       heapp)) apply just to the key values.")
    (xdoc::p
      "See @(see tset::implementation) for an overview of the underlying
       treap data structure."))
  :order-subtopics t)
