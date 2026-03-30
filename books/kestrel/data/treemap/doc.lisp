; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "internal/doc")
(include-book "top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This book is used only for the manual. It is not intended to be included by
;; ordinary books.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ treemap
  :parents (data::data-lib)
  :short "A tree-based implementation of ordered finite maps."
  :long
  (xdoc::topstring
    (xdoc::p
      "This library generalizes the finite sets of the "
      (xdoc::seetopic "treeset::treeset" "treeset")
      " library to finite maps. Just as "
      (xdoc::seetopic "treeset::treeset" "treeset")
      "s are isomorphic to "
      (xdoc::seetopic "set::std/osets" "osets")
      ", @(see treemap)s are isomorphic to "
      (xdoc::seetopic "omap::omaps" "omaps")
      ".")
    (xdoc::p
      "The core operations are:")
    (xdoc::ul
      (xdoc::li
        "@(tsee mapp) &mdash; @($O(n)$)")
      (xdoc::li
        "@(tsee keys) &mdash; @($O(n)$)")
      (xdoc::li
        "@(tsee values) &mdash; @($O(\\log(n))$)")
      (xdoc::li
        "@(tsee in) &mdash; @($O(\\log(n))$)")
      (xdoc::li
        "@(tsee lookup) &mdash; @($O(\\log(n))$)")
      (xdoc::li
        "@(tsee submap) &mdash; @($O(m\\log(n/m))$)")
      (xdoc::li
        "@(tsee update) &mdash; @($O(\\log(n))$)")
      (xdoc::li
        "@(tsee delete) &mdash; @($O(\\log(n))$)")
      (xdoc::li
        "@(tsee update*) &mdash; @($O(m\\log(n/m))$)")
      (xdoc::li
        "@(tsee restrict) &mdash; @($O(m\\log(n/m))$)"))
    (xdoc::p
      "(where @($m < n$))."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ implementation
  :parents (treemap)
  :short "Implementation details of @(see treemap)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "The representation of @(see treemap)s is a straightforward
       generalization from "
      (xdoc::seetopic "treeset::treeset" "treeset")
      "s. Node values are replaced with
       key/value pairs, and all invariants (i.e., @(tsee bstp) and @(tsee
       heapp)) apply just to the key values.")
    (xdoc::p
      "See @(see treeset::implementation) for an overview of the underlying
       treap data structure."))
  :order-subtopics t)
