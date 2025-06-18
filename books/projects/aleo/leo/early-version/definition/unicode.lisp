; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unicode-characters
  :parents (concrete-syntax)
  :short "Unicode characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Leo is written in Unicode.
     Here we introduce a notion of Unicode characters,
     used to formalize the concrete syntax of Leo.")
   (xdoc::p
    "In the future, ideally we should make use of
     a more general ACL2 library for Unicode,
     of which the community books have an initial version
     (which could and should be expanded)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod unicode
  :short "Fixtype of Unicode characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the set of Unicode code points.")
   (xdoc::p
    "We wrap the code point into a one-component product type
     for better encapsulation and abstraction.
     We use an invariant to restrict the number to the prescribed range.")
   (xdoc::p
    "This fixtype has currently the same definition
     as @(tsee char) in the abstract syntax formalization.
     However, in the future we might change the representation of @(tsee char)
     (e.g. by keeping track of escapes,
     or by treating ASCII and non-ASCII differently for more readability),
     while the fixtype defined here is expected to stay
     isomorphic to the natural numbers that represent Unicode code points."))
  ((codepoint nat :reqfix (if (<= codepoint #x10ffff) codepoint 0)))
  :require (<= codepoint #x10ffff)
  :tag :unicode
  :pred unicodep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist unicode-list
  :short "Fixtype of lists of Unicode characters."
  :elt-type unicode
  :true-listp t
  :elementp-of-nil nil
  :pred unicode-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection unicode-list->codepoint-list ((x unicode-listp))
  :returns (cpoints nat-listp)
  :short "Lift @(tsee unicode->codepoint) to lists."
  (unicode->codepoint x)
  ///
  (fty::deffixequiv unicode-list->codepoint-list))
