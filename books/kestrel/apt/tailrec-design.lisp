; APT Tail Recursion Transformation -- Design Notes
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/xdoc/constructors" :dir :system)

; (depends-on "design-notes/tailrec.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; documentation topic for the design notes,
; which are in design-notes/tailrec.pdf:

(defxdoc tailrec-design

  :parents (design-notes tailrec)

  :short "Design notes for the APT tail recursion transformation."

  :long

  (xdoc::topstring

   (xdoc::p
    "The design of the transformation is described in
     <a href='res/apt/tailrec.pdf'>these notes</a>,
     which use "
    (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "this notation")
    ".")

   (xdoc::p
    "The correspondence between the design notes and the reference documentation
     is the following:")

   (xdoc::ul
    (xdoc::li
     "@($f$) corresponds to @('old').")
    (xdoc::li
     "@($a(\\overline{x})$) corresponds to @('test<x1,...,xn>').")
    (xdoc::li
     "@($b(\\overline{x})$) corresponds to @('base<x1,...,xn>').")
    (xdoc::li
     "@($c(\\overline{x})$) corresponds to @('nonrec<x1,...,xn>').")
    (xdoc::li
     "@($d_i(\\overline{x})$) corresponds to @('update-xi<x1,...,xn>').")
    (xdoc::li
     "@($D$) corresponds to @('domain').")
    (xdoc::li
     "@($*$) corresponds to @('combine').")
    (xdoc::li
     "@($D{}b$) corresponds to @(':domain-of-base').")
    (xdoc::li
     "@($D{}c$) corresponds to @(':domain-of-nonrec').")
    (xdoc::li
     "@($D\\!*$) corresponds to @(':domain-of-combine').")
    (xdoc::li
     "@($D\\!*'$) corresponds to @(':domain-of-combine-uncond').")
    (xdoc::li
     "@($A{}S{}C$) corresponds to @(':combine-associativity').")
    (xdoc::li
     "@($A{}S{}C'$) corresponds to @(':combine-associativity-uncond').")
    (xdoc::li
     "@($L{}I$) corresponds to @(':combine-left-identity').")
    (xdoc::li
     "@($R{}I$) corresponds to @(':combine-right-identity').")
    (xdoc::li
     "@($G{}D$) corresponds to @(':domain-guard').")
    (xdoc::li
     "@($G\\!*$) corresponds to @(':combine-guard').")
    (xdoc::li
     "@($G{}D{}c$) corresponds to @(':domain-of-nonrec-when-guard').")
    (xdoc::li
     "@($f'$) corresponds to @('new').")
    (xdoc::li
     "@($\\tilde{f}$) corresponds to @('wrapper').")
    (xdoc::li
     "@($f{}f'$) corresponds to @('old-to-new').")
    (xdoc::li
     "@($f{}\\tilde{f}$) corresponds to @('old-to-wrapper')."))

   (xdoc::p
    "The decomposition of the recursive branch
     described in the reference documentation
     does not handle all the cases described in the design notes
     about the decomposition of the old function.")

   (xdoc::p
    "The transformation requires the term @('base<x1,...,xn>')
     to be ground when the variant is @(':monoid') or @(':monoid-alt').
     The reason for this restriction is to avoid, for now,
     generating and using the function @($\\beta$) defined in the design notes.
     Thus, with the @(':monoid') or @(':monoid-alt') variants,
     the transformation is always in the special case of a ground base value
     described in the design notes.")

   (xdoc::p
    "The transformation does not yet handle
     left and right identity independently,
     whose independent treatment is covered in the design notes.")))
