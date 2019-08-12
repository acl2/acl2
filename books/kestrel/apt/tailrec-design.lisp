; APT (Automated Program Transformations) Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/event-macros/xdoc-constructors" :dir :system)

; (depends-on "design-notes/tailrec.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-design-notes
 tailrec
 "res/kestrel-apt-design-notes/tailrec.pdf"
 :additional-parents (design-notes)
 :correspondences
  ("@($f$) corresponds to @('old')."
   "@($a(\\overline{x})$) corresponds to @('test<x1,...,xn>')."
   "@($b(\\overline{x})$) corresponds to @('base<x1,...,xn>')."
   "@($c(\\overline{x})$) corresponds to @('nonrec<x1,...,xn>')."
   "@($d_i(\\overline{x})$) corresponds to @('update-xi<x1,...,xn>')."
   "@($D$) corresponds to @('domain')."
   "@($*$) corresponds to @('combine')."
   "@($D{}b$) corresponds to @(':domain-of-base')."
   "@($D{}c$) corresponds to @(':domain-of-nonrec')."
   "@($D\\!*$) corresponds to @(':domain-of-combine')."
   "@($D\\!*'$) corresponds to @(':domain-of-combine-uncond')."
   "@($A{}S{}C$) corresponds to @(':combine-associativity')."
   "@($A{}S{}C'$) corresponds to @(':combine-associativity-uncond')."
   "@($L{}I$) corresponds to @(':combine-left-identity')."
   "@($R{}I$) corresponds to @(':combine-right-identity')."
   "@($G{}D$) corresponds to @(':domain-guard')."
   "@($G\\!*$) corresponds to @(':combine-guard')."
   "@($G{}D{}c$) corresponds to @(':domain-of-nonrec-when-guard')."
   "@($f'$) corresponds to @('new')."
   "@($\\tilde{f}$) corresponds to @('wrapper')."
   "@($f{}f'$) corresponds to @('old-to-new')."
   "@($f{}\\tilde{f}$) corresponds to @('old-to-wrapper').")
  :additional-doc
  ((xdoc::p
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
