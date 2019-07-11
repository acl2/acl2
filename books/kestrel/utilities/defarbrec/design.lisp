; Arbitrary Recursion Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)
; (depends-on "kestrel/utilities/design-notes/defarbrec.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defarbrec-design

  :parents (defarbrec)

  :short "Design notes for @(tsee defarbrec)."

  :long

  (xdoc::topstring

   (xdoc::p
    "The design of @(tsee defarbrec) is described in "
    (xdoc::a :href "res/kestrel-utilities-design-notes/defarbrec.pdf"
      "these notes")
    ", which use "
    (xdoc::a :href "res/kestrel-general-design-notes/notation.pdf"
      "this notation")
    ".")

   (xdoc::p
    "The correspondence between the design notes and the reference documentation
     is the following:")
   (xdoc::ul
    (xdoc::li
     "@($f$) corresponds to the program-mode function.")
    (xdoc::li
     "@($a(\\overline{x})$) corresponds to @('test<x1,...,xn>')")
    (xdoc::li
     "@($b(\\overline{x})$) corresponds to @('base<x1,...,xn>').")
    (xdoc::li
     "@($c(\\overline{x},y)$) corresponds to @('combine<x1,...,xn,y>').")
    (xdoc::li
     "@($d_i(\\overline{x})$) corresponds to @('update-xi<x1,...,xn>').")
    (xdoc::li
     "@($d_i^{k}(\\overline{x})$) corresponds to @('update*-xi k x1 ... xn').")
    (xdoc::li
     "@($t$) corresponds to @('terminates').")
    (xdoc::li
     "@($\\phi$) corresponds to @(tsee nfix).")
    (xdoc::li
     "@($\\epsilon_t$) corresponds to @('terminates-witness').")
    (xdoc::li
     "@($\\nu$) corresponds to @('measure').")
    (xdoc::li
     "@($\\hat{f}$) corresponds to the logic-mode function."))))
