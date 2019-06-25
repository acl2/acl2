; APT Domain Restriction Transformation -- Design Notes
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/constructors" :dir :system)

; (depends-on "design-notes/restrict.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; documentation topic for the design notes,
; which are in design-notes/restrict.pdf:

(defxdoc restrict-design

  :parents (design-notes restrict)

  :short "Design notes for the APT domain restriction transformation."

  :long

  (xdoc::topstring

   (xdoc::p
    "The design of the transformation is described in "
    (xdoc::a :href "res/kestrel-apt-design-notes/restrict.pdf" "these notes")
    ", which use "
    (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "this notation")
    ".")

   (xdoc::p
    "The correspondence between the design notes and the reference documentation
     is the following:")

   (xdoc::ul
    (xdoc::li
     "@($f$) corresponds to @('old').")
    (xdoc::li
     "@($e(\\overline{x})$) corresponds to the body of @('old'),
      when @('old') is not recursive.")
    (xdoc::li
     "When @('old') is recursive,
      the notes use
      a single non-recursive branch @($b(\\overline{x})$)
      controlled by @($a(\\overline{x})$)
      and a single recursive branch
      @($c(\\overline{x},f(\\overline{d}(\\overline{x})))$)
      controlled by the negation of @($a(\\overline{x})$).
      This is a representative recursive structure,
      but the transformation handles
      multiple non-recursive and recursive branches.
      In this representative recursive structure,
      @($d_i(\\overline{x})$)
      corresponds to @('update-xi<x1,...,xn>')
      and the negation of @($a(\\overline{x})$)
      corresponds to @('context<x1,...,xn>').")
    (xdoc::li
     "@($R$) corresponds to @('(lambda (x1 ... xn) restriction<x1,...,xn>)').")
    (xdoc::li
     "@($R{}d$) corresponds to @(':restriction-of-rec-calls').")
    (xdoc::li
     "@($G{}R$) corresponds to @(':restriction-guard').")
    (xdoc::li
     "@($f'$) corresponds to @('new').")
    (xdoc::li
     "@($f{}f'$) corresponds to @('old-to-new')."))))
