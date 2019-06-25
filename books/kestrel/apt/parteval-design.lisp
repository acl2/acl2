; APT Partial Evaluation Transformation -- Design Notes
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

(defxdoc parteval-design
  :parents (design-notes parteval)
  :short "Design notes for the APT partial evaluation transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The design of the transformation is described in "
    (xdoc::a :href "res/kestrel-apt-design-notes/parteval.pdf" "these notes")
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
     "Each @($\\widetilde{y}_j$) corresponds to @('cj').")
    (xdoc::li
     "@($f'$) corresponds to @('new').")
    (xdoc::li
     "@($f{}f'$) corresponds to @('old-to-new')."))))
