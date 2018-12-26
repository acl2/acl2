; APT Partial Evaluation Transformation -- Design Notes
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/xdoc/constructors" :dir :system)

; (depends-on "design-notes/restrict.pdf")
; (depends-on "design-notes/notation.pdf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc parteval-design
  :parents (design-notes parteval)
  :short "Design notes for the APT partial evaluation transformation."
  :long
  (xdoc::topapp
   (xdoc::p
    "The design of the transformation is described in
     <a href='res/apt/parteval.pdf'>these notes</a>,
     which use <a href='res/apt/notation.pdf'>this notation</a>.")
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
