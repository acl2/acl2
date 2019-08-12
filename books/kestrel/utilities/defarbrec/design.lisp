; Arbitrary Recursion Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/event-macros/xdoc-constructors" :dir :system)

; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)
; (depends-on "kestrel/utilities/design-notes/defarbrec.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-design-notes
 defarbrec
 "res/kestrel-utilities-design-notes/defarbrec.pdf"
 :correspondences
  ("@($f$) corresponds to the program-mode function."
   "@($a(\\overline{x})$) corresponds to @('test<x1,...,xn>')"
   "@($b(\\overline{x})$) corresponds to @('base<x1,...,xn>')."
   "@($c(\\overline{x},y)$) corresponds to @('combine<x1,...,xn,y>')."
   "@($d_i(\\overline{x})$) corresponds to @('update-xi<x1,...,xn>')."
   "@($d_i^{k}(\\overline{x})$) corresponds to @('update*-xi k x1 ... xn')."
   "@($t$) corresponds to @('terminates')."
   "@($\\phi$) corresponds to @(tsee nfix)."
   "@($\\epsilon_t$) corresponds to @('terminates-witness')."
   "@($\\nu$) corresponds to @('measure')."
   "@($\\hat{f}$) corresponds to the logic-mode function."))
