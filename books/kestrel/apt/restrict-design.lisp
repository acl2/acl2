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

; (depends-on "design-notes/restrict.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-design-notes
 restrict
 "res/kestrel-apt-design-notes/restrict.pdf"
 :additional-parents (design-notes)
 :correspondences
  ("@($f$) corresponds to @('old')."
   "@($e(\\overline{x})$) corresponds to the body of @('old'),
    when @('old') is not recursive."
   "When @('old') is recursive,
    the notes use
    a single non-recursive branch @($b(\\overline{x})$)
    controlled by @($a(\\overline{x})$)
    and a single recursive branch
    @($c(\\overline{x},f(\\overline{d}(\\overline{x})))$)
    controlled by the negation of @($a(\\overline{x})$).
    This is a representative recursive structure,
    but the transformation handles
    multiple non-recursive and recursive branches,
    and also recursive functions that occur in their termination theorem.
    In this representative recursive structure,
    @($d_i(\\overline{x})$)
    corresponds to @('update-xi<x1,...,xn>')
    and the negation of @($a(\\overline{x})$)
    corresponds to @('context<x1,...,xn>')."
   "@($R$) corresponds to @('(lambda (x1 ... xn) restriction<x1,...,xn>)')."
   "@($R{}d$) corresponds to @(':restriction-of-rec-calls')."
   "@($G{}R$) corresponds to @(':restriction-guard')."
   "@($f'$) corresponds to @('new')."
   "@($f{}f'$) corresponds to @('old-to-new')."))
