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
 parteval
 "res/kestrel-apt-design-notes/parteval.pdf"
 :additional-parents (design-notes)
 :correspondences
  ("@($f$) corresponds to @('old')."
   "Each @($\\widetilde{y}_j$) corresponds to @('cj')."
   "@($f'$) corresponds to @('new')."
   "@($f{}f'$) corresponds to @('old-to-new')."))
