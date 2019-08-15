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

; (depends-on "design-notes/casesplit.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-design-notes
 casesplit
 "res/kestrel-apt-design-notes/casesplit.pdf"
 :additional-parents (design-notes)
 :correspondences
  ("@($f$) corresponds to @('old')."
   "@($c_k$) corresponds to @('condk'), for @($1 \\leq k \\leq p$)."
   "@($f{}f'_k$) corresponds to @('thmk'), for @($0 \\leq k \\leq p$)."
   "@($h_k$) corresponds to @('hypk'), for @($0 \\leq k \\leq p$)."
   "@($f_k$) corresponds to @('newk'), for @($0 \\leq k \\leq p$)."
   "@($H_k$) corresponds to @(':thmk-hyps'), for @($0 \\leq k \\leq p$)."
   "@($GC_k$) correponds to @(':condk-guard'), for @($1 \\leq k \\leq p$)."
   "@($Gf_k$) correponds to @(':newk-guard'), for @($0 \\leq k \\leq p$)."
   "@($f'$) corresponds to @('new')."
   "@($f{}f'$) corresponds to @('old-to-new').")
  :additional-doc
  ((xdoc::p
    "The transformation does not yet handle
     the case in which @($f$) returns multiple results (i.e. @($m > 1$)).")))
