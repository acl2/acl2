; APT (Automated Program Transformations) Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/constructors" :dir :system)

; (depends-on "design-notes/casesplit.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; documentation topic for the design notes,
; which are in design-notes/casesplit.pdf:

(defxdoc casesplit-design

  :parents (design-notes casesplit)

  :short "Design notes for the APT case splitting transformation."

  :long

  (xdoc::topstring

   (xdoc::p
    "The design of the transformation is described in "
    (xdoc::a :href "res/kestrel-apt-design-notes/casesplit.pdf" "these notes")
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
     "@($c_k$) corresponds to @('condk'), for @($1 \leq k \leq p$).")
    (xdoc::li
     "@($f{}f'_k$) corresponds to @('thmk'), for @($0 \leq k \leq p$).")
    (xdoc::li
     "@($h_k$) corresponds to @('hypk'), for @($0 \leq k \leq p$).")
    (xdoc::li
     "@($f_k$) corresponds to @('newk'), for @($0 \leq k \leq p$).")
    (xdoc::li
     "@($H_k$) corresponds to @(':thmk-hyps'), for @($0 \leq k \leq p$).")
    (xdoc::li
     "@($GC_k$) correponds to @(':condk-guard'), for @($1 \leq k \leq p$).")
    (xdoc::li
     "@($Gf_k$) correponds to @(':newk-guard'), for @($0 \leq k \leq p$).")
    (xdoc::li
     "@($f'$) corresponds to @('new').")
    (xdoc::li
     "@($f{}f'$) corresponds to @('old-to-new')."))

   (xdoc::p
    "The transformation does not yet handle
     the case in which @($f$) returns multiple results (i.e. @($m > 1$)).")))
