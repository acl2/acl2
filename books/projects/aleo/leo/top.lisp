; Leo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO")

(include-book "grammar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ leo
  :parents (aleo::aleo)
  :short "An ACL2 library for the Leo language."
  :long
  (xdoc::topstring
   (xdoc::p
    (xdoc::ahref "https://www.leo-lang.org" "Leo")
    " is "
    (xdoc::ahref "https://provable.com" "Provable")
    "'s high-level language for writing zero-knowledge applications for the "
    (xdoc::ahref "https://aleo.org" "Aleo blockchain")
    ".")
   (xdoc::p
    "This library is work in progress towards
     a formalization of Leo in ACL2,
     along with ACL2 tools for the Leo language.")))
