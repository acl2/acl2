; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "program-and-input-checking")
(include-book "output-checking")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-semantics
  :parents (definition)
  :short "Static semantics of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "The static semantics of Leo defines
     the requirements that must be satisfied
     by the constructs defined in the "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    " in order for the Leo code
     to execute without certain kinds of errors
     (such as accessing variables not in scope,
     applying operators to operands of the wrong types,
     and so on)
     and to be flattened to zero-knowledge circuits.")
   (xdoc::p
    "The static semantics is formalized via
     predicates to check that the constructs satisfy the requirements.")))
