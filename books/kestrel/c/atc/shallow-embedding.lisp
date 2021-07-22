; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integer-operations")
(include-book "arrays")
(include-book "conditional-expressions")
(include-book "let-designations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-shallow-embedding
  :parents (atc-implementation)
  :short "Shallow embedding of C in ACL2 for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 representation of C constructs,
     which ATC recognizes and translates to C,
     constitutes a shallow embedding of C in ACL2.
     In contrast, the "
    (xdoc::seetopic "atc-abstract-syntax" "abstract syntax")
    ", "
    (xdoc::seetopic "atc-static-semantics" "static semantics")
    ", and "
    (xdoc::seetopic "atc-dynamic-semantics" "dynamic semantics")
    " constitute a deep embedding of C in ACL2.
     The two are not separate:
     the deep embedding, specifically the dynamic semantics,
     includes the shallow embedding.")
   (xdoc::p
    "The file where this XDOC topic appears
     can be included by tools, such as APT transformations,
     that need to operate on the ACL2 representations of the C constructs,
     without having to include all of ATC."))
  :order-subtopics t)
