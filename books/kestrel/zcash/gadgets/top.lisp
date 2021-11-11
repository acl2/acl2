; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "proof-support")

(include-book "a-3-1-1-spec")
(include-book "a-3-1-2-spec")
(include-book "a-3-1-3-spec")
(include-book "a-3-1-4-spec")
(include-book "a-3-1-5-spec")

(include-book "a-3-2-1-spec")
(include-book "a-3-2-2-spec")

(include-book "a-3-3-1-spec")
(include-book "a-3-3-1-proof")
(include-book "a-3-3-1-alt-proof")

(include-book "a-3-3-2-spec")
(include-book "a-3-3-3-spec")
(include-book "a-3-3-4-spec")
(include-book "a-3-3-5-spec")
(include-book "a-3-3-6-spec")
(include-book "a-3-3-7-spec")
(include-book "a-3-3-8-spec")
(include-book "a-3-3-9-spec")

(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ zcash-gadgets
  :parents (zcash)
  :short "A collection of Zcash gadgets, with formal specifications and proofs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('.txt') files in this directory contain
     ACL2 representations of R1CS and tree gadgets,
     generated via the @('bellman') and @('librustzcash') Rust libraries.
     The R1CS and tree gadgets are functionally equivalent,
     but the tree gadgets have more structure than the R1CS gadgets;
     the additional structure has been derived
     by modifying the Rust code that generates the gadgets
     to output some additional information.")
   (xdoc::p
    "The @('.lisp') files in this directory contain
     ACL2 specifications and proofs of the gadgets.
     The specifications are generally thin wrappers of
     existing specifications in the Zcash formalization one directory up,
     or in the elliptic curve library.")))
