; Solidity Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOLIDITY")

(include-book "sld-refs")
(include-book "boolean-values")
(include-book "boolean-operations")
(include-book "integer-values")
(include-book "integer-operations")
(include-book "values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ solidity
  :parents (acl2::kestrel-books acl2::projects)
  :short "An ACL2 library for Solidity."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently this library contains a formalization of some aspects of
     the Solidity language for "
    (xdoc::ahref "https://ethereum.org" "Ethereum")
    " smart contracts.")
   (xdoc::p
    "In the documentation of this library, the Solidity language documentation
     is referenced and linked as `" xdoc::*sld* "' as a whole.
     Sections of it are referenced and linked
     by appending titles separated by colon,
     e.g. `" xdoc::*sld-types* "' for the `Types' section;
     note that sections are not numbered in " xdoc::*sld* "."))
  :order-subtopics t)
