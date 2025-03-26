; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "language/top")
(include-book "json/top")
(include-book "transformations/top")
(include-book "test/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ yul
  :parents (acl2::kestrel-books acl2::projects)
  :short "An ACL2 library for Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "Yul is a programming language
     used as an intermediate language
     in the compilation of "
    (xdoc::ahref "https://ethereum.org" "Ethereum")
    " smart contracts written in the Solidity language.
     However, Yul is designed to be more general than Solidity,
     and may find additional uses.")
   (xdoc::p
    "This ACL2 library for Yul is being developed
     to provide a formalization of Yul in ACL2,
     verified Yul code transformations,
     and tools related to Yul and ACL2.
     This library is work in progress.")
   (xdoc::p
    "Yul is currently documented as part of the "
    (xdoc::ahref "https://docs.soliditylang.org/en/latest/"
                 "Solidity documentation")
    ", precisely in the "
    (xdoc::ahref "https://docs.soliditylang.org/en/latest/yul.html"
                 "`Yul' section")
    ".")
   (xdoc::p
    "In the documentation of this ACL2 library,
     the Yul documentation (part of the Solidity documentation)
     is referenced as `[Yul]`;
     subsections of it are referenced by appending
     their titles separated by colons, e.g.
     `[Yul: Specification of Yul: Scoping Rules]`.
     These square-bracketed references may be used
     as nouns or parenthetically.")
   (xdoc::p
    "Since some aspects of Yul are described
     in part of the Solidity documentation that is not [Yul],
     we also reference (the rest of) the Solidity documentation,
     which we do as `[Solidity]' and `[Solidity: ...]',
     similarly to how we reference the Yul documentation proper."))
  :order-subtopics t)
