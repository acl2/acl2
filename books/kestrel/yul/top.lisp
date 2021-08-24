; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "concrete-syntax")
(include-book "abstract-syntax")
(include-book "static-semantics")
(include-book "dynamic-semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ yul
  :parents (acl2::kestrel-books acl2::projects)
  :short "An ACL2 library for Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "Yul is a programming language,
     which is being used as an intermediate language
     in the compilation of "
    (xdoc::ahref "https://ethereum.org" "Ethereum")
    " smart contracts written in in the Solidity language.
     However, Yul is designed to be more general than Solidity,
     and may find additional uses soon.")
   (xdoc::p
    "This ACL2 library for Yul is being developed
     to provide a formalization of Yul in ACL2,
     as well as tools related to Yul and ACL2.
     This library is work in progress.")
   (xdoc::p
    "Yul is currently documented as part of the "
    (xdoc::ahref "https://docs.soliditylang.org/en/latest/"
                 "Solidity documentation")
    ", precisely in the "
    (xdoc::ahref "https://docs.soliditylang.org/en/latest/yul.html"
                 "`Yul' section of the Solidity documentation")
    ". However, since Yul is designed to be more general than Solidity,
     it is possible that eventually it may have its own documentation.")
   (xdoc::p
    "In the documentation of this ACL2 library,
     the Yul documentation (part of the Solidity documentation)
     is referenced as `[Yul]`;
     subsections of it are referenced by appending
     by appending their titles separated by colons,  e.g.
     `[Yul: Specification of Yul: Scoping Rules]`.
     These square-bracketed references may be used
     as nouns or parenthetically."))
  :order-subtopics t)
