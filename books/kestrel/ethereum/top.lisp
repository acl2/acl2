; Ethereum Library
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

; the order of the following INCLUDE-BOOKs determines
; the order of the subtopics of the ETHEREUM topic below:
(include-book "basics")
(include-book "crypto")
(include-book "rlp")
(include-book "hex-prefix")
(include-book "mmp-trees")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ethereum
  :parents (acl2::kestrel-books acl2::projects)
  :short "A library for Ethereum."
  :long
  (xdoc::topapp
   (xdoc::p
    "Currently this library contains a formal model of some aspects of
     the <a href=\"https://ethereum.org\">Ethereum</a> ``world computer''.
     It is expected that this library will be extended with more
     Ethereum-related formalizations and tools.")
   (xdoc::p
    "This library is based on the following sources:")
   (xdoc::ul
    (xdoc::li
     "The <a href=\"https://github.com/ethereum/wiki/wiki\">Ethereum Wiki</a>,
      referenced as `[Wiki]' in the documentation of this library.")
    (xdoc::li
     "The BYZANTIUM VERSION 69351d5 of
      the <a href=\"https://github.com/ethereum/yellowpaper\">Ethereum
      Yellow Paper</a>,
      referenced as `[YP]' in the documentation of this library.
      Sections, appendices, and equations are referenced
      by appending their designations separated by colon,
      e.g.
      `[YP:3]' references Section 3,
      `[YP:6.1]' references Section 6.1,
      `[YP:B]' references Appendix B, and
      `[YP:(4)]' references Equation (4)."))
   (xdoc::p
    "These square-bracketed references may be used
     as nouns or parenthentically."))
  :order-subtopics t)
