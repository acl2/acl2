; Ethereum Library
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/xdoc-constructors" :dir :system)

; the order of the following INCLUDE-BOOKs determines
; the order of the subtopics of the ETHEREUM topic below:
(include-book "basics")
(include-book "rlp")
(include-book "hex-prefix")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc ethereum

  :parents (acl2::kestrel-books acl2::project)

  :short "A library for Ethereum."

  :long

  (xdoc::topapp

   (xdoc::p
    "Currently this library contains a formal model of some aspects of
     the <a href=\"https://ethereum.org\">Ethereum</a> ``world computer''.
     It is expected that this library will be extended with more
     Ethereum-related formalizations and tools.")

   (xdoc::p
    "This library is based on
     the <a href=\"https://github.com/ethereum/wiki/wiki\">Ethereum Wiki</a>
     (`Wiki' for short),
     in particular the BYZANTIUM VERSION e94ebda 2018-06-05 of
     the <a href=\"https://github.com/ethereum/yellowpaper\">Ethereum
     Yellow Paper</a>
     (`YP' for short).
     In the documentation of this library,
     (sub)sections and equations of YP are referenced
     by appending their (possibly dotted or parenthesized) numbers
     to `YP:',
     e.g.
     `YP:3' references Section 3 (not page 3) of YP,
     `YP:6.1' references Section 6.1 of YP,
     `YP:B' references Appendix B of YP, and
     `YP:(4)' references Equation (4) of YP.
     These references are enclosed in square brackets when used parenthetically,
     as often done with bibliographic references.")))

(xdoc::order-subtopics ethereum nil t)
