; Ethereum Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "basics")
(include-book "crypto")
(include-book "rlp/top")
(include-book "database")
(include-book "hex-prefix")
(include-book "mmp-trees")
(include-book "transactions")
(include-book "addresses")
(include-book "evm/evm-rules") ; includes evm/evm.lisp

; Merge-io-pairs call added by Matt K. at the request of Alessandro C.:
(acl2::merge-io-pairs
 dm::primep
 (include-book "semaphore/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ethereum
  :parents (acl2::kestrel-books acl2::projects)
  :short "A library for Ethereum."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently this library contains a formal model of some aspects of the "
    (xdoc::a :href "https://ethereum.org" "Ethereum")
    " ``world computer''.
     It is expected that this library will be extended with more
     Ethereum-related formalizations and tools.")
   (xdoc::p
    "This library is based on the following sources:")
   (xdoc::ul
    (xdoc::li
     "The Ethereum Wiki,
      referenced as `[Wiki]' in the documentation of this library.
      This Ethereum Wiki can no longer be found at the URL it had at the time,
      but presumably its contents have been migrated (and likely updated)
      to the "
     (xdoc::ahref "https://ethereum.org/en/developers/docs/"
                  "Ethereum development documentation")
     ".")
    (xdoc::li
     "The BYZANTIUM VERSION 3e36772 of the "
     (xdoc::a :href "https://github.com/ethereum/yellowpaper"
       "Ethereum Yellow Paper")
     ", referenced as `[YP]' in the documentation of this library.
      Sections, appendices, and equations are referenced
      by appending their designations separated by colon,
      e.g.
      `[YP:3]' references Section 3,
      `[YP:6.1]' references Section 6.1,
      `[YP:B]' references Appendix B, and
      `[YP:(4)]' references Equation (4).")
    (xdoc::li
     "The "
     (xdoc::a :href "http://eips.ethereum.org/EIPS/eip-155"
       "Ethereum Improvement Proposal (EIP) 155")
     ", referenced as `[EIP155]' in the documentation of this library."))
   (xdoc::p
    "These square-bracketed references may be used
     as nouns or parenthentically."))
  :order-subtopics (basics
                    cryptography
                    rlp
                    database
                    hex-prefix
                    mmp-trees
                    transactions
                    addresses))
