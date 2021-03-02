; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "bit-byte-integer-conversions")
(include-book "blake2-hash")
(include-book "constants")
(include-book "jubjub")
(include-book "jubjub-montgomery")
(include-book "pedersen-hash")
(include-book "randomness-beacon")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ zcash
  :parents (acl2::projects acl2::kestrel-books)
  :short "A library for Zcash."
  :long
  (xdoc::topstring
   (xdoc::p
    (xdoc::ahref "https://z.cash" "Zcash")
    " is a blockchain currency that provides confidentiality
     via zero-knowledge proofs.")
   (xdoc::p
    "This library provides an ACL2 formalization of some aspects of Zcash.
     The formalization is based on the "
    (xdoc::ahref
     "https://github.com/zcash/zips/blob/master/protocol/protocol.pdf"
     "Zcash Protocol Specification (Version 2021.1.16)")
    ", referenced as `[ZPS]' in the documentation of this library.
     Sections, appendices, theorems, etc. are referenced
     by appending their designations separated by colo,
     e.g.
     `[ZPS:4.1.1]' references Section 4.1.1,
     `[ZPS:A.2]' references Appendix A.2, and
     `[ZPS:T.A.2.1]' references Theorem A.2.1
     (that is, we use `T' to refer to theorems, including lemmas).
     These square-bracketed references may be used
     as nouns or parenthentically."))
  :order-subtopics t)
