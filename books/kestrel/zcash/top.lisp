; Zcash Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "bit-byte-integer-conversions")
(include-book "blake2-hash")
(include-book "constants")
(include-book "jubjub")
(include-book "jubjub-r-properties")
(include-book "jubjub-montgomery")
(include-book "pedersen-hash")
(include-book "pedersen-hash-bound-properties")
(include-book "pedersen-hash-injectivity-properties")
(include-book "pedersen-hash-image-properties")
(include-book "randomness-beacon")
(include-book "verify-zcash-r1cs")

(include-book "gadgets/top")

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
     "https://zips.z.cash/protocol/protocol.pdf" "Zcash Protocol Specification")
    " (Version 2021.1.15 [NU5 proposal] of 2021-09-01, as of this writing),
     referenced as `[ZPS]' in the documentation of this library.
     Sections, appendices, theorems, etc. are referenced
     by appending their designations separated by colo,
     e.g.
     `[ZPS:4.1.1]' references Section 4.1.1,
     `[ZPS:A.2]' references Appendix A.2, and
     `[ZPS:T.A.2.1]' references Theorem A.2.1
     (that is, we use `T' to refer to theorems, including lemmas).
     These square-bracketed references may be used
     as nouns or parenthentically.")
   (xdoc::p
    "The link to [ZPS] above actually points to
     a newer version (presumably, the most recent)
     than the one that our formalization is based on, specified above.
     It is not clear whether that older version is available anywhere now;
     but it should be possible to ``map''
     the references in the documentation of our formalization
     to the newer version at the link above."))
  :order-subtopics t)
