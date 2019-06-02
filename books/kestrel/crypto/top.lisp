; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "secp256k1-placeholder")

(include-book "interfaces/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc cryptography
  :parents (acl2::kestrel-books acl2::projects)
  :short "A library for cryptography.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc placeholders
  :parents (cryptography)
  :short "Cryptographic placeholders."
  :long
  (xdoc::topstring
   (xdoc::p
    "Cryptographic functions are largely black boxes,
     in the sense that most of their details
     are not needed in order to describe the behavior of
     systems that use cryptography.")
   (xdoc::p
    "We introduce placeholders for cryptographic functions,
     mostly as (weakly) constrained functions.
     Some of the simpler ones are defined instead of constrained,
     because it is actually easier to define than constrain them,
     and/or because we actually need complete definitions
     to describe the behavior of certain systems of interest.")
   (xdoc::p
    "These placeholders will be replaced with fully defined functions
     that will populate this cryptographic library.")))
