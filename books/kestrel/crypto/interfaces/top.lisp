; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "definterface-hash")
(include-book "definterface-hmac")
(include-book "definterface-pbkdf2")
(include-book "definterface-encrypt-block")
(include-book "definterface-encrypt-init")

(include-book "keccak-256")
(include-book "keccak-512")
(include-book "ripemd-160")
(include-book "sha-256")
(include-book "sha-512")

(include-book "hmac-sha-256")
(include-book "hmac-sha-512")

(include-book "pbkdf2-hmac-sha-256")
(include-book "pbkdf2-hmac-sha-512")

(include-book "aes-128")
(include-book "aes-192")
(include-book "aes-256")

(include-book "aes-128-cbc-pkcs7")
(include-book "aes-192-cbc-pkcs7")
(include-book "aes-256-cbc-pkcs7")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc interfaces
  :parents (cryptography)
  :short "Cryptographic interfaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "Cryptographic functions are largely black boxes,
     in the sense that most of their details
     are not needed in order to describe the behavior of
     systems that use cryptography.")
   (xdoc::p
    "Thus, it is useful to introduce interfaces for cryptographic functions,
     in the form of (weakly) constrained ACL2 functions,
     whose only properties concern, for instance,
     the types of their inputs and outputs.
     A formalization that involves cryptography
     can include and use these interfaces,
     whose relatively shallow properties should nonetheless suffice,
     because of the aforementioned black-box nature of cryptography.
     In other words, a formalization can be parameterized
     over the details of the cryptographic functions,
     without having to include and use full definitions of these functions.")
   (xdoc::p
    "Executable attachments for these interfaces can be used
     to execute code that calls these interfaces.
     It should be also possible to automatically specialize
     code that uses these interfaces
     to use (compatible) full definitions of the functions.")
   (xdoc::p
    "We provide macros to generate cryptographic interfaces of various kinds
     (e.g. interfaces for hash functions),
     as well as interfaces for various standard cryptographic functions.")))
