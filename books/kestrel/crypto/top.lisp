; Cryptographic Library
;
; Copyright (C) 2019-2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "primes/top")
(include-book "ecurve/top")
(include-book "ecdsa/top")
(include-book "interfaces/top")
(include-book "keccak/top")
(include-book "hmac/top")
(include-book "mimc/top")
(include-book "padding/top")
(include-book "pfcs/top")
(include-book "sha-2/top")
(include-book "kdf/top")
(include-book "r1cs/top") ;; todo: name clash on perm
(include-book "r1cs/doc")
(include-book "r1cs/sparse/doc")
(include-book "blake/top")

(include-book "attachments/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc cryptography
  :parents (acl2::kestrel-books acl2::projects)
  :short "A library for cryptography.")
