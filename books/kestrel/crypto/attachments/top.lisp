; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "hmac-sha-512")
(include-book "keccak-256")
(include-book "pbkdf2-hmac-sha-512")
(include-book "sha-256")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc attachments
  :parents (cryptography)
  :short "Cryptographic attachments."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we provide executable attachments for "
    (xdoc::seetopic "interfaces" "cryptographic interfaces")
    ".")))
