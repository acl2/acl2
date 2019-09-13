; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "definterface-pbkdf2")
(include-book "hmac-sha-512")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definterface-pbkdf2 pbkdf2-hmac-sha-512
  :hmac hmac-sha-512
  :parents (interfaces)
  :short (xdoc::topstring
          "PBKDF2-HMAC-SHA-512 " (xdoc::seetopic "interfaces" "interface") ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "PBKDF2 stands for Password-Based Key Derivation Function 2.
     It is defined in "
    (xdoc::ahref "https://tools.ietf.org/html/rfc8018" "IETF RFC 8018")
    ".")
   (xdoc::p
    "We instantiate PBKDF2 with the "
    (xdoc::seetopic "hmac::hmac" "pseudorandom function HMAC-SHA-512."))
   (xdoc::p
    "See also:"
    (xdoc::ul
     (xdoc::li (xdoc::seetopic "kdf::kdf" "PBKDF2-HMAC-SHA-512 executable specification"))
     (xdoc::li (xdoc::seetopic "pbkdf2-hmac-sha-512-attachment" "attaching PBKDF2-HMAC-SHA-512 executable specification to this interface"))))
   ))
