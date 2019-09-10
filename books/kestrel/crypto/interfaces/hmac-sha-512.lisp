; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "definterface-hmac")
(include-book "sha-512")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definterface-hmac hmac-sha-512
  :hash sha-512
  :block-size 128
  :parents (interfaces)
  :short (xdoc::topstring
          "HMAC-SHA-512 " (xdoc::seetopic "interfaces" "interface") ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "We instantiate HMAC with the SHA-512 hash,
     whose block size is 128 bytes according to FIPS 180-4.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hmac-sha-512-interface-ext
  :extension hmac-sha-512-interface

  (defrule byte-list64p-of-hmac-sha-512
    (byte-list64p (hmac-sha-512 key text))
    :enable byte-list64p))
