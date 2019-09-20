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
(include-book "sha-256")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definterface-hmac hmac-sha-256
  :hash sha-256
  :block-size 64
  :parents (interfaces)
  :short (xdoc::topstring
          "HMAC-SHA-256 " (xdoc::seetopic "interfaces" "interface") ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "We instantiate HMAC with the SHA-256 hash,
     whose block size is 64 bytes according to FIPS 180-4.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hmac-sha-256-interface-ext
  :extension hmac-sha-256-interface

  (defrule byte-list32p-of-hmac-sha-256
    (byte-list32p (hmac-sha-256 key text))
    :enable byte-list32p))
