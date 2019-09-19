; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "definterface-encrypt-block")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definterface-encrypt-block aes-128
  :key-size 128
  :block-size 128
  :parents (interfaces)
  :short (xdoc::topstring
          "AES-128 " (xdoc::seetopic "interfaces" "interface") ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "AES-128 is specified in the "
    (xdoc::a :href "https://csrc.nist.gov/publications/detail/fips/197/final"
      "FIPS PUB 197 standard")
    ".")
   (xdoc::p
    "According to FIPS PUB 197,
     AES-128 has a key size of 128 bits and a block size of 128 bits.")))
