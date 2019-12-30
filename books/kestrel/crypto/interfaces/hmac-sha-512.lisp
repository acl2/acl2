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
    "HMAC stands for keyed-hash message authentication code.
     It is specified in "
    (xdoc::ahref "https://tools.ietf.org/html/rfc2104" "IETF RFC 2104")
    ".")
   (xdoc::p
    "We instantiate HMAC with the "
    (xdoc::seetopic "sha2::sha-2" "SHA-512 hash function") ",
    whose block size is 128 bytes and output size is 64 bytes
    according to FIPS 180-4.")
   (xdoc::p
    "See also:"
    (xdoc::ul
     (xdoc::li
      (xdoc::seetopic "hmac::hmac" "HMAC-SHA-512 executable specification"))
     (xdoc::li
      (xdoc::seetopic
       "hmac-sha-512-attachment"
       "attaching HMAC-SHA-512 executable specification to this interface"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hmac-sha-512-interface-ext
  :extension hmac-sha-512-interface

  (defrule byte-list64p-of-hmac-sha-512
    (byte-list64p (hmac-sha-512 key text))
    :enable byte-list64p))
