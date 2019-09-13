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
(include-book "kestrel/fty/byte-list64" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definterface-hash sha-512
  :input-size-limit (expt 2 128)
  :output-size 512
  :parents (interfaces)
  :short (xdoc::topstring
          "SHA-512 " (xdoc::seetopic "interfaces" "interface") ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "SHA-512 is specified in the "
    (xdoc::a :href "https://csrc.nist.gov/publications/detail/fips/180/4/final"
      "FIPS PUB 180-4 standard")
    ".")
   (xdoc::p
    "According to FIPS PUB 180-4,
     the input of SHA-512 is a sequence of less than @($2^{128}$) bits,
     or less than @($2^{125}$) bytes.")
   (xdoc::p
    "According to FIPS PUB 180-4,
     the output of SHA-512 is a sequence of exactly 512 bits, or 64 bytes.")
   (xdoc::p
    "See also:"
    (xdoc::ul
     (xdoc::li (xdoc::seetopic "sha2::sha-2" "SHA-512 executable specification"))))
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection sha-512-interface-ext
  :extension sha-512-interface

  (defrule byte-list64p-of-sha-512-bytes
    (byte-list64p (sha-512-bytes bytes))
    :enable byte-list64p))
