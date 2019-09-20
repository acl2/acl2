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
(include-book "kestrel/fty/byte-list20" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definterface-hash ripemd-160
  :input-size-limit nil
  :output-size 160
  :parents (interfaces)
  :short (xdoc::topstring
          "RIPEMD-160 " (xdoc::seetopic "interfaces" "interface") ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "RIPEMD-160 is specified in "
    (xdoc::a
     :href
      "https://homes.esat.kuleuven.be/~bosselae/ripemd160/pdf/AB-9601/AB-9601.pdf"
      "the `RIPEMD-160: A Strengthened Version of RIPEMD' document")
    ".")
   (xdoc::p
    "According to the aforementioned document,
     the input of RIPEMD-160 is a sequence of any number of bits,
     or any number of bytes.")
   (xdoc::p
    "According to the aforementioned document,
     the output of RIPEMD-160 is a sequence of exactly 160 bits,
     or 20 bytes.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ripemd-160-interface-ext
  :extension ripemd-160-interface

  (defrule byte-list20p-of-ripemd-160-bytes
    (byte-list20p (ripemd-160-bytes bytes))
    :enable byte-list20p))
