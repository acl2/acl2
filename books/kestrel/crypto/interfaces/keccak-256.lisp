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
(include-book "kestrel/fty/byte-list32" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definterface-hash keccak-256
  :input-size-limit nil
  :output-size 256
  :parents (interfaces)
  :short (xdoc::topstring
          "Keccak-256 " (xdoc::seetopic "interfaces" "interface") ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "Keccak-256 is specified in the "
    (xdoc::a :href "https://keccak.team/keccak.html" "Keccak web site")
    ", in particular `The Keccak Reference' document, Version 3.0.")
   (xdoc::p
    "According to the aforementioned specification,
     the input of Keccak-256 is a sequence of any number of bits,
     or any number of bytes.")
   (xdoc::p
    "According to the aforementioned specification,
     the output of Keccak-256 is a sequence of exactly 256 bits,
     or 32 bytes.")
   (xdoc::p
    "See also:"
    (xdoc::ul
     (xdoc::li (xdoc::seetopic "keccak::keccak" "Keccak-256 executable specification"))
     (xdoc::li (xdoc::seetopic "keccak-256-attachment" "attaching Keccak-256 executable specification to this interface"))))
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection keccak-256-interface-ext
  :extension keccak-256-interface

  (defrule byte-list32p-of-keccak-256-bytes
    (byte-list32p (keccak-256-bytes bytes))
    :enable byte-list32p))
