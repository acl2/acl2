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

(definterface-hash keccak-512
  :input-size-limit nil
  :output-size 512
  :parents (interfaces)
  :short (xdoc::topstring
          "Keccak-512 " (xdoc::seetopic "interfaces" "interface") ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "Keccak-512 is specified in the "
    (xdoc::a :href "https://keccak.team/keccak.html" "Keccak web site")
    ", in particular `The Keccak Reference' document, Version 3.0.")
   (xdoc::p
    "According to the aforementioned specification,
     the input of Keccak-512 is a sequence of any number of bits,
     or any number of bytes.")
   (xdoc::p
    "According to the aforementioned specification,
     the output of Keccak-512 is a sequence of exactly 512 bits,
     or 64 bytes.")
   (xdoc::p
    "See also:"
    (xdoc::ul
     (xdoc::li (xdoc::seetopic "keccak::keccak" "Keccak-512 executable specification"))))
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection keccak-512-interface-ext
  :extension keccak-512-interface

  (defrule byte-list64p-of-keccak-512-bytes
    (byte-list64p (keccak-512-bytes bytes))
    :enable byte-list64p))
