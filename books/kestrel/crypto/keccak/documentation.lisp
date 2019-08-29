; Keccak Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "KECCAK")

(include-book "keccak")

(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)

(defxdoc keccak
  :parents (crypto::cryptography)
  :short "A library for Keccak hash functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The following executable functions implement the Keccak SHA-3 submission,
     Version 3, January 14, 2011, before SHA-3 was finalized.")
   (xdoc::p
    "There are two sets of functions described here: bit-oriented and byte-oriented.
     To call them, include the following book:")
   (xdoc::@{}
    "(include-book \"kestrel/crypto/keccak/keccak\" :dir :system)")
   (xdoc::p
    "Since Keccak is specified to accept bit strings of any length, the most
     general functions accept and return \"bit strings\", which we model by lists of bits.
     The input can be any number of bits and the output length is the number
     in the function name.  There are four variants defined:")
   (xdoc::@{}
    "(keccak-224 bit-list)
(keccak-256 bit-list)
(keccak-384 bit-list)
(keccak-512 bit-list)")
   (xdoc::p
    "More commonly, callers prefer to work with bytes.  The following functions
     accept and return \"hexadecimal strings with an even number of digits\",
     which we model by lists of unsigned 8-bit bytes.  The input can be any number
     of bytes and the output length in bytes is the number in the function name
     divided by 8.  There are four variants defined:")
   (xdoc::@{}
    "(keccak-224-bytes byte-list)
(keccak-256-bytes byte-list)
(keccak-384-bytes byte-list)
(keccak-512-bytes byte-list)")
   (xdoc::p
    "For more details, please refer to the source file, which is extensively
     commented.")
   ))
