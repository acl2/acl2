; SHA-2 Library Documentation
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SHA2")

(include-book "xdoc/constructors" :dir :system)

(xdoc::defxdoc sha-2
  :parents (crypto::cryptography)
  :short "A formal specification of the SHA-2 hash functions"
  :long
  (xdoc::topstring
   (xdoc::p
    "The SHA-2 library contains executable formal specifications of several
    hash functions: SHA-224, SHA-256, SHA-384, and SHA-512.  These algorithms
    are described in NIST publication "
    (xdoc::ahref "https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf"
                 "FIPS PUB 180-4")
    ".")
   (xdoc::p
    "The library also includes tests of the specifications.")
   (xdoc::p
    "The following "
    (xdoc::tt "include-book")
    " commands may be helpful to bring in the library:")
   (xdoc::@{}
    "(include-book \"kestrel/crypto/sha-2/sha-224\" :dir :system)
(include-book \"kestrel/crypto/sha-2/sha-256\" :dir :system)
(include-book \"kestrel/crypto/sha-2/sha-384\" :dir :system)
(include-book \"kestrel/crypto/sha-2/sha-512\" :dir :system)")
   (xdoc::p
    "Or one can do:")
   (xdoc::@{}
    "(include-book \"kestrel/crypto/sha-2/top\" :dir :system)")
   (xdoc::p
    "The SHA-2 library contains two sets of interface functions: core functions
    that take lists of bits and additional convenience functions that take
    lists of bytes.  All of the functions return the hash (or message digest)
    as a list of bytes.  For both inputs and outputs, bytes are interpreted in
    a big-endian fashion.  More precisely, a sequence of bytes can be converted
    to a sequence of bits by taking the bits from the first byte, starting with
    the most significant bit, then the bits of the next byte, and so on.")
   (xdoc::p "The interface functions are:")
   (xdoc::ul
    (xdoc::li (xdoc::tt "(sha-224 bits)") " applies SHA-224 to the given list of bits, returning the hash as a list of 28 bytes.")
    (xdoc::li (xdoc::tt "(sha-224-bytes bytes)") " applies SHA-224 to the given list of bytes, returning the hash as a list of 28 bytes.")
    (xdoc::li (xdoc::tt "(sha-256 bits)") " applies SHA-256 to the given list of bits, returning the hash as a list of 32 bytes.")
    (xdoc::li (xdoc::tt "(sha-256-bytes bytes)") " applies SHA-256 to the given list of bytes, returning the hash as a list of 32 bytes.")
    (xdoc::li (xdoc::tt "(sha-384 bits)") " applies SHA-384 to the given list of bits, returning the hash as a list of 48 bytes.")
    (xdoc::li (xdoc::tt "(sha-384-bytes bytes)") " applies SHA-384 to the given list of bytes, returning the hash as a list of 48 bytes.")
    (xdoc::li (xdoc::tt "(sha-512 bits)") " applies SHA-512 to the given list of bits, returning the hash as a list of 64 bytes.")
    (xdoc::li (xdoc::tt "(sha-512-bytes bytes)") " applies SHA-512 to the given list of bytes, returning the hash as a list of 64 bytes."))
   (xdoc::p
    "See the comments in the source files for more information.")))

(xdoc::defpointer sha-224 sha-2)
(xdoc::defpointer sha-256 sha-2)
(xdoc::defpointer sha-384 sha-2)
(xdoc::defpointer sha-512 sha-2)
