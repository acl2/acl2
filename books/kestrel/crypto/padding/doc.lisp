; Padding Library Documentation
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PADDING")

(include-book "xdoc/constructors" :dir :system)

(xdoc::defxdoc padding
  :parents (crypto::cryptography)
  :short "A library containing come padding operations useful for cryptography"
  :long
  (xdoc::topstring
   (xdoc::p
    "The padding library contains executable formal specifications of several
    cryptographic padding operations.  These operations are described in, for example,
    Section 5.1.1 of "
    (xdoc::ahref "https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf"
                 "FIPS PUB 180-4")
    ".")
   (xdoc::p
    "The library also includes tests and validation theorems about the padding operations.")
   (xdoc::p
    "The following "
    (xdoc::tt "include-book")
    " commands may be helpful to bring in the library:")
   (xdoc::@{}
    "(include-book \"kestrel/crypto/padding/pad-to-448\" :dir :system)
(include-book \"kestrel/crypto/padding/pad-to-896\" :dir :system)")
   (xdoc::p
    "Or one can do:")
   (xdoc::@{}
    "(include-book \"kestrel/crypto/padding/top\" :dir :system)")
   (xdoc::p "The interface functions are:")
   (xdoc::ul
     (xdoc::li (xdoc::tt "(pad-to-448 bits)") ": Given list of any number of bits, add a single 1 bit, followed by enough 0 bits to make the resulting list's length be congruent to 448 modulo 512.")
     (xdoc::li (xdoc::tt "(pad-to-896 bits)") ": Given list of any number of bits, add a single 1 bit, followed by enough 0 bits to make the resulting list's length be congruent to 896 modulo 1024."))
   (xdoc::p "The above functions do not include the encoded length field, as is often done when using these padding operations, leaving that up to the caller if desired.  The reason is that cryptogtaphic algorithms differ on the endianness that should be used when storing the length field.")
   (xdoc::p
    "See the comments in the source files for more information.")))

(xdoc::defpointer pad-to-448 padding)
(xdoc::defpointer pad-to-896 padding)
