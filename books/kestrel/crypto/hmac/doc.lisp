; HMAC Library Documentation
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HMAC")

(include-book "xdoc/constructors" :dir :system)

(xdoc::defxdoc hmac
  :parents (crypto::cryptography)
  :short "A library for the HMAC keyed-hash message authentication code"
  :long
  (xdoc::topstring
   (xdoc::p
    "The HMAC library includes formal specifications for HMAC-SHA-256 and
    HMAC-SHA-512, i.e., for the HMAC keyed-hash message authentication code,
    using either " (xdoc::seetopic "sha2::sha-2" "SHA-256") " or " (xdoc::seetopic
    "sha2::sha-2" "SHA-512") " as the underlying hash function.  HMAC is defined
    in " (xdoc::ahref "https://tools.ietf.org/html/rfc2104" "RFC 2104") ".")
   (xdoc::p
    "The following "
    (xdoc::tt "include-book")
    " commands may be helpful to bring in the library:")
   (xdoc::@{}
    "(include-book \"kestrel/crypto/hmac/hmac-sha-256\" :dir :system)
(include-book \"kestrel/crypto/hmac/hmac-sha-512\" :dir :system)")
   (xdoc::p
    "Or one can do:")
   (xdoc::@{}
    "(include-book \"kestrel/crypto/hmac/top\" :dir :system)")
   (xdoc::p "The interface functions are:")
   (xdoc::ul
     (xdoc::li (xdoc::tt "(hmac-sha-256 k text)") " applies HMAC-SHA-256 to key " (xdoc::tt "k") " (a list of bytes) and data " (xdoc::tt "text") " (a list of bits).  Returns a list of 32 bytes.")
     (xdoc::li (xdoc::tt "(hmac-sha-512 k text)") " applies HMAC-SHA-512 to key " (xdoc::tt "k") " (a list of bytes) and data " (xdoc::tt "text") " (a list of bits).  Returns a list of 64 bytes."))
   (xdoc::p "See " (xdoc::ahref "https://tools.ietf.org/html/rfc2104" "RFC 2104") " for guidance on the length of the keys used.")
   (xdoc::p
    "See the comments in the source files for more information on the HMAC library.")
   (xdoc::p
    "The library also includes tests of the specifications.")
   ))

(xdoc::defpointer hmac-sha-256 hmac)
(xdoc::defpointer hmac-sha-512 hmac)
