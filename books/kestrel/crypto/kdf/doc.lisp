; KDF Library Documentation
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "KDF")

(include-book "xdoc/constructors" :dir :system)

(xdoc::defxdoc kdf
  :parents (crypto::cryptography)
  :short "A library for Key Derivation Functions"
  :long
  (xdoc::topstring
   (xdoc::p
    "The KDF library includes a formal specification for PBKDF2,
     Password-Based Key Derivation Function 2, specialized to use "
    (xdoc::seetopic "hmac::hmac" "the pseudorandom function HMAC-SHA-512")
    ". This key derivation function is defined in "
    (xdoc::ahref "https://tools.ietf.org/html/rfc8018" "IETF RFC 8018"))
   (xdoc::p
    "The following "
    (xdoc::tt "include-book")
    " command may be helpful to bring in the library:")
   (xdoc::@{}
    "(include-book \"kestrel/crypto/kdf/pbkdf2-hmac-sha-512\" :dir :system)")
   (xdoc::h3 "Interface Functions")
   (xdoc::h4 "pbkdf2-hmac-sha-512")
   (xdoc::blockquote (xdoc::@call "pbkdf2-hmac-sha-512"))
   (xdoc::p "Arguments:")
   (xdoc::ol
    (xdoc::li
     "@('P') -- the password, an octet string represented as a list of 8-bit bytes")
    (xdoc::li
     "@('S') -- the salt, an octet string represented as a list of 8-bit bytes")
    (xdoc::li
     "@('c') -- the iteraction count.  Note that "
     (xdoc::seetopic "bitcoin::bip39" "BIP 39")
     " uses an iteraction count of 2048.")
    (xdoc::li
     "@('dkLen') -- the intended length in octets of the derived key.  Note that "
     (xdoc::seetopic "bitcoin::bip39" "BIP 39")
     " uses a length of 64."))
    (xdoc::p
     "Returns a list of @('dkLen') bytes.")

   (xdoc::h4 "pbkdf2-hmac-sha-512-strings")
   (xdoc::blockquote (xdoc::@call "pbkdf2-hmac-sha-512-from-strings"))
   (xdoc::p "Arguments:")
   (xdoc::ol
    (xdoc::li
     "@('P-string') -- the password, an octet string represented as an ACL2 string")
    (xdoc::li
     "@('S-string') -- the salt, an octet string represented as a an ACL2 string")
    (xdoc::li
     "@('c') -- the iteraction count.  Note that "
     (xdoc::seetopic "bitcoin::bip39" "BIP 39")
     " uses an iteraction count of 2048.")
    (xdoc::li
     "@('dkLen') -- the intended length in octets of the derived key.  Note that "
     (xdoc::seetopic "bitcoin::bip39" "BIP 39")
     " uses a length of 64."))
    (xdoc::p
     "Returns a list of @('dkLen') bytes.")
   ))


(xdoc::defpointer pbkdf2-hmac-sha-512 kdf)
(xdoc::defpointer pbkdf2-hmac-sha-512-from-strings kdf)
