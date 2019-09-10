; Cryptocurrency Hierarchical Deterministic Wallet Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HDWALLET")

(include-book "wallet")

(include-book "kestrel/crypto/attachments/hmac-sha-512" :dir :system)
(include-book "kestrel/crypto/attachments/keccak-256" :dir :system)
(include-book "kestrel/crypto/attachments/pbkdf2-hmac-sha-512" :dir :system)
(include-book "kestrel/crypto/attachments/sha-256" :dir :system)
(include-book "kestrel/crypto/ecdsa/secp256k1-attachment" :dir :system)
(include-book "kestrel/crypto/ecurve/secp256k1-attachment" :dir :system)
(include-book "kestrel/bitcoin/bip32-executable" :dir :system)
(include-book "oslib/file-types" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc crypto-hdwallet-executable
  :parents (crypto-hdwallet)
  :short "Executable version of the
          hierachical deterministic wallet for cryptocurrencies."
  :long
  (xdoc::topstring
   (xdoc::p
    "The wallet specification is mostly executable.
     We make it completely executable
     by including the following in this file,
     besides the wallet specification itself:")
   (xdoc::ul
    (xdoc::li
     "The needed "
     (xdoc::seetopic "crypto::attachments" "cryptographic executable attachments")
     ".")
    (xdoc::li
     "The "
     (xdoc::seetopic "bitcoin::bip32-executable-attachments"
                   "BIP 32 executable attachments")
     ".")
    (xdoc::li
     "The raw Lisp code for some "
     (xdoc::seetopic "oslib::oslib" "OSLIB")
     " utilities. See `Loading the library' on that manual page."))))
