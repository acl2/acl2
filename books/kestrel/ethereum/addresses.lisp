; Ethereum Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/crypto/ecurve/secp256k1-interface" :dir :system)
(include-book "kestrel/crypto/interfaces/keccak-256" :dir :system)
(include-book "bytes")

(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ addresses
  :parents (ethereum)
  :short "Addresses."
  :long
  (xdoc::topstring
   (xdoc::p
    "Account addresses are 160-bit values [YP:4.1] [YP:A],
     which are equivalent to 20-byte values.
     We use the library type @(tsee byte-list20)
     to model addresses in our Ethereum model,
     which is consistent with [YP:(18)]."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define public-key-to-address ((pub-key secp256k1-pub-key-p))
  :returns (address byte-list20p
                    :hints (("Goal" :in-theory (enable byte-list20p))))
  :parents (addresses)
  :short "Calculate the address for a public key."
  :long
  (xdoc::topstring
   (xdoc::p
    "The address consists of
     the rightmost 160 bits of the 256-bit Keccak-256 hash
     of the serialized public key [YP:(284)].
     This is equivalent to the rightmost 20 bytes of the 32-byte hash.")
   (xdoc::p
    "This function corresponds to ``part of'' the function @($A$) [YP:(284)],
     because it takes a public key as argument,
     corresponding to @($\\mathtt{ECDSAPUBKEY}(p_\\mathrm{r})$) in [YP:(284)].
     The function @($\\mathtt{ECDSAPUBKEY}$)
     returns an array of 64 bytes [YP:(277)]
     which suggests that the public key is represented
     as an elliptic curve point in uncompressed form.
     Thus, we use the library function @(tsee secp256k1-point-to-bytes)
     to turn the public key into that form.")
   (xdoc::p
    "The function @(tsee private-key-to-address) calculates an address
     from a private key instead."))
  (b* ((pub-key (mbe :logic (secp256k1-pub-key-fix pub-key) :exec pub-key))
       (uncompressed-form (secp256k1-point-to-bytes pub-key nil))
       (hash (keccak-256-bytes uncompressed-form))
       (address (nthcdr 12 hash)))
    address)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define private-key-to-address ((priv-key secp256k1-priv-key-p))
  :returns (address byte-list20p
                    :hints (("Goal" :in-theory (enable byte-list20p))))
  :parents (addresses)
  :short "Calculate the address for a private key."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the public key from the private key,
     and then use @(tsee public-key-to-address) to calculate the addres."))
  (public-key-to-address (secp256k1-priv-to-pub priv-key))
  :hooks (:fix))
