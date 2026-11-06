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

(define public-key-to-bytes ((pub-key secp256k1-pub-key-p))
  :returns (bytes byte-list64p
                  :hints (("Goal" :in-theory (enable byte-list64p))))
  :parents (addresses)
  :short "Serialize a public key into 64 bytes, as in [YP:(277)]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @($\\mathtt{ECDSAPUBKEY}$) [YP:(277)]
     returns a public key as an array of 64 bytes,
     consisting of the x and y coordinates of the elliptic curve point,
     each as a 32-byte big-endian unsigned integer [YP:F].")
   (xdoc::p
    "This is not one of the point encodings defined in SEC 1 (Section 2.3.3),
     which are produced by @(tsee secp256k1-point-to-bytes).
     Those start with a byte that identifies the form:
     2 or 3 for the compressed form, 4 for the uncompressed form.
     The SEC 1 uncompressed form consists of that byte 4
     followed by the 64 bytes produced by this function,
     as proved below.
     Only the 64 bytes, without the byte 4,
     are hashed to obtain the address of the public key
     (see @(tsee public-key-to-address)).")
   (xdoc::p
    "Since a public key is never the point at infinity,
     this function does not need a representation for that point,
     unlike SEC 1."))
  (b* ((pub-key (mbe :logic (secp256k1-pub-key-fix pub-key) :exec pub-key)))
    (append (acl2::nat=>bebytes 32 (ecurve::secp256k1-point->x pub-key))
            (acl2::nat=>bebytes 32 (ecurve::secp256k1-point->y pub-key))))
  :hooks (:fix)
  ///

  (defrule len-of-public-key-to-bytes
    (equal (len (public-key-to-bytes pub-key))
           64))

  (defruled secp256k1-point-to-bytes-uncompressed-of-public-key
    (equal (secp256k1-point-to-bytes (secp256k1-pub-key-fix pub-key) nil)
           (cons 4 (public-key-to-bytes pub-key)))
    :enable (secp256k1-point-to-bytes
             ecurve::secp256k1-pub-key-p)))

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
     returns an array of 64 bytes [YP:(277)],
     which we obtain via @(tsee public-key-to-bytes).")
   (xdoc::p
    "The function @(tsee private-key-to-address) calculates an address
     from a private key instead."))
  (b* ((bytes (public-key-to-bytes pub-key))
       (hash (keccak-256-bytes bytes))
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
     and then use @(tsee public-key-to-address) to calculate the address."))
  (public-key-to-address (secp256k1-priv-to-pub priv-key))
  :hooks (:fix))
