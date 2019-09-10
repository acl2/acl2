; Bitcoin Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "base58")
(include-book "crypto")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ base58check
  :parents (bitcoin)
  :short "Base58Check encoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Base58Check encoding is described in
     <a href=\"https://en.bitcoin.it/wiki/Base58Check_encoding\"
     >Page `Base58Check encoding' of [Wiki]</a>.
     Base58Check encoding is also described
     in Section `Base58 and Base58Check Encoding' of Chapter 4 of [MB].
     [WP] does not mention Base58Check encoding.")
   (xdoc::p
    "We do not formalize any Base58Check decoding for now."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base58check-encode ((version byte-listp) (payload byte-listp))
  :guard (and (consp version)
              (< (+ (len version) (len payload))
                 (expt 2 61)))
  :returns (chars base58-character-listp)
  :short "Encode a payload, with a version prefix, in Base58Check."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is described in
     <a href=\"https://en.bitcoin.it/wiki/Base58Check_encoding#Creating_a_Base58Check_string\"
     >Section `Creating a Base58Check string' of Page `Base58Check encoding'
     of [Wiki]</a>.
     It is also described
     in Section `Base58 and Base58Check Encoding' of Chapter 4 of [MB],
     with an illustration in Figure 6.")
   (xdoc::p
    "Version prefix and payload (which are both lists of bytes)
     are concatenated and hashed twice with SHA-256.
     The first four bytes of the hash are used as a checksum,
     which is appended to the concatenated version prefix and payload.
     The resulting bytes are Base58-encoded.")
   (xdoc::p
    "Bullet 1 of the description in [Wiki] talks about a single version byte.
     However, both Table 1 of Chapter 4 of [MB]
     and <a href=\"https://en.bitcoin.it/wiki/List_of_address_prefixes\">Page
     `List of address prefixes' of [Wiki]</a>
     include multi-byte prefixes.
     Thus, this function takes a list of bytes as the version prefix.")
   (xdoc::p
    "The combined length of version prefix and payload
     must not exceed the (large) limit for SHA-256.
     See the guard of "
    (xdoc::seetopic "crypto::sha-256-interface" "@('sha-256')")
    ".")
   (xdoc::p
    "We require the version to be non-empty.
     A version that is the empty list of bytes does not seem to make sense.
     We allow the payload to be empty,
     even though this may never happen in Bitcoin."))
  (b* ((version (mbe :logic (if (consp version) version (list 0))
                     :exec version))
       (version+payload (append version payload))
       (hash (sha-256-bytes (sha-256-bytes version+payload)))
       (checksum (take 4 hash))
       (version+payload+checksum (append version+payload checksum)))
    (base58-encode version+payload+checksum))
  :hooks (:fix)
  ///

  (defruled base58check-encode-fixes-version-nonempty
    (equal (base58check-encode nil payload)
           (base58check-encode (list 0) payload))))
