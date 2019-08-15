; HDWALLET -- Package
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Eric McCarthy (mccarthy@kestrel.edu)
;          Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "kestrel/bitcoin/portcullis" :dir :system)
(include-book "kestrel/ethereum/portcullis" :dir :system)
(include-book "oslib/portcullis" :dir :system)
(include-book "kestrel/crypto/ecdsa/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "HDWALLET"
  (append '(;; added symbols
            bebytes=>bits
            byte-listp
            byte-list20p
            define-sk
            defxdoc+
            hexstring=>ubyte8s
            nat
            nat=>bebytes
            nats=>string
            read-file-bytes
            read-string
            string=>nats
            tuplep
            ubyte8s=>hexstring
            ubyte32-fix
            ubyte32-list-fix
            ubyte32-listp
            ubyte32p
            write-bytes-to-file
            bitcoin::*bip44-purpose*
            bitcoin::bip32-ext-key-priv
            bitcoin::bip32-ext-priv-key
            bitcoin::bip32-extend-tree
            bitcoin::bip32-get-priv-key-at-path
            bitcoin::bip32-key-tree
            bitcoin::bip32-key-tree->index-tree
            bitcoin::bip32-key-tree->root-depth
            bitcoin::bip32-key-tree-priv-p
            bitcoin::bip32-master-tree
            bitcoin::bip32-path-in-tree-p
            bitcoin::bip32-path-setp
            bitcoin::bip39-entropy-size-p
            bitcoin::bip39-entropy-to-mnemonic
            bitcoin::bip39-entropyp
            bitcoin::bip39-mnemonic-to-seed
            crypto::aes-128-cbc-pkcs7-encrypt-bytes
            crypto::aes-128-cbc-pkcs7-decrypt-bytes
            crypto::pbkdf2-hmac-sha-512
            ecdsa::ecdsasign
            ethereum::make-signed-transaction
            ethereum::make-transaction
            ethereum::maybe-byte-list20p
            ethereum::private-key-to-address
            ethereum::rlp-encode-transaction
            ethereum::wordp
            oslib::file-kind
            oslib::path-exists-p
            str::cat
            str::hex-digit-string-p
            str::strtok
            str::strval
            )
          (set-difference-eq
           *std-pkg-symbols*
           '(;; removed symbols
             ))))
