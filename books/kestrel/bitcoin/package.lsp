; Bitcoin -- Package
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "kestrel/crypto/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "BITCOIN" (append *std-pkg-symbols*
                          '(bendian=>nat
                            byte
                            byte-fix
                            byte-list
                            byte-listp
                            byte-list-equiv
                            byte-list-fix
                            bytep
                            dab-digit-fix
                            dab-digit-list-fix
                            dab-digit-listp
                            dab-digitp
                            define-sk
                            defthm-dab-return-types
                            defxdoc+
                            explode
                            implode
                            index-of
                            nat
                            nat-equiv
                            nat=>bendian
                            nat=>bendian*
                            prefixp
                            string=>nats
                            trim-bendian*
                            ubyte32
                            ubyte32-fix
                            ubyte32-list
                            ubyte32-list-fix
                            ubyte32-listp
                            ubyte32p
                            ubyte8-fix
                            ubyte8-list-equiv
                            ubyte8-list-fix
                            ubyte8-listp
                            ubyte8p
                            unsigned-byte-fix
                            unsigned-byte-list-fix
                            crypto::hmac-sha-512
                            crypto::ripemd-160
                            crypto::sha-256
                            crypto::secp256k1-add
                            crypto::secp256k1-generator
                            crypto::secp256k1-infinityp
                            crypto::secp256k1-mul
                            crypto::secp256k1-order
                            crypto::secp256k1-point-to-bytes
                            crypto::secp256k1-pointp
                            crypto::secp256k1-priv-key
                            crypto::secp256k1-priv-key-p
                            crypto::secp256k1-priv-to-pub
                            crypto::secp256k1-pub-key
                            crypto::secp256k1-pub-key-p)))
