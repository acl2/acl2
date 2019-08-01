; Bitcoin Library
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
(include-book "kestrel/crypto/ecurve/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "BITCOIN" (append *std-pkg-symbols*
                          '(bebytes=>bits
                            bebytes=>nat
                            bendian=>nat
                            bit-listp
                            bits=>bebytes
                            bits=>beubyte11s
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
                            nat=>bebytes
                            nat=>bebytes*
                            nat=>bendian
                            nat=>bendian*
                            prefixp
                            string=>nats
                            trim-bendian*
                            ubyte11-fix
                            ubyte11-listp
                            ubyte11p
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
                            crypto::pbkdf2-hmac-sha-512
                            crypto::ripemd-160-bytes
                            crypto::sha-256-bytes
                            ecurve::secp256k1-add
                            ecurve::secp256k1-mul
                            ecurve::secp256k1-priv-to-pub
                            ecurve::secp256k1-order
                            ecurve::secp256k1-point-generator
                            ecurve::secp256k1-point-infinityp
                            ecurve::secp256k1-point-to-bytes
                            ecurve::secp256k1-pointp
                            ecurve::secp256k1-priv-key
                            ecurve::secp256k1-priv-key-p
                            ecurve::secp256k1-pub-key
                            ecurve::secp256k1-pub-key-p)))
