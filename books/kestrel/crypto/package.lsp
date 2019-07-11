; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "kestrel/crypto/ecurve/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "CRYPTO" (append *std-pkg-symbols*
                         '(bit-listp
                           bool-fix
                           byte-list-equiv
                           byte-list-fix
                           byte-listp
                           byte-list20p
                           byte-list32p
                           byte-list64p
                           defxdoc+
                           maybe-posp
                           nat-equiv
                           nat=>bebytes
                           pos-fix
                           ecurve::secp256k1-a
                           ecurve::secp256k1-b
                           ecurve::secp256k1-fieldp
                           ecurve::secp256k1-point-generator
                           ecurve::secp256k1-point
                           ecurve::secp256k1-point->x
                           ecurve::secp256k1-point->y
                           ecurve::secp256k1-point-equiv
                           ecurve::secp256k1-point-fix
                           ecurve::secp256k1-pointp
                           ecurve::secp256k1-prime
                           ecurve::secp256k1-priv-key-equiv
                           ecurve::secp256k1-priv-key-fix
                           ecurve::secp256k1-priv-key-p
                           ecurve::secp256k1-pub-key-p)))
