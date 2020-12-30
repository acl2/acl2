; Elliptic Curve Digital Signature Algorithm Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/crypto/ecurve/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ECDSA"
  (append '(;; added symbols
            all-unsigned-byte-p
            assert!
            b*
            bebytes=>bits
            bit-listp
            bool-fix
            byte-list-equiv
            byte-list-fix
            byte-listp
            bytes-to-bits
            define
            defrule
            defrulel
            defsection
            defxdoc
            defxdoc+
            repeat
            when
            ;; from ECURVE
            ecurve::ec-32bytes-to-nat
            ecurve::ec-point-to-64bytes
            ecurve::secp256k1*
            ecurve::secp256k1+
            ecurve::secp256k1-a
            ecurve::secp256k1-b
            ecurve::secp256k1-fieldp
            ecurve::secp256k1-generator
            ecurve::secp256k1-negate
            ecurve::secp256k1-group-prime
            ecurve::secp256k1-field-prime
            ecurve::secp256k1-priv-key-equiv
            ecurve::secp256k1-priv-key-fix
            ecurve::secp256k1-priv-key-p
            )
          (set-difference-eq
           *acl2-exports*
           '(;; removed symbols
             ))))
