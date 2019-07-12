; Elliptic Curve Digital Signature Algorithm Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/crypto/ecurve/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ECDSA"
  (append '(;; added symbols
            assert!
            b*
            bytes-to-bits
            define
            defxdoc
            repeat
            when
            ;; from ECURVE
            ecurve::secp256k1-prime
            ecurve::secp256k1-order
            ecurve::secp256k1-generator
            ecurve::secp256k1-a
            ecurve::secp256k1-b
            ecurve::secp256k1*
            ecurve::secp256k1+
            ecurve::secp256k1-negate
            ecurve::ec-32bytes-to-nat
            ecurve::ec-point-to-64bytes
            )
          (set-difference-eq
           *acl2-exports*
           '(;; removed symbols
             ))))
