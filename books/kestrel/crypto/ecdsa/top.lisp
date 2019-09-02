; Elliptic Curve Digital Signature Algorithm Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECDSA")

(include-book "secp256k1-interface")

(include-book "secp256k1-attachment")

(include-book "deterministic-ecdsa-secp256k1")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc elliptic-curve-digital-signature-algorithm
  :parents (crypto::cryptography)
  :short "Elliptic Curve Digital Signature Algorithm (ECDSA).")
