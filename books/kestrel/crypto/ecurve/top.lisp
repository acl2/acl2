; Elliptic Curve Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "short-weierstrass")
(include-book "short-weierstrass-validation")

(include-book "twisted-edwards")

(include-book "montgomery")

(include-book "birational-montgomery-twisted-edwards")

(include-book "secp256k1-domain-parameters")
(include-book "secp256k1-interface")
(include-book "secp256k1-types")

(include-book "secp256k1")
(include-book "secp256k1-attachment")

(include-book "points-fty")

(acl2::merge-io-pairs
 rtl::primep
 (include-book "bls12-377-domain-parameters"))

(include-book "edwards-bls12")

(include-book "prime-field-squares")
(include-book "prime-field-squares2")
(include-book "prime-field-squares-euler-criterion")
(include-book "prime-field-extra-rules")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc elliptic-curves
  :parents (crypto::cryptography)
  :short "Elliptic curve cryptography.")

(xdoc::order-subtopics elliptic-curves
  (points
   short-weierstrass-curves
   twisted-edwards
   montgomery
   edwards-bls12
   secp256k1-domain-parameters
   secp256k1-types
   secp256k1
   secp256k1-interface
   secp256k1-attachment
   bls12-377-domain-parameters
   pfield-squarep))
