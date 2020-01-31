; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (coglio@kestrel.edu)
;          Eric McCarthy (mccarthy@kestrel.edu)
;          Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ secp256k1-domain-parameters
  :parents (elliptic-curves)
  :short "Domain parameters of the secp256k1 elliptic curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "The secp256k1 elliptic curve is specified in "
    (xdoc::a :href "http://www.secg.org/sec1-v2.pdf"
      "Standards for Efficient Cryptography 1 (SEC 1)")
    " and "
    (xdoc::a :href "http://www.secg.org/sec2-v2.pdf"
      "Standards for Efficient Cryptography 2 (SEC 2)")
    ".")
   (xdoc::p
    "Here we introduce the domain parameters @($(p,a,b,G,n,h)$) of the curve,
     as nullary functions.
     For the generator point @($G$),
     we introduce two nullary functions (for the @($x$) and @($y$) coordinates),
     to facilitate the use of different representations of points.
     All these nullary functions have values that are natural numbers."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-prime ()
  :short "The prime @($p$) of the field of the curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is @($2^{256} - 2^{32} - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1$).")
   (xdoc::p
    "SEC 2 lists it as ")
   (xdoc::codeblock
    "FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE FFFFFC2F"))
  #xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
  :no-function t
  ///

  (assert-event (posp (secp256k1-prime)))

  (assert-event (equal (integer-length (secp256k1-prime)) 256))

  (assert-event (equal (secp256k1-prime)
                       (- (- (- (- (- (- (- (expt 2 256) (expt 2 32))
                                         (expt 2 9))
                                      (expt 2 8))
                                   (expt 2 7))
                                (expt 2 6))
                             (expt 2 4))
                          1)))

  (in-theory (disable (:e secp256k1-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-a ()
  :short "The coefficient @($a$) of the curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equation of the curve is @($y^2 = x^3 + ax + b$).")
   (xdoc::p
    "SEC 2 lists it as ")
   (xdoc::codeblock
    "00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000000"))
  0
  :no-function t
  ///

  (assert-event (natp (secp256k1-a)))

  (assert-event (< (secp256k1-a) (secp256k1-prime)))

  (in-theory (disable (:e secp256k1-a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-b ()
  :short "The coefficient @($b$) of the curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equation of the curve is @($y^2 = x^3 + ax + b$).")
   (xdoc::p
    "SEC 2 lists it as ")
   (xdoc::codeblock
    "00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000007"))
  7
  :no-function t
  ///

  (assert-event (natp (secp256k1-b)))

  (assert-event (< (secp256k1-b) (secp256k1-prime)))

  (in-theory (disable (:e secp256k1-b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-generator-x ()
  :short "The @($x$) coordinate of the generator @($G$)
          of the group of the curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "SEC 2 lists the point in compressed and uncompressed form.
     The @($x$) coordinate is apparent in both forms as")
   (xdoc::codeblock
    "79BE667E F9DCBBAC 55A06295 CE870B07 029BFCDB 2DCE28D9 59F2815B 16F81798"))
  #x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
  :no-function t

  ///

  (assert-event (natp (secp256k1-generator-x)))

  (assert-event (< (secp256k1-generator-x) (secp256k1-prime)))

  (in-theory (disable (:e secp256k1-generator-x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-generator-y ()
  :short "The @($y$) coordinate of the generator @($G$)
          of the group of the curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "SEC 2 lists the point in compressed and uncompressed form.
     The @($y$) coordinate is apparent in the latter forms as")
   (xdoc::codeblock
    "483ADA77 26A3C465 5DA4FBFC 0E1108A8 FD17B448 A6855419 9C47D08F FB10D4B8"))
  #x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
  :no-function t

  ///

  (assert-event (natp (secp256k1-generator-y)))

  (assert-event (< (secp256k1-generator-y) (secp256k1-prime)))

  (in-theory (disable (:e secp256k1-generator-y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-order ()
  :short "The order @($n$) of the group of the curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "SEC 2 lists it as")
   (xdoc::codeblock
    "FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE BAAEDCE6 AF48A03B BFD25E8C D0364141"))
  #xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
  :no-function t
  ///

  (assert-event (posp (secp256k1-order)))

  (assert-event (equal (integer-length (secp256k1-order)) 256))

  (in-theory (disable (:e secp256k1-order))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-cofactor ()
  :short "The cofactor @($h$) of the group of the curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "SEC 2 lists it as")
   (xdoc::codeblock
    "01"))
  1
  :no-function t
  ///

  (assert-event (posp (secp256k1-cofactor)))

  (in-theory (disable (:e secp256k1-cofactor))))
