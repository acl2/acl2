; Elliptic Curve Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "kestrel/crypto/ecurve/secp256k1-domain-parameters" :dir :system)

(include-book "projects/quadratic-reciprocity/euclid" :dir :system) ;for rtl::primep
(local (include-book "projects/quadratic-reciprocity/pratt" :dir :system))

(in-theory (disable (:e rtl::primep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book proves some properties of the prime p used in the curve secp256k1,
; which is defined in the SEC 2 standard,
; available at http://www.secg.org/sec2-v2.pdf,
; Section 2.4.1.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; To prove that p is indeed a prime,
;; we use Russinoff's algorithm from the paper
;; "Pratt certification and the primality of 2^255 - 19",
;; where a Pratt certificate of n is a tree
;; (r (p1 ... pn) (e1 ... en) (c1 ... cn))
;; such that
;; 1. r is primitive root of n
;; 2. n - 1 = (p1^e1)...(pn^en)
;; 3. ci is a pratt certificate of pi.

(local
 ;; the following certificate was generated using
 ;; Mathematica's FactorInteger and PrimitiveRoot:
 (defconst *secp256k1-prime-pratt-cert*
   '(3 (2 3 7 13441 205115282021455665897114700593932402728804164701536103180137503955397371)
       (1 1 1 1 1)
       (() () () ()
        (10 (2 3 5 29 31 7723 132896956044521568488119 255515944373312847190720520512484175977)
            (1 1 1 2 1 1 1 1)
            (() () () () () ()
             (6 (2 3 22149492674086928081353)
                (1 1 1)
                (() ()
                 (5 (2 3 5323 173378833005251801)
                    (3 1 1 1)
                    (() () ()
                     (6 (2 5 2621 24809 13331831)
                        (3 2 1 1 1)
                        (() () () ()
                         (13 (2 5 971 1373)
                             (1 1 1 1)
                             (() () () ()))
                         ))
                     ))
                 ))
             (3 (2 7 11 1627 2657 4423 41201 96557 7240687 107590001)
                (3 2 1 1 1 1 1 1 1 1)
                (() () () () () () () () ()
                 (3 (2 5 7 29 53)
                    (4 4 1 1 1)
                    (() () () () ()))
                 ))
             ))
        ))))

(defthm secp256k1-prime-is-prime
  (rtl::primep (secp256k1-prime))
  :hints (("Goal"
           :in-theory (enable secp256k1-prime
                              rtl::certify-prime)
           :use (:instance rtl::certification-theorem
                 (p (secp256k1-prime))
                 (c *secp256k1-prime-pratt-cert*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some theorems about p.

(defthmd secp256k1-prime>2
  (< 2 (secp256k1-prime))
  :hints (("Goal" :in-theory (enable secp256k1-prime))))

(defthm secp256k1-prime-linear ; a very strong linear rule
  (= (secp256k1-prime)
     115792089237316195423570985008687907853269984665640564039457584007908834671663)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable secp256k1-prime))))

(defthm secp256k1-prime-type-prescription
  (and (integerp (secp256k1-prime))
       (< 1 (secp256k1-prime)))
  :rule-classes :type-prescription)
