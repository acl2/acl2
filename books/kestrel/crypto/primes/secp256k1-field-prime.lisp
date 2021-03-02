; Primes Library: Field Prime for secp256k1
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We introduce the prime that characterizes the prime field
; over which the secp256k1 elliptic curve is defined.
; This elliptic curve is specified in
; "Standards for Efficient Cryptography 1 (SEC 1)"
; (http://www.secg.org/sec1-v2.pdf) and
; "Standards for Efficient Cryptography 2 (SEC 2)"
; (http://www.secg.org/sec2-v2.pdf).
; This prime is called p in SEC 1 and 2.
; See, in particular, Section 2 of SEC 2.

; Also see ./secp256k1-group-prime.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "kestrel/number-theory/defprime" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprime secp256k1-field-prime

  #xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

  ;; The following Pratt certificate was generated using
  ;; Mathematica's FactorInteger and PrimitiveRoot.
  (3 (2 3 7 13441 205115282021455665897114700593932402728804164701536103180137503955397371)
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
      )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This prime is 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1.

(assert-event (equal (secp256k1-field-prime)
                     (- (- (- (- (- (- (- (expt 2 256) (expt 2 32))
                                       (expt 2 9))
                                    (expt 2 8))
                                 (expt 2 7))
                              (expt 2 6))
                           (expt 2 4))
                        1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This prime has length 256 bits.

(assert-event (equal (integer-length (secp256k1-field-prime)) 256))
