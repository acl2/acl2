; Primes Library: Group Prime for secp256k1
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We introduce the prime that is the order of the group
; defined by the secp256k1 elliptic curve domain parameters.
; This elliptic curve is specified in
; "Standards for Efficient Cryptography 1 (SEC 1)"
; (http://www.secg.org/sec1-v2.pdf) and
; "Standards for Efficient Cryptography 2 (SEC 2)"
; (http://www.secg.org/sec2-v2.pdf).
; This prime is called n in SEC 1 and 2.
; See, in particular, Section 2 of SEC 2.

; Also see ./secp256k1-field-prime.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "kestrel/number-theory/defprime" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprime secp256k1-group-prime

  #xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

  ;; Pratt certificate for secp256k1 group order prime.
  ;; The following certificate was generated using
  ;; sagecell.sagemath.org and wolframalpha.com
  ;; For example,
  ;; SageCellServer:
  ;;   k = GF(115792089237316195423570985008687907852837564279074904382605163141518161494337, modulus="primitive")
  ;;   k.gen()
  ;;   F = factor(115792089237316195423570985008687907852837564279074904382605163141518161494336)
  ;;   list(F)
  ;; See also Mathematica's FactorInteger and PrimitiveRoot.
  (7 (2 3 149 631 107361793816595537 174723607534414371449 341948486974166000522343609283189)
     (6 1 1 1 1 1 1)
     (() () () ()
      ;; 107361793816595537
      (3 (2 16699 85831 4681609)
         (4 1 1 1)
         (() () ()
          ;; 4681609
          (23 (2 3 97 2011)
              (3 1 1 1)
              (() () () ()))))
      ;; 174723607534414371449
      (3 (2 17 59 4051 120233 44706919)
         (3 1 1 1 1 1)
         (() () () () ()
          ;; 44706919
          (6 (2 3 797 9349)
             (1 1 1 1)
             (() () () ()))))
      ;; 341948486974166000522343609283189
      (2 (2 3 109 29047611873442575647497758179)
         (2 3 1 1)
         (() () ()
          ;; 29047611873442575647497758179
          (2 (2 293 305873 545358713 297159362677)
             (1 1 1 1 1)
             (() () ()
              ;; 545358713
              (5 (2 41 59 28181)
                 (3 1 1 1)
                 (() () () ()))
              ;; 297159362677
              (2 (2 3 11 461 1627771)
                 (2 2 1 1 1)
                 (() () () ()
                  ;; 1627771
                  (3 (2 3 5 29 1871)
                     (1 1 1 1 1)
                     (() () () () ())))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This prime has length 256 bits.

(assert-event (equal (integer-length (secp256k1-group-prime)) 256))
