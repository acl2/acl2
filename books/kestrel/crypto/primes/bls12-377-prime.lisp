; Primes Library: Scalar Field prime for BLS12-377
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Authors: Eric McCarthy (mccarthy@kestrel.edu)
;                       Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The elliptic curve BLS12-377 contains a subgroup with a large prime order.
;; The certificate in this file can be used to prove primality of this number.
;; This prime number is usually called the "scalar field prime" since the
;; arithmetic circuits used for zk-SNARKs are computed modulo this prime.
;; In the first reference below, the prime is also called 'r'.

;; References for BLS12-377:
;; https://eprint.iacr.org/2018/962.pdf
;; https://github.com/AleoHQ/snarkOS/blob/c9e5f823b8493f8c3a6c43e6f4dfd16173b99957/curves/README.md#bls12-377

;; See also ../ecurve/bls12-377-domain-parameters.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "kestrel/number-theory/defprime" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprime bls12-377-scalar-field-prime

  #x12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001

  ;; The following certificate was generated using
  ;; sagecell.sagemath.org and wolframalpha.com
  ;; For example,
  ;; SageCellServer:
  ;;   k = GF(8444461749428370424248824938781546531375899335154063827935233455917409239041, modulus="primitive")
  ;;   k.gen()
  ;;   F = factor(8444461749428370424248824938781546531375899335154063827935233455917409239040)
  ;;   list(F)
  ;; See also Mathematica's FactorInteger and PrimitiveRoot.
  (22 (2 3 5 7 13 499 958612291309063373 9586122913090633729)
      (47 1 1 1 1 1 1 2)
      (() () () () () ()
       ;; 958612291309063373
       (2 (2 29 167 49484425527001)
          (2  1   1  1)
          (() () ()
           ;; 49484425527001
           (14 (2 3 5 1832756501)
               (3 3 3 1)
               (() () ()
                ;; 1832756501
                (2 (2 5 29 126397)
                   (2 3 1 1)
                   (() () () ()))))))
       ;; 9586122913090633729
       (11 (2 3 7 13 499)
           (46 1 1 1 1)
           (() () () () ()))))

  :parents (bls12-377-domain-parameters)

  :short "The prime @($r$)."

  :long
  (xdoc::topstring
   (xdoc::p
    "The prime @($r$) is the scalar field size of
     the curve @($E_{BLS}$), and is also the base field size of
     the twisted Edwards curve @($E_{Ed/BLS}$).")
   (xdoc::p
    "@($r$) is computed from the
     <see topic='@(url ecurve::bls12-377-parameter-x)'>parameter x</see>:
     @([
        r = x^4 - x^2 + 1
      ])")
   (xdoc::p
    "Figure 16 lists its value in hexadecimal:")
   (xdoc::codeblock
    "0x12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This prime has length 253 bits.

(assert-event (equal (integer-length (bls12-377-scalar-field-prime)) 253))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Decimal version of this prime.

(assert-event
 (equal (bls12-377-scalar-field-prime)
        8444461749428370424248824938781546531375899335154063827935233455917409239041
        ))
