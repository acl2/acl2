; bls12-377-curves Library: Base Field prime for BLS12-377
;
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The elliptic curve BLS12-377 is defined in a base field
;; that is a prime number with 377 bits.

;; The certificate in this file can be used to prove primality of this number.
;; This prime number is usually called the "base field prime" since the
;; arithmetic circuits used for zk-SNARKs are computed modulo this prime.
;; In the first reference below, the prime is also called 'p'; in code,
;; it is often called 'q'.

;; References for BLS12-377:
;; https://eprint.iacr.org/2018/962.pdf
;; https://github.com/AleoHQ/snarkOS/blob/c9e5f823b8493f8c3a6c43e6f4dfd16173b99957/curves/README.md#bls12-377

;; See also ../ecurve/bls12-377-domain-parameters.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "kestrel/number-theory/defprime" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprime bls12-377-base-field-prime

  #x1ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001

  ;; The following certificate was generated using
  ;; sagecell.sagemath.org and wolframalpha.com
  ;; For example,
  ;; SageCellServer:
  ;;   k = GF(258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458177, modulus="primitive")
  ;;   k.gen()
  ;;   F = factor(258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458176)
  ;;   list(F)
  ;; See also Mathematica's FactorInteger and PrimitiveRoot.

  (15 (2 3 7 13 53 409 499 2557 6633514200929891813 73387170334035996766247648424745786170238574695861388454532790956181)
      (46 1 1 1 1 1 1 1 1 1)
      (() () () () () () () ()
       ;; 6633514200929891813
       (2 (2 19 25537 47521 71924131)
          (2 1 1 1 1)
          (() () () ()
           ;; 71924131
           (2 (2 3 5 317 2521)
               (1 2 1 1 1)
               (() () () () ()))))
       ;; 73387170334035996766247648424745786170238574695861388454532790956181
       (3 (2 5 11 23 494527005853 3721412928183745004194199 7880826209898991662826602799)
          (2 1 1 1 1 1 1)
          (() () () ()
           ;; 494527005853
           (5 (2 3 11 167 22433633)
              (2 1 1 1 1)
              (() () () ()
               ;; 22433633
               (3 (2 13 53927)
                  (5 1 1)
                  (() () ()))))
           ;; 3721412928183745004194199
           (13 (2 19 97931919162730131689321)
               (1 1 1)
               (() ()
                ;; 97931919162730131689321
                (3 (2 5 11 222572543551659390203)
                   (3 1 1 1)
                   (() () ()
                    ;; 222572543551659390203
                    (2 (2 111286271775829695101)
                       (1 1)
                       (()
                        ;; 111286271775829695101
                        (2 (2 5 73 8263 1844934619849)
                           (2 2 1 1 1)
                           (() () () ()
                            ;; 1844934619849
                            (14 (2 3 76872275827)
                                (3 1 1)
                                (() ()
                                 ;; 76872275827
                                 (2 (2 3 17 19 23 229 443)
                                    (1 1 2 1 1 1 1)
                                    (() () () () () () ()))))))))))))
           ;; 7880826209898991662826602799
           (21 (2 3 53 4777599223 5187222954756607)
               (1 1 1 1 1)
               (() () ()
                ;; 4777599223
                (3 (2 3 11 59 408971)
                   (1 2 1 1 1)
                   (() () () () ()))
                ;; 5187222954756607
                (3 (2 3 19 5301089 8583511)
                   (1 1 1 1 1)
                   (() () ()
                    ;; 5301089
                    (3 (2 13 12743)
                       (5 1 1)
                       (() () ()))
                    ;; 8583511
                    (6 (2 3 5 13 1693)
                       (1 1 1 2 1)
                       (() () () () ()))))))))))

  :parents (ecurve::bls12-377-domain-parameters)

  :short "The prime @($q$)."

  :long
  (xdoc::topstring
   (xdoc::p
    "The prime @($q$) is the base field size of
     the curve @($E_{BLS}$).")
   (xdoc::p
    "@($q$) is computed from the
     <see topic='@(url ecurve::bls12-377-parameter-x)'>parameter x</see>:
     @([
        q = (x - 1)^{2}r/3 + x
      ])
     where
     @([
        r = x^4 - x^2 + 1
      ]).")
   (xdoc::p
    "Figure 16 of the Zexe paper lists its value in hexadecimal:")
   (xdoc::codeblock
    "0x1ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Note that the smallest quadratic non-residue
; for *BLS12-377-BASE-FIELD-PRIME*
; is 5.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This prime has length 377 bits.

(assert-event (equal (integer-length (bls12-377-base-field-prime)) 377))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Decimal version of this prime.

(assert-event
 (equal (bls12-377-base-field-prime)
        258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458177
        ))
