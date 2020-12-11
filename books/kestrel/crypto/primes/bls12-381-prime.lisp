; Primes Library: Scalar Field prime for BLS-381
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The prime r used for the curve BLS12-381
;; is described in
;;   https://www.ietf.org/id/draft-irtf-cfrg-pairing-friendly-curves-07.html

(in-package "PRIMES")

(include-book "defprime")

;; This is the order of the groups G1 and G2 from BLS12-381.  Also known as r.
;; We intend to add xdoc for this later.
(defprime bls12-381-scalar-field-prime
  52435875175126190479447740508185965837690552500527637822603658699938581184513
  ;; Pratt certificate for BLS-381 prime subgroup (scalar field) aka "r".
  ;; The following certificate was generated using
  ;; sagecell.sagemath.org and wolframalpha.com
  ;; For example,
  ;; SageCellServer:
  ;;   k = GF(52435875175126190479447740508185965837690552500527637822603658699938581184513, modulus="primitive")
  ;;   k.gen()
  ;;   F = factor(52435875175126190479447740508185965837690552500527637822603658699938581184512)
  ;;   list(F)
  ;; See also Mathematica's FactorInteger and PrimitiveRoot.
  (7 (2 3 11 19 10177 125527 859267 906349 2508409 2529403 52437899 254760293)
     (32 1 1 1 1 1 1 2 1 1 1 2)
     (() () () () () ()
      ;; 859267
      (2 (2 3 47737)
         (1 2 1)
         (() () ()))
      ;; 906349
      (2 (2 3 47 1607)
         (2 1 1 1)
         (() () () ()))
      ;; 2508409
      (11 (2 3 7 79)
          (3 4 2 1)
          (() () () ()))
      ;; 2529403
      (2 (2 3 23 18329)
         (1 1 1 1)
         (() () () ()))
      ;; 52437899
      (2 (2 43 609743)
         (1 1 1)
         (() ()
          ;; 609743
          (5 (2 7 97 449)
             (1 1 1 1)
             (() () () ()))
          ))
      ;; 254760293
      (2 (2 63690073)
         (2 1)
         (()
          ;; 63690073
          (7 (2 3 2653753)
             (3 1 1)
             (() ()
              ;; 2653753
              (5 (2 3 110573)
                 (3 1 1)
                 (() ()
                  ;; 110573
                  (3 (2 7 11 359)
                     (2 1 1 1)
                     (() () () ()))
                  ))
              ))
          ))
      )))
