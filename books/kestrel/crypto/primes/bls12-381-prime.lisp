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

(include-book "projects/quadratic-reciprocity/euclid" :dir :system) ;for rtl::primep
(local (include-book "projects/quadratic-reciprocity/pratt" :dir :system))

;; Prevent very expensive calls to primep
(in-theory (disable (:e rtl::primep)))

;; This is the order of the groups G1 and G2 from BLS12-381.
(defconst *bls12-381-r*
  52435875175126190479447740508185965837690552500527637822603658699938581184513)

;; We intend to add xdoc for this later.
(defund bls12-381-scalar-field-prime ()
  (declare (xargs :guard t))
  *bls12-381-r*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Pratt certificate for BLS-381 prime subgroup (scalar field) aka "r".

;; To prove that r is indeed a prime,
;; we use Russinoff's algorithm from the paper
;; "Pratt certification and the primality of 2^255 - 19",
;; where a Pratt certificate of n is a tree
;; (r (p1 ... pn) (e1 ... en) (c1 ... cn))
;; such that
;; 1. r is primitive root of n
;; 2. n - 1 = (p1^e1)...(pn^en)
;; 3. ci is a pratt certificate of pi.

;; The following certificate was generated using
;; sagecell.sagemath.org and wolframalpha.com
;; For example,
;; SageCellServer:
;;   k = GF(52435875175126190479447740508185965837690552500527637822603658699938581184513, modulus="primitive")
;;   k.gen()
;;   F = factor(52435875175126190479447740508185965837690552500527637822603658699938581184512)
;;   list(F)
;; See also Mathematica's FactorInteger and PrimitiveRoot.

(defconst *bls12-381-r-pratt-cert*
  '(7 (2 3 11 19 10177 125527 859267 906349 2508409 2529403 52437899 254760293)
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


;; Since primep may often be disabled and this cannot be efficiently executed.
(defthm primep-of-bls12-381-scalar-field-prime-constant
  (rtl::primep *bls12-381-r*)
  :hints (("Goal" :in-theory (enable (:e rtl::certify-prime))
           :use (:instance rtl::certification-theorem
                           (p *bls12-381-r*)
                           (c *bls12-381-r-pratt-cert*)))))

(defthm primep-of-bls12-381-scalar-field-prime
  (rtl::primep (bls12-381-scalar-field-prime))
  :hints (("Goal" :in-theory (enable (:e bls12-381-scalar-field-prime) (:e rtl::certify-prime))
           :use (:instance rtl::certification-theorem
                           (p *bls12-381-r*)
                           (c *bls12-381-r-pratt-cert*)))))

;; To allow the :linear rule to be created.
(local (in-theory (disable (:e bls12-381-scalar-field-prime))))

(defthm bls12-381-scalar-field-prime-linear
  (= (bls12-381-scalar-field-prime) *bls12-381-r*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable (:e bls12-381-scalar-field-prime)))))
