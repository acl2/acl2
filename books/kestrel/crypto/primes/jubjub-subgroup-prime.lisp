; Primes Library: Subgroup prime for the twisted Edwards curve "Jubjub".
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Jubjub is defined in the Zcash Protocol Specification.
;; https://zips.z.cash/protocol/protocol.pdf

;; This file proves primality of r_J, the order of the largest subgroup
;; of the twisted Edwards curve "Jubjub".

;; For primality of the base field in which "Jubjub" is defined,
;; see bls12-381-prime.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "kestrel/number-theory/defprime" :dir :system)

(defprime jubjub-subgroup-prime
  6554484396890773809930967563523245729705921265872317281365359162392183254199

  ;; Pratt certificate for the twisted Edwards curve "Jubjub".
  (6 (2 3 12281 1710050753150114629 203928654140967434528233
        255074062430788457494141376149)
     (1 1 1 1 1 1)
     (() () ()
      ;; 1710050753150114629
      (6 (2 3 11 12954929948106929)
         (2 1 1 1)
         (() () ()
          ;; 12954929948106929
          (3 (2 23 35203613989421)
             (4 1 1)
             (() ()
              ;; 35203613989421
              (2 (2 5 1699 1036009829)
                 (2 1 1 1)
                 (() () ()
                  ;; 1036009829
                  (2 (2 7 499 74149)
                     (2 1 1 1)
                     (() () () ()))))))))
      ;; 203928654140967434528233
      (5 (2 3 6566909 431305263804409)
         (3 2 1 1)
         (() ()
          ;; 6566909
          (2 (2 37 44371)
             (2 1 1)
             (() () ()))
          ;; 431305263804409
          (13 (2 3 7 2567293236931)
              (3 1 1 1)
              (() () ()
               ;; 2567293236931
               (2 (2 3 5 457 187256983)
                  (1 1 1 1 1)
                  (() () () ()
                   ;; 187256983
                   (5 (2 3 11 2837227)
                      (1 1 1 1)
                      (() () ()
                       ;; 2837227
                       (2 (2 3 7 43 1571)
                          (1 1 1 1 1)
                          (() () () () ()))))))))))
      ;; 255074062430788457494141376149
      (2 (2 3 311 5521 19861 623312455501769069)
         (2 1 1 1 1 1)
         (() () () () ()
          ;; 623312455501769069
          (2 (2 7 1361 16356472538621)
             (2 1 1 1)
             (() () ()
              ;; 16356472538621
              (2 (2 5 23 62701 567097)
                 (2 1 1 1 1)
                 (() () () () ()))))))))
  )
