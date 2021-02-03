; Primes Library: Group prime for BN-254
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "kestrel/number-theory/defprime" :dir :system)

;; This is the order of the BN254 curve, and also the order of the field in
;; which the BabyJubjub curve is defined.
(defprime bn-254-group-prime
  21888242871839275222246405745257275088548364400416034343698204186575808495617
  ;; the following certificate was generated using mathematica's FactorInteger and PrimitiveRoot
  (5 (2 3 13 29 983 11003 237073 405928799 1670836401704629 13818364434197438864469338081)
     (28 2 1 1 1 1 1 1 1 1)
     (() () () () () () ()
      (22 (2 11 3691 4999)
          (1 1 1 1)
          (() () () ()))
      (2 (2 3 5156902474397)
         (2 4 1)
         (() ()
          (2 (2 107 12048837557)
             (2 1 1)
             (() ()
              (2 (2 7 661 93001)
                 (2 2 1 1)
                 (() () () ()))
              ))
          ))
      (3 (2 5 823 1593227 65865678001877903)
         (5 1 1 1 1)
         (() () () ()
          (5 (2 83 379 1637 639533339)
             (1 1 1 1 1)
             (() () () ()
              (2 (2 229 853 1637)
                 (1 1 1 1)
                 (() () () ()))
              ))
          ))
      )))
