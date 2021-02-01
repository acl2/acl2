; Primes Library: Subgroup prime for the twisted Edwards curve "Edwards BLS12"
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "Edwards BLS12" is defined in the Zexe paper:
;;   https://eprint.iacr.org/2018/962.pdf
;; and here:
;;   https://github.com/AleoHQ/snarkOS/tree/master/curves

;; This file proves primality of the order of the largest subgroup of
;; (aka the "Scalar Field Size" of)
;; the twisted Edwards curve "Edwards BLS12",

;; For primality of the base field in which "Edwards BLS12" is defined,
;; see bls12-377-prime.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "kestrel/number-theory/defprime" :dir :system)

(defprime edwards-bls12-subgroup-prime
  2111115437357092606062206234695386632838870926408408195193685246394721360383

  ;; Pratt certificate for the twisted Edwards curve "Edwards BLS12".
  (5 (2 1553 1282495723 4153589585267 127594226306900005382664386181896662579473947460767)
     (1 1 1 1 1)
     (() ()
      ;; 1282495723
      (5 (2 3 229 933403)
         (1 1 1 1)
         (() () () ()))
      ;; 4153589585267
      (2 (2 11 188799526603)
         (1 1 1)
         (() ()
          ;; 188799526603
          (3 (2 3 17 71 1187 7321)
             (1 2 1 1 1 1)
             (() () () () () ()))))
      ;; 127594226306900005382664386181896662579473947460767
      (5 (2 73 149 181 11959 11892231440692483 227853185823450011796547)
         (1 1 1 1 1 1 1)
         (() () () () ()
          ;; 11892231440692483
          (3 (2 3 11 71 109 601 38740043)
             (1 1 1 1 1 1 1)
             (() () () () () ()
              ;; 38740043
              (5 (2 11 17 103583)
                 (1 1 1 1)
                 (() () () ()))
              )
             )
          ;; 227853185823450011796547
          (3 (2 3 12511 14293 212367687039617)
           (1 1 1 1 1)
           (() () () ()
            ;; 212367687039617
            (3 (2 107 15505818271)
               (7 1 1)
               (() ()
                ;; 15505818271
                (6 (2 3 5 516860609)
                   (1 1 1 1)
                   (() () ()
                    ;; 516860609
                    (3 (2 11 734177)
                       (6 1 1)
                       (() () ())))))))))))))
