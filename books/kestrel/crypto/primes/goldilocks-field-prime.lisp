; Primes Library:
; Prime for the "Goldilocks Field" as used in Plonky2 and Polygon Miden.
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The Plonky2 Repo is here:
;;   https://github.com/mir-protocol/plonky2

;; The current file proves primality of the Goldilocks Field prime
;;   2^64 - 2^32 + 1

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "kestrel/number-theory/defprime" :dir :system)

(defprime goldilocks-prime
  18446744069414584321

  ;; Pratt certificate for the Goldilocks Field prime
  (7 (2 3 5 17 257 65537)
     (32 1 1 1 1 1)
     (() () () () ()
      ;; 65537
      (3 (2)
         (16)
         (())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Make sure we used the right number to define (goldilocks-prime)

(assert-event
 (equal (goldilocks-prime)
        (+ (- (expt 2 64) (expt 2 32)) 1)))
