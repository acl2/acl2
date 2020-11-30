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

(include-book "projects/quadratic-reciprocity/euclid" :dir :system) ;for rtl::primep
(local (include-book "projects/quadratic-reciprocity/pratt" :dir :system))

;; Prevent very expensive calls to primep
(in-theory (disable (:e rtl::primep)))

;; This is the order of the BN254 curve, and also the order of the field in
;; which the BabyJubjub curve is defined.
(defconst *bn-254-group-prime*
  21888242871839275222246405745257275088548364400416034343698204186575808495617)

(defund bn-254-group-prime ()
  (declare (xargs :guard t))
  *bn-254-group-prime*)

;; (in-theory (disable (:e bn-254-group-prime)))

;; We use Russinoff's algorithm from "Pratt certification and the primality of 2^255 - 19"
;; where a Pratt certificate of n is a tree
;; (r (p1 ... pn) (e1 ... en) (c1 ... cn))
;; such that
;; 1. r is primitive root of n
;; 2. n - 1 = (p1^e1)...(pn^en)
;; 3. ci is a pratt certificate of pi.

;; the following certificate was generated using mathematica's FactorInteger and PrimitiveRoot
(defconst *bn-254-group-prime-pratt-cert*
  '(5 (2 3 13 29 983 11003 237073 405928799 1670836401704629 13818364434197438864469338081)
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

;; Since primep may often be disabled and this cannot be efficiently executed.
(defthm primep-of-bn-254-group-prime-constant
  (rtl::primep *bn-254-group-prime*)
  :hints (("Goal" :in-theory (enable (:e rtl::certify-prime))
           :use (:instance rtl::certification-theorem
                           (p *bn-254-group-prime*)
                           (c *bn-254-group-prime-pratt-cert*)))))

(defthm primep-of-bn-254-group-prime
  (rtl::primep (bn-254-group-prime))
  :hints (("Goal" :in-theory (enable (:e bn-254-group-prime) (:e rtl::certify-prime))
           :use (:instance rtl::certification-theorem
                           (p *bn-254-group-prime*)
                           (c *bn-254-group-prime-pratt-cert*)))))

;; To allow the :linear rule to be created.
(local (in-theory (disable (:e bn-254-group-prime))))

(defthm bn-254-group-prime-linear
  (= (bn-254-group-prime) *bn-254-group-prime*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable (:e bn-254-group-prime)))))

;; (defthm <-of-2-and-bn-254-group-prime
;;   (< 2 (bn-254-group-prime))
;;   :rule-classes ((:rewrite :linear))
;;   :hints (("Goal" :in-theory (enable (:e bn-254-group-prime)))))
