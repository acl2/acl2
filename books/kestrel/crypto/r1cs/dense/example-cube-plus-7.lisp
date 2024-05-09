; A (simple) verified R1CS to check whether Y=X^3+7.
;
; Copyright (C) 2019-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "r1cs")
(include-book "rules")
;(include-book "kestrel/crypto/r1cs/gadgets" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))

;; We use 19 as the prime (must be larger than 7).

;gen
(defthm fep-of-7
  (equal (pfield::fep 7 prime)
         (< 7 prime))
  :hints (("Goal" :in-theory (enable pfield::fep))))

(defthm primep-of-19
  (primep 19)
  :hints (("Goal" :in-theory (enable primep))))

;; The goal of this example: Create an R1CS that corresponds to this function
;; (actually, that checks whether y is equal to cube-plus-7(x)) and prove it
;; correct.
(defun cube-plus-7 (x)
  (declare (xargs :guard (pfield::fep x 19)))
  (pfield::add (pfield::mul x (pfield::mul x x 19) 19)
               7
               19))

;; Let's try to compute y = x^3 + 7.
;; Approach: w1=x^2.  w2=x^3. w3=x^3+7.
(defun r1cs-for-y=x^3+7 ()
  (declare (xargs :guard t))
  (r1cs 19 ;the prime
        '(x ;inputs
          w1 w2 w3 ;intermediate vars
          y) ;outputs
        ;; The vector will be [1,x,w1,w2,w3,y]
        (list ;;w1=x^2
         (r1cs-constraint (list 0 1 0 0 0 0) ;x
                          (list 0 1 0 0 0 0) ;x
                          (list 0 0 1 0 0 0) ;w1
                          )
          ;;w2=w1*x
         (r1cs-constraint (list 0 1 0 0 0 0) ;x
                          (list 0 0 1 0 0 0) ;w1
                          (list 0 0 0 1 0 0) ;w2
                          )
         ;;w3=w2+7
         (r1cs-constraint (list 7 0 0 1 0 0) ;7+w2
                          (list 1 0 0 0 0 0) ;1
                          (list 0 0 0 0 1 0) ;w3
                          )
         ;;y=w3 (TODO: omit this constraint?)
         (r1cs-constraint (list 0 0 0 0 1 0) ;w3
                          (list 1 0 0 0 0 0) ;1
                          (list 0 0 0 0 0 1) ;y
                          ))))

;Soundness
(defthm soundness-of-r1cs-for-y=x^3+7
  (implies (and (r1cs-valuationp valuation 19)
                (valuation-bindsp valuation 'x)
                (valuation-bindsp valuation 'y)
                (valuation-bindsp valuation 'w1)
                (valuation-bindsp valuation 'w2)
                (valuation-bindsp valuation 'w3))
           (implies (r1cs-holdsp (r1cs-for-y=x^3+7) valuation)
                    (equal (lookup-equal 'y valuation)
                           (cube-plus-7 (lookup-equal 'x valuation)))))
  :hints (("Goal" :in-theory (enable r1cs-holdsp r1cs-constraint-holdsp))))

;; Completeness. There exists a valuation that makes the R1CS hold.
;; TODO: Improve the form of this ("there exist w1, w2, w3 such that ...")
(defthm completeness-of-r1cs-for-y=x^3+7
  (implies (and (pfield::fep x 19)
                (pfield::fep y 19))
           (implies (equal y (cube-plus-7 x))
                    (r1cs-holdsp (r1cs-for-y=x^3+7)
                                 (acons 'x x
                                        (acons 'y y
                                               (acons 'w1 (pfield::mul x x 19)
                                                      (acons 'w2 (pfield::mul x (pfield::mul x x 19) 19)
                                                             (acons 'w3 (pfield::add 7 (pfield::mul x (pfield::mul x x 19) 19) 19)
                                                                    valuation))))))))
  :hints (("Goal" :in-theory (enable r1cs-holdsp r1cs-constraint-holdsp))))
