; A (very simple) verified R1CS to check whether X is a bit (0 or 1)
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
(include-book "kestrel/crypto/r1cs/gadgets" :dir :system)
(local (include-book "kestrel/crypto/r1cs/gadgets/boolean-rules" :dir :system))
;(local (include-book "kestrel/lists-light/nth" :dir :system))

;; Assume the constraint-vector is just [1, x].  The constraint is (1-x) * x = 0.
;; Would be a constant but we can't eval.
;; todo: maybe dont separate inputs from outputs (this example has no outputs)
(defund bit-constraint-for-x (prime)
  (r1cs-constraint (list 1 (pfield::minus1 prime)) ;A
                   (list 0 1) ;B
                   (list 0 0) ;C
                   ))

(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(defthm bit-constraint-for-x-correct
  (implies (and ;(fep x)
            (primep prime)
            (r1cs-valuationp valuation prime)
            (valuation-bindsp valuation'x)
            (equal x (lookup-equal 'x valuation)))
           (iff (r1cs-constraint-holdsp (bit-constraint-for-x prime)
                                        valuation
                                        '(x)
                                        prime)
                (bitp x)))
  :hints (("Goal"
           :in-theory (e/d (bitp ;minus1
                            bit-constraint-for-x
                            ;;sub
                            r1cs-constraint-holdsp
                            )
                           (pfield::equal-of-0-and-mul)))))

;; An R1CS that simply checks whether X is a bit.
(defun r1cs-for-bitp-of-x ()
  (r1cs 7 ; the prime
        '(x) ;vars
        (list (bit-constraint-for-x 7))))

(defthm primep-of-7
  (primep 7)
  :hints (("Goal" :in-theory (enable (:e primep)))))

(defthm correctness-of-r1cs-for-bitp-of-x
  (implies (and (r1cs-valuationp valuation 7)
                (valuation-bindsp valuation 'x))
           (iff (r1cs-holdsp (r1cs-for-bitp-of-x) valuation)
                (bitp (lookup-equal 'x valuation))))
  :hints (("Goal" :in-theory (disable (:e r1cs-for-bitp-of-x)
                                      (:e bit-constraint-for-x)))))
