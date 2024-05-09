; A (simple) verified R1CS to check whether Y^2=X.
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
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;; The vector is [1,x,y].  The constraint is y * y = x.
(defun constraint-for-x=y^2 ()
  (declare (xargs :guard t))
  (r1cs-constraint (list 0 0 1) ;A
                   (list 0 0 1) ;B
                   (list 0 1 0) ;C
                   ))

(defthm primep-of-13
  (primep 13)
  :hints (("Goal" :in-theory (enable primep))))

(defun r1cs-for-x=y^2 ()
  (declare (xargs :guard t))
  (r1cs 13  ;the prime
        '(x ;inputs
          ;;no intermediate vars
          y) ;outputs
        (list (constraint-for-x=y^2))))

(defun check-that-x-is-y-squared (x y)
  (declare (xargs :guard (and (pfield::fep x 13)
                              (pfield::fep y 13))
                  :guard-hints (("Goal" :in-theory (enable r1cs-valuationp)))))
  (r1cs-holdsp (r1cs-for-x=y^2) (acons 'x x (acons 'y y nil))))

(defthm correctness-of-r1cs-for-x=y^2
  (implies (and (r1cs-valuationp valuation 13)
                (valuation-bindsp valuation 'x)
                (valuation-bindsp valuation 'y))
           (iff (r1cs-holdsp (r1cs-for-x=y^2) valuation)
                (equal (lookup-equal 'x valuation)
                       (pfield::mul (lookup-equal 'y valuation)
                            (lookup-equal 'y valuation)
                            13))))
  :hints (("Goal" :in-theory (enable R1CS-CONSTRAINT-HOLDSP))))

(in-theory (disable R1CS-HOLDSP r1cs-for-x=y^2 (:e R1CS-FOR-X=Y^2)))

(defthm correctness-of-check-that-x-is-y-squared
  (implies (and (pfield::fep x 13)
                (pfield::fep y 13))
           (iff (check-that-x-is-y-squared x y)
                (equal x (pfield::mul y y 13))))
  :hints (("Goal" :in-theory (enable R1CS-VALUATIONP))))
