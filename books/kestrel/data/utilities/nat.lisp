; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/basic/arith-equiv-defs" :dir :system))
(local (include-book "std/util/defredundant" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; nfix rules

(defrule natp-of-nfix
  (natp (nfix x)))

(defrule nfix-when-natp
  (implies (natp x)
           (equal (nfix x)
                  x))
  :enable nfix)

(defruled nfix-when-not-natp
  (implies (not (natp x))
           (equal (nfix x)
                  0))
  :enable nfix)

(defrule nfix-when-not-natp-cheap
  (implies (not (natp x))
           (equal (nfix x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by nfix-when-not-natp)

(defrule nfix-when-not-natp-type-prescription
  (implies (not (natp x))
           (equal (nfix x)
                  0))
  :rule-classes :type-prescription)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; nat-fix

(define nat-fix ((n natp))
  (mbe :logic (nfix n)
       :exec (the unsigned-byte n))
  :enabled t
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; nat-equiv

(std::defredundant
  :names (int-equiv
          nat-equiv))

(defequiv nat-equiv
  :package :equiv)

(defrefinement int-equiv nat-equiv
  :package :equiv1)

(defrule nfix-nat-equiv-congruence
  (implies (nat-equiv x0 x1)
           (equal (nfix x0)
                  (nfix x1)))
  :rule-classes :congruence)

(defrule nfix-under-nat-equiv
  (nat-equiv (nfix x)
             x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; nat-equal

(define nat-equal
  ((x natp)
   (y natp))
  (mbe :logic (nat-equiv x y)
       :exec (= (the unsigned-byte x) (the unsigned-byte y)))
  :enabled t
  :inline t)
