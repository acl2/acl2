; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "INTERVAL")

(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "noninterval-arith-support"))

(include-book "kestrel/arithmetic-light/max" :dir :system)
(include-book "kestrel/arithmetic-light/min" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; min

#!ACL2
(defruled min-when-<
  (implies (< x y)
           (equal (min x y)
                  x))
  :enable min)

#!ACL2
(defrule min-when-<-cheap
  (implies (< x y)
           (equal (min x y)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by min-when-<)

#!ACL2
(defruled min-when-<=
  (implies (<= y x)
           (equal (min x y)
                  y))
  :enable min)

#!ACL2
(defrule min-when-<=-cheap
  (implies (<= y x)
           (equal (min x y)
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by min-when-<=)

#!ACL2
(defrule <=-of-min-and-arg1-linear
  (<= (min x y) x)
  :rule-classes :linear)

#!ACL2
(defrule <=-of-min-and-arg2-linear
  (<= (min x y) y)
  :rule-classes :linear)

#!ACL2
(defrule associativity-of-min
  (equal (min (min x y) z)
         (min x (min y z)))
  :enable min)

#!ACL2
(defrule commutativity-of-min
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (min y x)
                  (min x y)))
  :enable min)

#!ACL2
(defrule commutativity-2-of-min
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (min y (min x z))
                  (min x (min y z))))
  :enable min)

#!ACL2
(defrule idempotence-of-min
  (equal (min x x)
         x)
  :enable min)

#!ACL2
(defrule contraction-of-min
  (equal (min x (min x y))
         (min x y))
  :enable min)

;; This is subsumed by <-of-min-arg1 and <-of-min-arg1.
#!ACL2
(defruled monotonicity-of-min
  (implies (and (<= x0 x1)
                (<= y0 y1))
           (<= (min x0 y0)
               (min x1 y1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; max

#!ACL2
(defruled max-when-<
  (implies (< y x)
           (equal (max x y)
                  x))
  :enable max)

#!ACL2
(defrule max-when-<-cheap
  (implies (< y x)
           (equal (max x y)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by max-when-<)

#!ACL2
(defruled max-when-<=
  (implies (<= x y)
           (equal (max x y)
                  y))
  :enable max)

#!ACL2
(defrule max-when-<=-cheap
  (implies (<= x y)
           (equal (max x y)
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by max-when-<=)

#!ACL2
(defrule <=-of-arg1-and-max-linear
  (<= x (max x y))
  :rule-classes :linear)

#!ACL2
(defrule <=-of-arg2-and-max-linear
  (<= y (max x y))
  :rule-classes :linear)

#!ACL2
(defrule associativity-of-max
  (equal (max (max x y) z)
         (max x (max y z)))
  :enable max)

#!ACL2
(defrule commutativity-of-max
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (max y x)
                  (max x y)))
  :enable max)

#!ACL2
(defrule commutativity-2-of-max
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (max y (max x z))
                  (max x (max y z))))
  :enable max)

#!ACL2
(defrule idempotence-of-max
  (equal (max x x)
         x)
  :enable max)

#!ACL2
(defrule contraction-of-max
  (equal (max x (max x y))
         (max x y))
  :enable max)

;; This is subsumed by <-of-max-arg1 and <-of-max-arg1.
#!ACL2
(defruled monotonicity-of-max
  (implies (and (<= x0 x1)
                (<= y0 y1))
           (<= (max x0 y0)
               (max x1 y1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; min and max

#!ACL2
(defrule min-max-absorption
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (min x (max x y))
                  x))
  :enable (min
           max))

;; If max is in the opposite order, we happen to not need the hyps.
#!ACL2
(defrule min-max-absorption-2
  (equal (min x (max y x))
         x)
  :enable (min
           max))

#!ACL2
(defrule max-min-absorption
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (max x (min x y))
                  x))
  :enable (min
           max))

;; If min is in the opposite order, we happen to not need the hyps.
#!ACL2
(defrule max-min-absorption-2
  (equal (max x (min y x))
         x)
  :enable (min
           max))

;;;;;;;;;;;;;;;;;;;;

;; Distributivity of + over min
#!ACL2
(defruled +-of-min
  (equal (+ x (min y z))
         (min (+ x y) (+ x z)))
  :enable min)

#!ACL2
(defrule min-of-+-factor
  (equal (min (+ x y) (+ x z))
         (+ x (min y z)))
  :by +-of-min)

#!ACL2
(theory-invariant (incompatible! (:rewrite +-of-min)
                                 (:rewrite min-of-+-factor)))

;; Distributivity of + over max
#!ACL2
(defruled +-of-max
  (equal (+ x (max y z))
         (max (+ x y) (+ x z)))
  :enable max)

#!ACL2
(defrule max-of-+-factor
  (equal (max (+ x y) (+ x z))
         (+ x (max y z)))
  :by +-of-max)

#!ACL2
(theory-invariant (incompatible! (:rewrite +-of-max)
                                 (:rewrite max-of-+-factor)))

;;;;;;;;;;;;;;;;;;;;

#!ACL2
(defruled --of-min
  (equal (- (min x y))
         (max (- x) (- y)))
  :enable (min
           max))

#!ACL2
(defrule max-of---factor
  (equal (max (- x) (- y))
         (- (min x y)))
 :by --of-min)

#!ACL2
(theory-invariant (incompatible! (:rewrite --of-min)
                                 (:rewrite max-of---factor)))

#!ACL2
(defruled --of-max
  (equal (- (max x y))
         (min (- x) (- y)))
  :enable (min
           max))

#!ACL2
(defrule min-of---factor
  (equal (min (- x) (- y))
         (- (max x y)))
 :by --of-max)

#!ACL2
(theory-invariant (incompatible! (:rewrite --of-max)
                                 (:rewrite min-of---factor)))

;;;;;;;;;;;;;;;;;;;;

#!ACL2
(defruled *-of-min
  (implies (rationalp x)
           (equal (* x (min y z))
                  (if (<= 0 x)
                      (min (* x y) (* x z))
                    (max (* x y) (* x z)))))
  :nonlinearp t
  :enable (min
           max))

#!ACL2
(defrule min-of-*-when-<=-0
  (implies (and (rationalp x)
                (<= 0 x))
           (equal (min (* x y) (* x z))
                  (* x (min y z))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :by *-of-min)

#!ACL2
(theory-invariant (incompatible! (:rewrite *-of-min)
                                 (:rewrite min-of-*-when-<=-0)))

#!ACL2
(defrule max-of-*-when-not-<-0
  (implies (and (rationalp x)
                (not (< 0 x)))
           (equal (max (* x y) (* x z))
                  (* x (min y z))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :use *-of-min)

#!ACL2
(theory-invariant (incompatible! (:rewrite *-of-min)
                                 (:rewrite max-of-*-when-not-<-0)))

#!ACL2
(defruled *-of-max
  (implies (rationalp x)
           (equal (* x (max y z))
                  (if (<= 0 x)
                      (max (* x y) (* x z))
                    (min (* x y) (* x z)))))
  :nonlinearp t
  :enable (min
           max))

#!ACL2
(defrule max-of-*-when-<=-0
  (implies (and (rationalp x)
                (<= 0 x))
           (equal (max (* x y) (* x z))
                  (* x (max y z))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :by *-of-max)

#!ACL2
(theory-invariant (incompatible! (:rewrite *-of-max)
                                 (:rewrite max-of-*-when-<=-0)))

#!ACL2
(defrule min-of-*-when-not-<-0
  (implies (and (rationalp x)
                (not (< 0 x)))
           (equal (min (* x y) (* x z))
                  (* x (max y z))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :use *-of-max)

#!ACL2
(theory-invariant (incompatible! (:rewrite *-of-max)
                                 (:rewrite min-of-*-when-not-<-0)))
