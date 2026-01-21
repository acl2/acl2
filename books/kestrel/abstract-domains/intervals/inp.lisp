; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "INTERVAL")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/utilities/arith-fix-and-equiv-defs" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "noninterval-arith-support"))
(include-book "core")
(include-book "exact")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inp
  ((r rationalp)
   (interval intervalp))
  :returns (yes/no booleanp)
  :parents (intervals)
  :short "Check if a number is contained within an interval."
  (and (not (emptyp interval))
       (let ((min (min interval))
             (max (max interval)))
         (and (or (not min)
                  (<= min (rational-fix r)))
              (or (not max)
                  (<= (rational-fix r) max))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t inp)))

(defrule inp-type-prescription
  (booleanp (inp r interval))
  :rule-classes ((:type-prescription :typed-term (inp r interval))))

(defrule inp-when-rational-equiv-congruence
  (implies (rational-equiv r0 r1)
           (equal (inp r0 interval)
                  (inp r1 interval)))
  :rule-classes :congruence
  :enable inp)

(defrule inp-when-equiv-congruence
  (implies (equiv interval0 interval1)
           (equal (inp r interval0)
                  (inp r interval1)))
  :rule-classes :congruence
  :enable inp)

(defrule inp-of-rfix
  (equal (inp (rfix r) interval)
         (inp r interval))
  :enable inp)

(defruled inp-when-not-intervalp
  (implies (not (intervalp interval))
           (inp r interval))
  :enable inp)

(defrule inp-when-not-intervalp-cheap
  (implies (not (intervalp interval))
           (inp r interval))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by inp-when-not-intervalp)

(defruled inp-when-emptyp
  (implies (emptyp interval)
           (not (inp r interval)))
  :enable inp)

(defrule inp-when-emptyp-cheap
  (implies (emptyp interval)
           (not (inp r interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by inp-when-emptyp)

(defrule inp-of-nil
  (not (inp r nil)))

(defrule inp-of-empty
  (not (inp r (empty))))

(defrule inp-of-full
  (inp r (interval nil nil))
  :enable inp)

(defrule inp-of-exact
  (equal (inp r (exact val))
         (equal (rfix r) (rfix val)))
  :enable inp)

(defruled inp-of-min
  (equal (inp (min interval) interval)
         (or (bounded-below-p interval)
             ;; If (not (bounded-below-p interval)), then (min interval) = nil.
             ;; inp then fixes nil to 0.
             (inp 0 interval)))
  :enable (inp
           min
           bounded-below-p
           fix
           intervalp
           interval)
  :disable min-under-iff)

(defrule inp-of-min-when-bounded-below-p
  (implies (bounded-below-p interval)
           (inp (min interval) interval))
  :enable inp-of-min)

(defruled inp-of-max
  (equal (inp (max interval) interval)
         (or (bounded-above-p interval)
             ;; See comment in inp-of-min
             (inp 0 interval)))
  :enable (inp
           max
           bounded-above-p
           fix
           intervalp
           interval)
  :disable max-under-iff)

(defrule inp-of-max-when-bounded-above-p
  (implies (bounded-above-p interval)
           (inp (max interval) interval))
  :enable inp-of-max)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define arbitrary
  ((interval intervalp))
  :guard (not (emptyp interval))
  :returns (arbitrary-elem rationalp)
  :parents (intervals)
  :short "Get an arbitrary element included in the interval."
  :long
  (xdoc::topstring
   (xdoc::p
     "This element is guaranteed to be included in the interval unless it is
      empty."))
  (cond ((bounded-below-p interval) (min interval))
        ((bounded-above-p interval) (max interval))
        (t 0)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t arbitrary)))

(defrule arbitrary-type-prescription
  (rationalp (arbitrary interval))
  :rule-classes :type-prescription)

(defrule arbitrary-when-equiv-congruence
  (implies (equiv interval0 interval1)
           (equal (arbitrary interval0)
                  (arbitrary interval1)))
  :rule-classes :congruence
  :enable arbitrary)

(defruled arbitrary-when-exactp
  (implies (exactp interval)
           (equal (arbitrary interval)
                  (min interval)))
  :enable arbitrary)

(defrule arbitrary-when-exactp-cheap
  (implies (exactp interval)
           (equal (arbitrary interval)
                  (min interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by arbitrary-when-exactp)

(defrule inp-of-arbitrary
  (equal (inp (arbitrary interval) interval)
         (not (equal interval (empty))))
  :enable (arbitrary
           inp))
