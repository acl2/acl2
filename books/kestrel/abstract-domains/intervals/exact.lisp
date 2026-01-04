; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "INTERVAL")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "noninterval-arith-support"))
(include-book "core")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exactp ((interval intervalp))
  :guard (not (emptyp interval))
  :returns (yes/no booleanp)
  :parents (intervals)
  :short "Recognize exact intervals."
  :long
  (xdoc::topstring
   (xdoc::p
     "By ``exact,'' we mean intervals which include exactly one element, such
      as those constructed via @(tsee exact)."))
  (mbe :logic (and (bounded-below-p interval)
                   (bounded-above-p interval)
                   (equal (min interval)
                          (max interval)))
       :exec (let ((min (min interval))
                   (max (max interval)))
               (and (the (or rational null) min)
                    (the (or rational null) max)
                    (= (the rational min)
                       (the rational max))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t exactp)))

(defrule exactp-type-prescription
  (booleanp (exactp interval))
  :rule-classes ((:type-prescription :typed-term (exactp interval))))

(defrule exactp-compound-recognizer
  (implies (exactp interval)
           (consp interval))
  :rule-classes :compound-recognizer
  :enable (exactp
           min
           interval))

(defrule exactp-when-equiv-congruence
  (implies (equiv interval0 interval1)
           (equal (exactp interval0)
                  (exactp interval1)))
  :rule-classes :congruence
  :enable exactp)

(defruled bounded-below-p-when-exactp
  (implies (exactp interval)
           (bounded-below-p interval))
  :enable exactp)

(defrule bounded-below-p-when-exactp-forward-chaining
  (implies (exactp interval)
           (bounded-below-p interval))
  :rule-classes :forward-chaining
  :by bounded-below-p-when-exactp)

(defruled bounded-above-p-when-exactp
  (implies (exactp interval)
           (bounded-above-p interval))
  :enable exactp)

(defrule bounded-above-p-when-exactp-forward-chaining
  (implies (exactp interval)
           (bounded-above-p interval))
  :rule-classes :forward-chaining
  :by bounded-above-p-when-exactp)

(defruled boundedp-when-exactp
  (implies (exactp interval)
           (boundedp interval))
  :enable exactp)

(defrule boundedp-when-exactp-forward-chaining
  (implies (exactp interval)
           (boundedp interval))
  :rule-classes :forward-chaining
  :by boundedp-when-exactp)

;; We normalize toward min
(defruled max-when-exactp
  (implies (exactp interval)
           (equal (max interval)
                  (min interval)))
  :enable exactp)

(defrule max-when-exactp-forward-chaining
  (implies (exactp interval)
           (equal (max interval)
                  (min interval)))
  :rule-classes :forward-chaining
  :by max-when-exactp)

(defrule max-when-exactp-cheap
  (implies (exactp interval)
           (equal (max interval)
                  (min interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by max-when-exactp)

(defruled exactp-when-not-bounded-below-p
  (implies (not (bounded-below-p interval))
           (not (exactp interval))))

(defrule exactp-when-not-bounded-below-p-cheap
  (implies (not (bounded-below-p interval))
           (not (exactp interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by exactp-when-not-bounded-below-p)

(defruled exactp-when-not-bounded-above-p
  (implies (not (bounded-above-p interval))
           (not (exactp interval))))

(defrule exactp-when-not-bounded-above-p-cheap
  (implies (not (bounded-above-p interval))
           (not (exactp interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by exactp-when-not-bounded-above-p)

(defruled exactp-when-not-equal-min-max
  (implies (not (equal (min interval) (max interval)))
           (not (exactp interval))))

(defrule exactp-when-not-equal-min-max-cheap
  (implies (not (equal (min interval) (max interval)))
           (not (exactp interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by exactp-when-not-equal-min-max)

(defruled intervalp-when-exactp
  (implies (exactp interval)
           (intervalp interval))
  :enable (exactp
           min
           max
           bounded-below-p
           bounded-above-p
           interval)
  :disable (min-under-iff
            max-under-iff))

(defrule intervalp-when-exactp-forward-chaining
  (implies (exactp interval)
           (intervalp interval))
  :rule-classes :forward-chaining
  :by intervalp-when-exactp)

(defruled exactp-when-not-intervalp
  (implies (not (intervalp interval))
           (not (exactp interval))))

(defrule exactp-when-not-intervalp-forward-chaining
  (implies (not (intervalp interval))
           (not (exactp interval)))
  :rule-classes :forward-chaining
  :by exactp-when-not-intervalp)

(defruled exactp-when-emptyp
  (implies (emptyp interval)
           (not (exactp interval)))
  :enable exactp)

(defrule exactp-when-emptyp-cheap
  (implies (emptyp interval)
           (not (exactp interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by exactp-when-emptyp)

(defrule exactp-of-empty
  (not (exactp (empty))))

(defrule exactp-of-interval
  (equal (exactp (interval min max))
         (and min
              max
              (equal (rfix min) (rfix max))))
  :enable (exactp
           interval
           min
           max
           bounded-below-p
           bounded-above-p
           intervalp)
  :disable (min-under-iff
            max-under-iff))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exact ((val rationalp))
  :returns (interval intervalp)
  :parents (intervals)
  :short "Construct an exact interval."
  :long
  (xdoc::topstring
   (xdoc::p
     "The resulting interval contains exactly one element &mdash; the argument
      to the constructor."))
  (interval (rational-fix val) (rational-fix val))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e exact) (:t exact)))

(defrule exact-type-prescription
  (consp (exact val))
  :rule-classes :type-prescription
  :enable (exact
           interval))

(defrule exact-under-iff
  (iff (exact val)
       t))

(defrule exactp-of-exact
  (exactp (exact val))
  :enable exact)

(defrule bounded-below-p-of-exact
  (bounded-below-p (exact val))
  :enable bounded-below-p-when-exactp)

(defrule bounded-above-p-of-exact
  (bounded-above-p (exact val))
  :enable bounded-above-p-when-exactp)

(defrule max-of-exact
  (equal (max (exact val))
         (min (exact val)))
  :enable max-when-exactp)

(defrule min-of-exact
  (equal (min (exact val))
         (rfix val))
  :enable (exact
           min-of-interval))

;; TODO: disable by default?
;; If so, add a rule for exact of min of exact.
(defrule exact-of-min-when-exactp
  (implies (exactp interval)
           (equal (exact (min interval))
                  interval))
  :enable (exact
           exactp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get (interval)
  :guard (mbe :logic (exactp interval)
              :exec (and (intervalp interval)
                         (not (emptyp interval))
                         (exactp interval)))
  :returns (val rationalp)
  :parents (exact)
  :short "Get the value of an @(see exact) interval."
  :long
  (xdoc::topstring
   (xdoc::p
     "The @(see min) and @(see max) values of an @(see exact) interval are
      equal. Logically, we normalize toward @(tsee min). In code, however, it
      may be clearer to call @(tsee get). This is a synonym for @(tsee min)
      when the argument is @(see exact) (&mdash; otherwise, it returns
      @('0'))."))
  (mbe :logic (if (exactp interval)
                  (min interval)
                0)
       :exec (min interval))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t get)))

(defrule get-type-prescription
  (rationalp (get interval))
  :rule-classes :type-prescription)

(defrule get-when-equiv-congruence
  (implies (equiv interval0 interval1)
           (equal (get interval0)
                  (get interval1)))
  :rule-classes :congruence
  :enable get)

(defruled get-when-emptyp
  (implies (emptyp interval)
           (equal (get interval)
                  0)))

(defrule get-when-emptyp-cheap
  (implies (emptyp interval)
           (equal (get interval)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by get-when-emptyp)

(defrule get-of-empty
  (equal (get (empty))
         0))

(defruled get-when-not-intervalp
  (implies (not (intervalp interval))
           (equal (get interval)
                  0))
  :enable get)

(defruled get-when-not-intervalp-cheap
  (implies (not (intervalp interval))
           (equal (get interval)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by get-when-not-intervalp)

(defruled get-when-not-exactp
  (implies (not (exactp interval))
           (equal (get interval)
                  0))
  :enable get)

(defrule get-when-not-exactp-cheap
  (implies (not (exactp interval))
           (equal (get interval)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by get-when-not-exactp)

(defrule get-when-exactp
  (implies (exactp interval)
           (equal (get interval)
                  (min interval)))
  :enable get)
