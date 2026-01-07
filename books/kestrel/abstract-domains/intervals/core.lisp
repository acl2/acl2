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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intervalp (x)
  :returns (yes/no booleanp)
  :parents (intervals)
  :short "Recognizer for @(see intervals)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Concretely, an interval is represented as either @('nil'), representing
      the empty interval, or a @('cons') pair of @(tsee maybe-rationalp) values
      representing the @(see min) and @(see max)."))
  (if (consp x)
      (mbe :logic (and (maybe-rationalp (car x))
                       (maybe-rationalp (cdr x))
                       (implies (and (rationalp (car x))
                                     (rationalp (cdr x)))
                                (<= (car x)
                                    (cdr x))))
           :exec (if (rationalp (car x))
                     (if (rationalp (cdr x))
                         (<= (car x) (cdr x))
                       (null (cdr x)))
                   (and (null (car x))
                        (or (rationalp (cdr x))
                            (null (cdr x))))))
    (null x)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t intervalp)))

(defrule intervalp-type-prescription
  (booleanp (intervalp x))
  :rule-classes ((:type-prescription :typed-term (intervalp x))))

(defrule intervalp-compound-recognizer
  (if (intervalp x)
      (or (consp x)
          (equal x nil))
    (not (equal x nil)))
  :rule-classes :compound-recognizer
  :enable intervalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define empty ()
  :returns (empty intervalp)
  :parents (intervals)
  :short "The empty interval."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is the bottom/minimum element of the bounded lattice, written
      @($\\emptyset$). It is the identity element for @(tsee hull) and the
      absorption element for @(tsee intersect)."))
  nil
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e empty) (:t empty)))

(defrule empty-type-prescription
  (equal (empty) nil)
  :rule-classes :type-prescription
  :enable empty)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define full ()
  :returns (full intervalp)
  :parents (intervals)
  :short "The full interval."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is the interval which contains all rational numbers, written
      @($(-\\infty, \\infty)$). It has no minimum or maximum bound.")
   (xdoc::p
     "This is the top/maximum element of the bounded lattice. It is the
      identity element for @(tsee intersect) and the absorption element for
      @(tsee hull).")
   (xdoc::p
     "We tend to avoid @('(full)'), using @('(interval nil nil)') instead.
      Indeed, we rewrite the former into the latter by default. We might avoid
      this definition of @(tsee full) altogether, except for a
      ``chicken and egg'' problem &mdash; the definition of @(tsee interval)
      depends on @(tsee fix), which depends on @(tsee full)."))
  (cons nil nil)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e full) (:t full)))

(defrule full-type-prescription
  (consp (full))
  :rule-classes :type-prescription
  :enable full)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fix ((interval intervalp))
  :returns (interval$ intervalp)
  :parents (intervals)
  :short "A fixing function for @(see intervals)."
  :long
  (xdoc::topstring
   (xdoc::p
     "If the argument is not an interval, we default to @('(full)'). This is
      more natural than @('(empty)'), since @('(full)') represents a lack of
      information (``the number can be anything'')."))
  (mbe :logic (if (intervalp interval)
                  interval
                (full))
       :exec interval)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t fix)))

(defrule fix-type-prescription
  (intervalp (fix interval))
  :rule-classes ((:type-prescription :typed-term (fix interval))))

(defrule fix-when-intervalp
  (implies (intervalp interval)
           (equal (fix interval)
                  interval))
  :enable fix)

(defruled fix-when-not-intervalp
  (implies (not (intervalp interval))
           (equal (fix interval)
                  (full)))
  :enable fix)

(defrule fix-when-not-intervalp-cheap
  (implies (not (intervalp interval))
           (equal (fix interval)
                  (full)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by fix-when-not-intervalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define equiv
  ((x intervalp)
   (y intervalp))
  :returns (yes/no booleanp)
  :parents (intervals)
  :short "Equivalence of intervals."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is a typical equality of fixers. Note that the representation of
      intervals is unique, so it is also the desired extensional equality."))
  (equal (fix x)
         (fix y))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t equiv)))

(defrule equiv-type-prescription
  (booleanp (equiv x y))
  :rule-classes ((:type-prescription :typed-term (equiv x y))))

(defequiv equiv
  :hints (("Goal" :in-theory (enable equiv))))

(defrule fix-under-equiv
  (equiv (fix interval)
         interval)
  :enable equiv)

(defrule fix-when-equiv-congruence
  (implies (equiv interval0 interval1)
           (equal (fix interval0)
                  (fix interval1)))
  :rule-classes :congruence
  :enable equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emptyp ((interval intervalp))
  :returns (yes/no booleanp)
  :parents (intervals)
  :short "Test an interval for emptiness."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function is intended for execution, not as a logical form. By
      default, we enable it and prefer to simply compare intervals directly to
      the unique @(see empty) interval."))
  (mbe :logic (equal interval (empty))
       :exec (endp interval))
  :inline t
  :enabled t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t emptyp)))

(defrule emptyp-type-prescription
  (booleanp (emptyp interval))
  :rule-classes ((:type-prescription :typed-term (emptyp interval))))

(defrule emptyp-compound-recognizer
  (implies (not (emptyp interval))
           (not (equal interval nil)))
  :rule-classes :compound-recognizer)

(defrule emptyp-when-equiv-congruence
  (implies (equiv interval0 interval1)
           (equal (emptyp interval0)
                  (emptyp interval1)))
  :rule-classes :congruence
  :enable (equiv
           fix))

(defrule emptyp-of-nil
  (emptyp nil))

(defrule emptyp-of-empty
  (emptyp (empty)))

(defruled intervalp-when-emptyp
  (implies (emptyp x)
           (intervalp x)))

(defrule intervalp-when-emptyp-forward-chaining
  (implies (emptyp x)
           (intervalp x))
  :rule-classes :forward-chaining
  :by intervalp-when-emptyp)

(defruled emptyp-when-not-intervalp
  (implies (not (intervalp x))
           (not (emptyp x))))

(defrule emptyp-when-not-intervalp-forward-chaining
  (implies (not (intervalp x))
           (not (emptyp x)))
  :rule-classes :forward-chaining
  :by emptyp-when-not-intervalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min ((interval intervalp))
  :guard (not (emptyp interval))
  :returns (min? maybe-rationalp
                 :hints (("Goal" :in-theory (enable fix
                                                    intervalp
                                                    full))))
  :parents (intervals)
  :short "Get the lower bound of an interval."
  :long
  (xdoc::topstring
   (xdoc::p
     "The lower bound is inclusive; the minimum element, if it exists, is
      therefore included in the interval.")
   (xdoc::p
     "The minimum exists if and only if the interval is
      @(tsee bounded-below-p). If the interval is not bounded below,
      @(tsee min) returns @('nil'), indicating ``no lower bound''. If the
      interval is empty (contrary to the guard), it is not sensible to talk
      about the lower bound. Logically, we arbitrarily choose to return
      @('nil')."))
  (mbe :logic (if (equal interval (empty))
                  nil
                (car (fix interval)))
       :exec (car (the cons interval)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t min)))

(defrule min-type-prescription
  (or (rationalp (min interval))
      (equal (min interval) nil))
  :rule-classes :type-prescription
  :use maybe-rationalp-of-min)

(defrule min-when-equiv-congruence
  (implies (equiv interval0 interval1)
           (equal (min interval0)
                  (min interval1)))
  :rule-classes :congruence
  :enable min)

(defruled min-when-emptyp
  (implies (emptyp interval)
           (equal (min interval)
                  nil)))

(defrule min-when-emptyp-cheap
  (implies (emptyp interval)
           (equal (min interval)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by min-when-emptyp)

(defrule min-of-empty
  (equal (min (empty))
         nil))

(defruled min-when-not-intervalp
  (implies (not (intervalp interval))
           (equal (min interval)
                  nil))
  :enable (min
           full))

(defrule min-when-not-intervalp-cheap
  (implies (not (intervalp interval))
           (equal (min interval)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by min-when-not-intervalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max ((interval intervalp))
  :guard (not (emptyp interval))
  :returns (max? maybe-rationalp
                 :hints (("Goal" :in-theory (enable fix
                                                    intervalp
                                                    full))))
  :parents (intervals)
  :short "Get the upper bound of an interval."
  :long
  (xdoc::topstring
   (xdoc::p
     "The upper bound is inclusive; the maximum element, if it exists, is
      therefore included in the interval.")
   (xdoc::p
     "The maximum exists if and only if the interval is
      @(tsee bounded-above-p). If the interval is not bounded above,
      @(tsee max) returns @('nil'), indicating ``no upper bound''. If the
      interval is empty (contrary to the guard), it is not sensible to talk
      about the upper bound. Logically, we arbitrarily choose to return
      @('nil')."))
  (mbe :logic (if (equal interval (empty))
                  nil
                (cdr (fix interval)))
       :exec (cdr (the cons interval)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t max)))

(defrule max-type-prescription
  (or (rationalp (max interval))
      (equal (max interval) nil))
  :rule-classes :type-prescription
  :use maybe-rationalp-of-max)

(defrule max-when-equiv-congruence
  (implies (equiv interval0 interval1)
           (equal (max interval0)
                  (max interval1)))
  :rule-classes :congruence
  :enable max)

(defruled max-when-emptyp
  (implies (emptyp interval)
           (equal (max interval)
                  nil))
  :enable min)

(defrule max-when-emptyp-cheap
  (implies (emptyp interval)
           (equal (max interval)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by max-when-emptyp)

(defrule max-of-empty
  (equal (max (empty))
         nil)
  :enable max)

(defruled max-when-not-intervalp
  (implies (not (intervalp interval))
           (equal (max interval)
                  nil))
  :enable (max
           full))

(defrule max-when-not-intervalp-cheap
  (implies (not (intervalp interval))
           (equal (max interval)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by max-when-not-intervalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bounded-below-p ((interval intervalp))
  :guard (not (emptyp interval))
  :returns (yes/no booleanp)
  :parents (intervals)
  :short "Check if the interval is bounded below."
  :long
  (xdoc::topstring
   (xdoc::p
     "That is, check if the interval has a lower bound. The @(tsee min)
      function will return a rational if the interval is
      @(tsee bounded-below-p), and @('nil') otherwise."))
  (mbe :logic (and (min interval) t)
       :exec (and (the (or rational null) (car (the cons interval))) t))
  :inline t
  :guard-hints (("Goal" :in-theory (enable min
                                           intervalp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t bounded-below-p)))

(defrule bounded-below-p-type-prescription
  (booleanp (bounded-below-p interval))
  :rule-classes ((:type-prescription :typed-term (bounded-below-p interval))))

(defrule bounded-below-p-when-equiv-congruence
  (implies (equiv interval0 interval1)
           (equal (bounded-below-p interval0)
                  (bounded-below-p interval1)))
  :rule-classes :congruence
  :enable bounded-below-p)

(defruled bounded-below-p-when-emptyp
  (implies (emptyp interval)
           (not (bounded-below-p interval))))

(defrule bounded-below-p-when-emptyp-cheap
  (implies (emptyp interval)
           (not (bounded-below-p interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bounded-below-p-when-emptyp)

(defrule bounded-below-p-of-empty
  (not (bounded-below-p (empty))))

(defruled bounded-below-p-when-not-intervalp
  (implies (not (intervalp interval))
           (not (bounded-below-p interval)))
  :enable bounded-below-p)

(defrule bounded-below-p-when-not-intervalp-cheap
  (implies (not (intervalp interval))
           (not (bounded-below-p interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bounded-below-p-when-not-intervalp)

(defrule min-under-iff
  (iff (min interval)
       (bounded-below-p interval))
  :enable bounded-below-p)

(theory-invariant (incompatible! (:rewrite min-under-iff)
                                 (:definition bounded-below-p$inline)))

(defrule rationalp-of-min
  (equal (rationalp (min interval))
         (bounded-below-p interval))
  :enable bounded-below-p
  :disable min-under-iff)

(defrule rationalp-of-min-when-bounded-below-p-type-prescription
  (implies (bounded-below-p interval)
           (rationalp (min interval)))
  :rule-classes :type-prescription)

(defruled min-when-not-bounded-below-p
  (implies (not (bounded-below-p interval))
           (equal (min interval)
                  nil)))

(defrule min-when-not-bounded-below-p-cheap
  (implies (not (bounded-below-p interval))
           (equal (min interval)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by min-when-not-bounded-below-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bounded-above-p ((interval intervalp))
  :guard (not (emptyp interval))
  :returns (yes/no booleanp)
  :parents (intervals)
  :short "Check if the interval is bounded above."
  :long
  (xdoc::topstring
   (xdoc::p
     "That is, check if the interval has a upper bound. The @(tsee max)
      function will return a rational if the interval is
      @(tsee bounded-above-p), and @('nil') otherwise."))
  (mbe :logic (and (max interval) t)
       :exec (and (the (or rational null) (cdr (the cons interval))) t))
  :inline t
  :guard-hints (("Goal" :in-theory (enable max
                                           intervalp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t bounded-above-p)))

(defrule bounded-above-p-type-prescription
  (booleanp (bounded-above-p interval))
  :rule-classes ((:type-prescription :typed-term (bounded-above-p interval))))

(defrule bounded-above-p-when-equiv-congruence
  (implies (equiv interval0 interval1)
           (equal (bounded-above-p interval0)
                  (bounded-above-p interval1)))
  :rule-classes :congruence
  :enable bounded-above-p)

(defruled bounded-above-p-when-emptyp
  (implies (emptyp interval)
           (not (bounded-above-p interval))))

(defrule bounded-above-p-when-emptyp-cheap
  (implies (emptyp interval)
           (not (bounded-above-p interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bounded-above-p-when-emptyp)

(defrule bounded-above-p-of-empty
  (not (bounded-above-p (empty))))

(defruled bounded-above-p-when-not-intervalp
  (implies (not (intervalp interval))
           (not (bounded-above-p interval)))
  :enable bounded-above-p)

(defrule bounded-above-p-when-not-intervalp-cheap
  (implies (not (intervalp interval))
           (not (bounded-above-p interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bounded-above-p-when-not-intervalp)

(defrule max-under-iff
  (iff (max interval)
       (bounded-above-p interval))
  :enable bounded-above-p)

(theory-invariant (incompatible! (:rewrite max-under-iff)
                                 (:definition bounded-above-p$inline)))

(defrule rationalp-of-max
  (equal (rationalp (max interval))
         (bounded-above-p interval))
  :enable bounded-above-p
  :disable max-under-iff)

(defrule rationalp-of-max-when-bounded-above-p-type-prescription
  (implies (bounded-above-p interval)
           (rationalp (max interval)))
  :rule-classes :type-prescription)

(defruled max-when-not-bounded-above-p
  (implies (not (bounded-above-p interval))
           (equal (max interval)
                  nil)))

(defrule max-when-not-bounded-above-p-cheap
  (implies (not (bounded-above-p interval))
           (equal (max interval)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by max-when-not-bounded-above-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule <=-of-min-and-max
  (implies (and (bounded-below-p interval)
                (bounded-above-p interval))
           (<= (min interval) (max interval)))
  :enable (min
           max
           bounded-below-p
           bounded-above-p
           intervalp
           fix
           full)
  :disable (min-under-iff
            max-under-iff))

(defrule <=-of-min-and-max-linear
  (implies (and (bounded-below-p interval)
                (bounded-above-p interval))
           (<= (min interval) (max interval)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boundedp ((interval intervalp))
  :guard (not (emptyp interval))
  :returns (yes/no booleanp)
  :parents (intervals)
  :short "Check if the interval is bounded from both below and above."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is simply the conjunction of @(tsee bounded-below-p) and
      @(tsee bounded-above-p). Since most of the core interval operations are
      closed on bounded intervals (@(tsee intersect) is the exception),
      we introduce this additional predicate to recognize such intervals."))
  (mbe :logic (and (bounded-below-p interval)
                   (bounded-above-p interval))
       :exec (and (the (or rational null) (car (the cons interval)))
                  (the (or rational null) (cdr (the cons interval)))
                  t))
  :inline t
  :guard-hints (("Goal" :in-theory (e/d (bounded-below-p
                                         bounded-above-p
                                         intervalp
                                         min
                                         max)
                                        (min-under-iff
                                         max-under-iff)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t boundedp)))

(defrule boundedp-type-prescription
  (booleanp (boundedp interval))
  :rule-classes ((:type-prescription :typed-term (boundedp interval))))

(defrule boundedp-when-equiv-congruence
  (implies (equiv interval0 interval1)
           (equal (boundedp interval0)
                  (boundedp interval1)))
  :rule-classes :congruence
  :enable boundedp)

(defruled boundedp-when-bounded-below-p-and-bounded-above-p
  (implies (and (bounded-below-p interval)
                (bounded-above-p interval))
           (boundedp interval))
  :enable boundedp)

(defrule boundedp-when-bounded-below-p-and-bounded-above-p-cheap
  (implies (and (bounded-below-p interval)
                (bounded-above-p interval))
           (boundedp interval))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :by boundedp-when-bounded-below-p-and-bounded-above-p)

(defruled bounded-below-p-when-boundedp
  (implies (boundedp interval)
           (bounded-below-p interval))
  :enable boundedp)

(defrule bounded-below-p-when-boundedp-forward-chaining
  (implies (boundedp interval)
           (bounded-below-p interval))
  :rule-classes :forward-chaining
  :by bounded-below-p-when-boundedp)

(defruled bounded-above-p-when-boundedp
  (implies (boundedp interval)
           (bounded-above-p interval))
  :enable boundedp)

(defrule bounded-above-p-when-boundedp-forward-chaining
  (implies (boundedp interval)
           (bounded-above-p interval))
  :rule-classes :forward-chaining
  :by bounded-above-p-when-boundedp)

(defruled boundedp-when-emptyp
  (implies (emptyp interval)
           (not (boundedp interval))))

(defrule boundedp-when-emptyp-cheap
  (implies (emptyp interval)
           (not (boundedp interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by boundedp-when-emptyp)

(defrule boundedp-of-empty
  (not (boundedp (empty))))

(defruled boundedp-when-not-intervalp
  (implies (not (intervalp interval))
           (not (boundedp interval)))
  :enable boundedp)

(defrule boundedp-when-not-intervalp-cheap
  (implies (not (intervalp interval))
           (not (boundedp interval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by boundedp-when-not-intervalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define interval (min max)
  :guard (mbe :logic (and (maybe-rationalp min)
                          (maybe-rationalp max)
                          (implies (and (rationalp min)
                                        (rationalp max))
                                   (<= min max)))
              :exec (if (rationalp min)
                        (if (rationalp max)
                            (<= min max)
                          (null max))
                      (and (null min)
                           (or (rationalp max)
                               (null max)))))
  :returns (interval intervalp
                     :hints (("Goal" :in-theory (enable intervalp))))
  :parents (intervals)
  :short "Construct a nonempty interval."
  :long
  (xdoc::topstring
   (xdoc::p
     "The @('min') and @('max') arguments correspond to the @(tsee min) and
      @(tsee max) accessors. A value of @('nil') represents ``no bound.''")
   (xdoc::p
     "The @('min') and @('max') arguments may be equal. This represents an
      @(see exact) interval. That is, an interval which includes exactly one
      rational number. The @('min') may not be greater than @('max'). If it is,
      we logically return the @(see empty) interval."))
  (mbe :logic (let ((min (maybe-rational-fix min))
                    (max (maybe-rational-fix max)))
                (if (and (rationalp min)
                         (rationalp max)
                         (< max min))
                    (empty)
                  (cons min max)))
       :exec(cons min max))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e interval) (:t interval)))

(defrule interval-type-prescription
  (intervalp (interval min max))
  :rule-classes ((:type-prescription :typed-term (interval min max))))

;;;;;;;;;;;;;;;;;;;;

(defruled min-of-interval
  (equal (min (interval min max))
         (if (and max
                  (< (rfix max) (maybe-rational-fix min)))
             nil
           (maybe-rational-fix min)))
  :enable (min
           interval
           intervalp))

(defruled bounded-below-p-of-interval
  (equal (bounded-below-p (interval min max))
         (and min
              (implies max
                       (<= (maybe-rational-fix min)
                           (rfix max)))))
  :enable (bounded-below-p
           min-of-interval)
  :disable min-under-iff)

(defrule min-of-interval-when-rationalp-and-<=
  (implies (and (rationalp min)
                (rationalp max)
                (<= min max))
           (equal (min (interval min max))
                  min))
  :enable min-of-interval)

(defrule bounded-below-p-of-interval-when-rationalp-and-<=
  (implies (and (rationalp min)
                (rationalp max)
                (<= min max))
           (bounded-below-p (interval min max)))
  :enable bounded-below-p-of-interval)

(defrule bounded-below-p-of-interval-nil
  (not (bounded-below-p (interval nil max)))
  :enable bounded-below-p-of-interval)

(defrule min-of-interval-nil
  (equal (min (interval nil max))
         nil))

(defruled max-of-interval
  (equal (max (interval min max))
         (if (and min
                  (< (maybe-rational-fix max) (rfix min)))
             nil
           (maybe-rational-fix max)))
  :enable (max
           interval
           intervalp))

(defruled bounded-above-p-of-interval
  (equal (bounded-above-p (interval min max))
         (and max
              (implies min
                       (<= (rfix min)
                           (maybe-rational-fix max)))))
  :enable (bounded-above-p
           max-of-interval)
  :disable max-under-iff)

(defrule max-of-interval-when-rationalp-and-<=
  (implies (and (rationalp min)
                (rationalp max)
                (<= min max))
           (equal (max (interval min max))
                  max))
  :enable max-of-interval)

(defrule bounded-above-p-of-interval-when-rationalp-and-<=
  (implies (and (rationalp min)
                (rationalp max)
                (<= min max))
           (bounded-above-p (interval min max)))
  :enable bounded-above-p-of-interval)

(defrule bounded-above-p-of-interval-arg1-nil
  (not (bounded-above-p (interval min nil)))
  :enable bounded-above-p-of-interval)

(defrule max-of-interval-arg1-nil
  (equal (max (interval min nil))
         nil))

(defruled boundedp-of-interval
  (equal (boundedp (interval min max))
         (and min
              max
              (<= (rfix min)
                  (rfix max))))
  :enable (boundedp
           bounded-below-p-of-interval
           bounded-above-p-of-interval))

(defrule boundedp-of-interval-when-rationalp-and-<=
  (implies (and (rationalp min)
                (rationalp max)
                (<= min max))
           (boundedp (interval min max)))
  :enable boundedp-of-interval)

;;;;;;;;;;;;;;;;;;;;

(defrule interval-elim
  (implies (and (intervalp interval)
                (not (emptyp interval)))
           (equal (interval (min interval) (max interval))
                  interval))
  :rule-classes :elim
  :enable (interval
           min
           max
           intervalp))

(defruled equal-when-nonempty
  (implies (and (intervalp x)
                (intervalp y)
                (not (equal x (empty)))
                (not (equal y (empty))))
           (equal (equal x y)
                  (and (equal (min x) (min y))
                       (equal (max x) (max y))))))

(defrule equal-when-nonempty-cheap
  (implies (and (intervalp x)
                (intervalp y)
                (not (equal x (empty)))
                (not (equal y (empty))))
           (equal (equal x y)
                  (and (equal (min x) (min y))
                       (equal (max x) (max y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 0 0)))
  :use equal-when-nonempty)

;; TODO: double-rewrite
(defruled equal-of-intervals-unlimited
  (implies (and (intervalp x)
                (intervalp y))
           (equal (equal x y)
                  (if (equal x (empty))
                      (equal y (empty))
                    (and (not (equal y (empty)))
                         (equal (min x) (min y))
                         (equal (max x) (max y)))))))

;; (defruled equal-of-intervals
;;   (implies (and (intervalp x)
;;                 (intervalp y))
;;            (equal (equal x y)
;;                   (if (equal x (empty))
;;                       (equal y (empty))
;;                     (and (not (equal y (empty)))
;;                          (equal (min x) (min y))
;;                          (equal (max x) (max y))))))
;;   :rule-classes ((:rewrite :backchain-limit-lst (1 1)))
;;   :by equal-of-intervals-no-backchain-limit)

(defruled equal-of-intervals
  (implies (and (syntaxp (and (not (equal x ''nil))
                              (not (equal x '(empty$inline)))
                              (not (equal y ''nil))
                              (not (equal y '(empty$inline)))))
                (intervalp x)
                (intervalp y))
           (equal (equal x y)
                  (if (equal x (empty))
                      (equal y (empty))
                    (and (not (equal y (empty)))
                         (equal (min x) (min y))
                         (equal (max x) (max y))))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 1 1)))
  :by equal-of-intervals-unlimited)

(defrule equal-of-interval-and-empty
  (equal (equal (interval min max) (empty))
         (and min
              max
              (< (rfix max)
                 (rfix min))))
  :enable interval)

(defrule emptyp-of-interval
  (equal (emptyp (interval min max))
         (and min
              max
              (< (rfix max)
                 (rfix min))))
  :use equal-of-interval-and-empty
  :disable equal-of-interval-and-empty)

(defrule interval-under-iff
  (iff (interval min max)
       (or (not min)
           (not max)
           (<= (rfix min)
               (rfix max))))
  :enable interval)

(defrule full-becomes-interval
  (equal (full)
         (interval nil nil))
  :rule-classes :definition
  :enable (full
           interval))

(defrule equal-of-fix-and-full
  (equal (equal (fix interval) (interval nil nil))
         (and (not (equal interval (empty)))
              (equal (min interval) nil)
              (equal (max interval) nil)))
  :enable (fix
           interval
           min
           max))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define interval$
  ((min maybe-rationalp)
   (max maybe-rationalp))
  :returns (interval intervalp)
  :parents (intervals)
  :short "Variant of @(tsee interval) with a weaker guard."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically, this is equivalent to @(tsee interval). It differs by checking
      the condition that @('min') is less than or equal to @('max') explicitly
      in the function body instead of requiring it in the guard."))
  (mbe :logic (interval min max)
       :exec (if (and min max (< max min))
                 (empty)
               (interval min max)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable interval))))
