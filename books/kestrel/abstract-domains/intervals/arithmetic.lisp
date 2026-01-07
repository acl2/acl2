; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "INTERVAL")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "noninterval-arith-support"))
(local (include-book "min-max-support"))
(include-book "core")
(include-book "exact")
(include-book "subintervalp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc arithmetic
  :parents (intervals)
  :short "Arithmetic on @(see intervals)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Given an @($n$)-ary function @('f') on rationals, and a corresponding
       @($n$)-ary function @('ivl-f') on intervals, we say that @('ivl-f') is
       an ``interval extension'' of @('f') iff, for all rationals
       @('x0'), @('x1'), ... @('xn') and intervals @('i0'), @('i1'), ...
       @('in'):")
    (xdoc::codeblock
      "(implies (and (inp x0 i0)"
      "              (inp x1 i1)"
      "              ..."
      "              (inp xn in))"
      "         (inp (f x0 x1 ... xn)"
      "              (ivl-f i0 i1 ... in)))")
    (xdoc::p
      ". The arithmetic operations defined here are the tightest possible
       interval extensions of the corresponding rational operation.")
    (xdoc::p
      "We define an interval extension to be ``precise'' when all rationals
       included in the output interval can actually be achieved by the regular
       function for some set of inputs from the input intervals.  More
       formally, for arbitrary intervals @('i0'), @('i1'), ... @('in'):")
    (xdoc::codeblock
      "(implies (inp r (inv-f i0 i1 ... in))"
      "         (exists (x0 x1 ... xn)"
      "                 (and (inp x0 i0)"
      "                      (inp x1 i1)"
      "                      ..."
      "                      (inp xn in)"
      "                      (equal r (f x0 x1 ... xn)))))")
    (xdoc::p
      "Note that the tightest interval extension will be precise if it extends
       a continue function, but not necessarily if it extends a discontinuous
       function. This is because an interval cannot represent any ``gaps''.
       Consider the tightest extension of the @(tsee floor) function.
       The output of @(tsee floor) is always an integer, but any nonempty,
       non-@(see exact) interval produced by the interval extension will
       necessarily include non-integers.")
    (xdoc::p
      "Currently, the only defined interval extension is @(tsee +). We plan to
       add further extensions.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection +
  :parents (arithmetic)
  :short "Interval addition."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is the precise interval extension of @(tsee acl2::+)."))

  (define binary-+
    ((x intervalp)
     (y intervalp))
    :returns (sum intervalp)
    (if (or (emptyp x)
            (emptyp y))
        (empty)
      (interval (let ((min-x (min x))
                      (min-y (min y)))
                  (if (and min-x min-y)
                      (acl2::+ min-x min-y)
                    nil))
                (let ((max-x (max x))
                      (max-y (max y)))
                  (if (and max-x max-y)
                      (acl2::+ max-x max-y)
                    nil))))
    ///

    (defmacro + (&rest rest)
      (if (endp rest)
          (exact 0)
        (if (rest rest)
            (xxxjoin 'binary-+ rest)
          (cons 'fix
                (list (first rest))))))

    (add-macro-fn + binary-+ t)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t +)))

(defrule +-type-prescription
  (intervalp (+ x y))
  :rule-classes ((:type-prescription :typed-term (+ x y))))

(defrule +-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (+ x0 y)
                  (+ x1 y)))
  :rule-classes :congruence
  :enable +)

(defrule +-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (+ x y0)
                  (+ x y1)))
  :rule-classes :congruence
  :enable +)

(defrule associativity-of-+
  (equal (+ (+ x y) z)
         (+ x y z))
  :enable (+
           min-of-interval
           max-of-interval))

(defrule commutativity-of-+
  (equal (+ y x)
         (+ x y))
  :enable +)

(defrule commutativity-2-of-+
  (equal (+ y x z)
         (+ x y z))
  :enable (+
           min-of-interval
           max-of-interval))

(defrule +-of-nil
  (equal (+ nil y)
         (empty))
  :enable +)

(defrule +-of-empty
  (equal (+ (empty) y)
         (empty))
  :enable +)

(defrule +-of-arg1-and-nil
  (equal (+ x nil)
         (empty))
  :enable +)

(defrule +-of-arg1-and-empty
  (equal (+ x (empty))
         (empty))
  :enable +)

(defrule +-of-interval-0-0
  (equal (+ (interval 0 0) y)
         (fix y))
  :enable (+
           acl2::fix))

(defrule +-of-arg1-and-interval-0-0
  (equal (+ x (interval 0 0))
         (fix x))
  :enable (+
           acl2::fix))

(defrule +-of-exact-0
  (equal (+ (exact 0) y)
         (fix y))
  :enable exact)

(defrule +-of-arg1-and-exact-0
  (equal (+ x (exact 0))
         (fix x))
  :enable exact)

(defrule +-of-full
  (equal (+ (intersect nil nil) y)
         (intersect nil nil))
  :enable +)

(defrule +-of-arg1-and-full
  (equal (+ x (intersect nil nil))
         (intersect nil nil))
  :enable +)

(defrule +-of-exact-exact
  (equal (+ (exact x) (exact y))
         (exact (acl2::+ (rfix x) (rfix y))))
  :enable (+
           exact))

(defruled min-of-+
  (equal (min (+ x y))
         (if (and (bounded-below-p x)
                  (bounded-below-p y))
             (acl2::+ (min x) (min y))
           nil))
  :enable (+
           min-of-interval))

(defruled min-of-+-when-not-bounded-below-p-of-arg1
  (implies (not (bounded-below-p x))
           (equal (min (+ x y))
                  nil))
  :by min-of-+)

(defrule min-of-+-when-not-bounded-below-p-of-arg1-cheap
  (implies (not (bounded-below-p x))
           (equal (min (+ x y))
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by min-of-+-when-not-bounded-below-p-of-arg1)

(defruled min-of-+-when-not-bounded-below-p-of-arg2
  (implies (not (bounded-below-p y))
           (equal (min (+ x y))
                  nil))
  :by min-of-+)

(defrule min-of-+-when-not-bounded-below-p-of-arg2-cheap
  (implies (not (bounded-below-p y))
           (equal (min (+ x y))
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by min-of-+-when-not-bounded-below-p-of-arg2)

(defruled min-of-+-when-bounded-below-p
  (implies (and (bounded-below-p x)
                (bounded-below-p y))
           (equal (min (+ x y))
                  (acl2::+ (min x) (min y))))
  :by min-of-+)

(defrule min-of-+-when-bounded-below-p-cheap
  (implies (and (bounded-below-p x)
                (bounded-below-p y))
           (equal (min (+ x y))
                  (acl2::+ (min x) (min y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :by min-of-+-when-bounded-below-p)

(defrule bounded-below-p-of-+
  (equal (bounded-below-p (+ x y))
         (and (bounded-below-p x)
              (bounded-below-p y)))
  :enable (bounded-below-p
           min-of-+)
  :disable min-under-iff)

(defruled max-of-+
  (equal (max (+ x y))
         (if (and (bounded-above-p x)
                  (bounded-above-p y))
             (acl2::+ (max x) (max y))
           nil))
  :enable (+
           max-of-interval))

(defruled max-of-+-when-not-bounded-above-p-of-arg1
  (implies (not (bounded-above-p x))
           (equal (max (+ x y))
                  nil))
  :by max-of-+)

(defrule max-of-+-when-not-bounded-above-p-of-arg1-cheap
  (implies (not (bounded-above-p x))
           (equal (max (+ x y))
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by max-of-+-when-not-bounded-above-p-of-arg1)

(defruled max-of-+-when-not-bounded-above-p-of-arg2
  (implies (not (bounded-above-p y))
           (equal (max (+ x y))
                  nil))
  :by max-of-+)

(defrule max-of-+-when-not-bounded-above-p-of-arg2-cheap
  (implies (not (bounded-above-p y))
           (equal (max (+ x y))
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by max-of-+-when-not-bounded-above-p-of-arg2)

(defruled max-of-+-when-bounded-above-p
  (implies (and (bounded-above-p x)
                (bounded-above-p y))
           (equal (max (+ x y))
                  (acl2::+ (max x) (max y))))
  :by max-of-+)

(defrule max-of-+-when-bounded-above-p-cheap
  (implies (and (bounded-above-p x)
                (bounded-above-p y))
           (equal (max (+ x y))
                  (acl2::+ (max x) (max y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :by max-of-+-when-bounded-above-p)

(defrule bounded-above-p-of-+
  (equal (bounded-above-p (+ x y))
         (and (bounded-above-p x)
              (bounded-above-p y)))
  :enable (bounded-above-p
           max-of-+)
  :disable max-under-iff)

(defrule boundedp-of-+
  (equal (boundedp (+ x y))
         (and (boundedp x)
              (boundedp y)))
  :enable boundedp)

(defrule equal-of-+-and-nil
  (equal (equal (+ x y) nil)
         (or (equal x (empty))
             (equal y (empty))))
  :enable +)

(defrule equal-of-+-empty
  (equal (equal (+ x y) (empty))
         (or (equal x (empty))
             (equal y (empty))))
  :enable +)

(defrule +-when-boundedp
  (implies (and (boundedp x)
                (boundedp y))
           (equal (+ x y)
                  (interval (acl2::+ (min x) (min y))
                            (acl2::+ (max x) (max y)))))
  :enable equal-of-intervals)

(defrule monotonicity-of-+
  (implies (and (subintervalp x-sub x-sup)
                (subintervalp y-sub y-sup))
           (subintervalp (+ x-sub y-sub)
                         (+ x-sup y-sup)))

  :enable (subintervalp
           +
           min-of-interval
           max-of-interval
           bounded-below-p-of-interval
           bounded-above-p-of-interval))

(defruled monotonicity-of-+-left
  (implies (subintervalp x-sub x-sup)
           (subintervalp (+ x-sub y)
                         (+ x-sup y))))

(defruled monotonicity-of-+-right
  (implies (subintervalp y-sub y-sup)
           (subintervalp (+ x y-sub)
                         (+ x y-sup))))

(defruled +-is-interval-extension
  (implies (and (inp a x)
                (inp b y))
           (inp (acl2::+ (rfix a) (rfix b))
                (+ x y)))
  :enable (+
           inp
           min-of-interval
           max-of-interval))

;; Given a `sum` s.t. `(inp sum (+ x y))`,
;; finds a rational witness s.t.
;; `(inp witness x)`
;; and
;; `(inp (- (rfix sum) witness) y)`
(define +-precise-witness
  ((sum rationalp)
   (x intervalp)
   (y intervalp))
  :returns (witness rationalp)
  (cond ((or (emptyp x)
             (emptyp y))
         0)
        ((and (bounded-below-p x)
              (bounded-above-p y))
         (acl2::max (min x)
                    (acl2::- (rational-fix sum) (max y))))
        ((bounded-below-p x)
         (min x))
        ((bounded-above-p y)
         (acl2::- (rational-fix sum) (max y)))
        ((and (bounded-above-p x)
              (bounded-below-p y))
         (acl2::min (max x)
                    (acl2::- (rational-fix sum) (min y))))
        ((bounded-above-p x)
         (max x))
        ((bounded-below-p y)
         (acl2::- (rational-fix sum) (min y)))
        (t 0)))

(defruled inp-of-+-precise-witness-and-arg1
  (implies (inp sum (+ x y))
           (inp (+-precise-witness sum x y) x))
  :enable (+-precise-witness
           +
           inp
           max-of-interval))

(defruled inp-of-+-precise-witness-and-arg2
  (implies (inp sum (+ x y))
           (inp (acl2::- (rfix sum) (+-precise-witness sum x y))
                y))
  :enable (+-precise-witness
           +
           inp
           acl2::max
           min-of-interval))

(defruled +-precise
  (implies (inp sum (+ x y))
           ;; some-a and some-b should be read as existentials
           (let* ((some-a (+-precise-witness sum x y))
                  (some-b (acl2::- (rfix sum) some-a)))
             (and (inp some-a x)
                  (inp some-b y)
                  (equal (rfix sum)
                         (acl2::+ some-a some-b)))))
  :use (inp-of-+-precise-witness-and-arg1
        inp-of-+-precise-witness-and-arg2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: -, *, /, etc.
