; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
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
(include-book "inp")

(local (include-book "kestrel/arithmetic-light/max" :dir :system))
(local (include-book "kestrel/arithmetic-light/min" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subintervalp
  ((x intervalp)
   (y intervalp))
  :returns (yes/no booleanp)
  :parents (intervals)
  :short "Check that one interval is totally contained within another."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is a partial order on intervals. With @(tsee hull) (the join) and
      @(tsee intersect) (the meet), it forms a bounded lattice. The
      bottom/minimum element is @('(empty)'). The top/maximum element is
      @('(full)').")
   (xdoc::p
     "Note that the lattice is not distributive, nor is it modular."))
  (or (emptyp x)
      (and (not (emptyp y))
           (mbe :logic (and (implies (bounded-below-p y)
                                     (and (bounded-below-p x)
                                          (<= (min y) (min x))))
                            (implies (bounded-above-p y)
                                     (and (bounded-above-p x)
                                          (<= (max x) (max y)))))
                :exec (let ((min-y (min y))
                            (max-y (max y)))
                        (and (or (null min-y)
                                 (let ((min-x (min x)))
                                   (and min-x (<= min-y min-x))))
                             (or (null max-y)
                                 (let ((max-x (max x)))
                                   (and max-x (<= max-x max-y)))))))))
  :guard-hints (("Goal" :in-theory (e/d (bounded-below-p
                                         bounded-above-p)
                                        (min-under-iff
                                         max-under-iff)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t subintervalp)))

(defrule subintervalp-type-prescription
  (booleanp (subintervalp x y))
  :rule-classes ((:type-prescription :typed-term (subintervalp x y))))

(defrule subintervalp-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (subintervalp x0 y)
                  (subintervalp x1 y)))
  :rule-classes :congruence
  :enable subintervalp)

(defrule subintervalp-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (subintervalp x y0)
                  (subintervalp x y1)))
  :rule-classes :congruence
  :enable subintervalp)

(defrule revlexivity-of-subintervalp
  (subintervalp x x)
  :enable subintervalp)

(defruled subintervalp-when-equal
  (implies (equal x y)
           (subintervalp x y)))

(defrule subintervalp-when-equal-cheap
  (implies (equal x y)
           (subintervalp x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defruled antisymmetry-of-subintervalp-weak
  (implies (and (subintervalp x y)
                (subintervalp y x))
           (equiv x y))
  :enable (subintervalp
           equiv
           fix
           intervalp
           interval
           min
           max
           bounded-below-p
           bounded-above-p)
  :disable (min-under-iff
            max-under-iff))

(defruled antisymmetry-of-subintervalp
  (equal (and (subintervalp x y)
              (subintervalp y x))
         (equiv x y))
  :use antisymmetry-of-subintervalp-weak)

(defrule transitivity-of-subintervalp
  (implies (and (subintervalp x y)
                (subintervalp y z))
           (subintervalp x z))
  :enable subintervalp)

(defrule subintervalp-of-nil
  (subintervalp nil y)
  :enable subintervalp)

(defrule subintervalp-of-empty
  (subintervalp (empty) y)
  :enable subintervalp)

(defrule subintervalp-of-arg1-and-nil
  (equal (subintervalp x nil)
         (equal x (empty)))
  :enable subintervalp)

(defrule subintervalp-of-arg1-and-empty
  (equal (subintervalp x (empty))
         (equal x (empty)))
  :enable subintervalp)

(defrule subintervalp-of-full
  (equal (subintervalp (interval nil nil) y)
         (equal (fix y) (interval nil nil)))
  :enable subintervalp)

(defrule subintervalp-of-arg1-and-full
  (subintervalp x (interval nil nil))
  :enable subintervalp)

(defrule inp-when-subintervalp
  (implies (and (subintervalp x y)
                (inp r x))
           (inp r y))
  :enable (subintervalp
           inp))

(defruled inp-becomes-subintervalp-definition
  (equal (inp r interval)
         (subintervalp (exact (rfix r)) interval))
  :rule-classes :definition
  :enable (inp
           subintervalp))

(defrule bounded-below-p-when-subintervalp-and-bounded-below-p
  (implies (and (subintervalp x y)
                (bounded-below-p y))
           (equal (bounded-below-p x)
                  (not (equal x (empty)))))
  :enable subintervalp)

(defrule bounded-above-p-when-subintervalp-and-bounded-above-p
  (implies (and (subintervalp x y)
                (bounded-above-p y))
           (equal (bounded-above-p x)
                  (not (equal x (empty)))))
  :enable subintervalp)

(defrule boundedp-when-subintervalp-and-boundedp
  (implies (and (subintervalp x y)
                (boundedp y))
           (equal (boundedp x)
                  (not (equal x (empty)))))
  :enable boundedp)

(defrule <=-of-min-when-subintervalp
  (implies (and (subintervalp x y)
                (bounded-below-p y)
                ;; This will likely backchain to
                ;; bounded-below-p-when-subintervalp-and-bounded-below-p
                (bounded-below-p x))
           (<= (min y)
               (min x)))
  :enable subintervalp
  :rule-classes (:rewrite :linear))

(defrule <=-of-max-when-subintervalp
  (implies (and (subintervalp x y)
                (bounded-above-p y)
                ;; This will likely backchain to
                ;; bounded-above-p-when-subintervalp-and-bounded-above-p
                (bounded-above-p x))
           (<= (max x)
               (max y)))
  :enable subintervalp
  :rule-classes (:rewrite :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection intersect
  :parents (intervals)
  :short "Find the intersection of two or more intervals."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is the ``meet'' of the @(tsee subintervalp) lattice."))

  (define binary-intersect
    ((x intervalp)
     (y intervalp))
    :returns (intersect intervalp)
    (if (or (emptyp x)
            (emptyp y))
        (empty)
      (interval$ (let ((min-x (min x))
                       (min-y (min y)))
                   (cond ((null min-x) min-y)
                         ((null min-y) min-x)
                         (t (acl2::max min-x min-y))))
                 (let ((max-x (max x))
                       (max-y (max y)))
                   (cond ((null max-x) max-y)
                         ((null max-y) max-x)
                         (t (acl2::min max-x max-y))))))
    ///

    (defmacro intersect (&rest rest)
      (if (endp rest)
          '(full)
        (if (rest rest)
            (xxxjoin 'binary-intersect rest)
          (cons 'fix
                (list (first rest))))))

    (add-macro-fn intersect binary-intersect t)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t intersect)))

(defrule intersect-type-prescription
  (intervalp (intersect x y))
  :rule-classes ((:type-prescription :typed-term (intersect x y))))

(defrule intersect-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (intersect x0 y)
                  (intersect x1 y)))
  :rule-classes :congruence
  :enable intersect)

(defrule intersect-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (intersect x y0)
                  (intersect x y1)))
  :rule-classes :congruence
  :enable intersect)

(defrule associativity-of-intersect
  (equal (intersect (intersect x y) z)
         (intersect x y z))
  :enable (intersect
           min-of-interval
           max-of-interval))

(defrule commutativity-of-intersect
  (equal (intersect y x)
         (intersect x y))
  :enable intersect)

(defrule commutativity-2-of-intersect
  (equal (intersect y x z)
         (intersect x y z))
  :enable (intersect
           min-of-interval
           max-of-interval))

(defrule idempotence-of-intersect
  (equal (intersect x x)
         (fix x))
  :enable intersect)

(defrule contraction-of-intersect
  (equal (intersect x (intersect x y))
         (intersect x y))
  :enable (intersect
           min-of-interval
           max-of-interval))

(defrule intersect-of-nil
  (equal (intersect nil y)
         (empty))
  :enable intersect)

(defrule intersect-of-empty
  (equal (intersect (empty) y)
         (empty))
  :enable intersect)

(defrule intersect-of-arg1-and-nil
  (equal (intersect x nil)
         (empty)))

(defrule intersect-of-arg1-and-empty
  (equal (intersect x (empty))
         (empty)))

(defrule intersect-of-full
  (equal (intersect (interval nil nil) y)
         (fix y))
  :enable intersect)

(defrule intersect-of-arg1-and-full
  (equal (intersect x (interval nil nil))
         (fix x)))

(defrule subintervalp-of-arg1-and-intersect
  (equal (subintervalp a (intersect x y))
         (and (subintervalp a x)
              (subintervalp a y)))
  :enable (subintervalp
           intersect
           min-of-interval
           max-of-interval
           bounded-below-p-of-interval
           bounded-above-p-of-interval))

;; TODO: rules about min/max/bounded of intersect? It is complicated by the
;; fact that bounded intervals may intersect to the empty interval.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hull
  :parents (intervals)
  :short "Find the hull of two or more intervals."
  :long
  (xdoc::topstring
    (xdoc::p
      "By ``hull'', we mean the smallest interval that contains both intervals.
       This is the ``join'' of the @(tsee subintervalp) lattice."))

  (define binary-hull
    ((x intervalp)
     (y intervalp))
    :returns (hull intervalp)
    (cond ((emptyp x) (fix y))
          ((emptyp y) (fix x))
          (t (interval (let ((min-x (min x))
                             (min-y (min y)))
                         (if (and min-x min-y)
                             (acl2::min min-x min-y)
                           nil))
                       (let ((max-x (max x))
                             (max-y (max y)))
                         (if (and max-x max-y)
                             (acl2::max max-x max-y)
                           nil)))))
    ///

    (defmacro hull (&rest rest)
      (if (endp rest)
          '(empty)
        (if (rest rest)
            (xxxjoin 'binary-hull rest)
          (cons 'fix
                (list (first rest))))))

    (add-macro-fn hull binary-hull t)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t hull)))

(defrule hull-type-prescription
  (intervalp (hull x y))
  :rule-classes ((:type-prescription :typed-term (hull x y))))

(defrule hull-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (hull x0 y)
                  (hull x1 y)))
  :rule-classes :congruence
  :enable hull)

(defrule hull-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (hull x y0)
                  (hull x y1)))
  :rule-classes :congruence
  :enable hull)

(defrule associativity-of-hull
  (equal (hull (hull x y) z)
         (hull x y z))
  :enable (hull
           min-of-interval
           max-of-interval))

(defrule commutativity-of-hull
  (equal (hull y x)
         (hull x y))
  :enable hull)

(defrule commutativity-2-of-hull
  (equal (hull y x z)
         (hull x y z))
  :enable (hull
           min-of-interval
           max-of-interval))

(defrule idempotence-of-hull
  (equal (hull x x)
         (fix x))
  :enable hull)

(defrule contraction-of-hull
  (equal (hull x x y)
         (hull x y))
  :enable (hull
           min-of-interval
           max-of-interval))

(defrule hull-of-nil
  (equal (hull nil y)
         (fix y))
  :enable hull)

(defrule hull-of-empty
  (equal (hull (empty) y)
         (fix y))
  :enable hull)

(defrule hull-of-arg1-and-nil
  (equal (hull x nil)
         (fix x))
  :enable hull)

(defrule hull-of-arg1-and-empty
  (equal (hull x (empty))
         (fix x))
  :enable hull)

(defrule hull-of-full
  (equal (hull (interval nil nil) y)
         (interval nil nil))
  :enable hull)

(defrule hull-of-arg1-and-full
  (equal (hull x (interval nil nil))
         (interval nil nil))
  :enable hull)

(defrule equal-of-hull-and-nil
  (equal (equal (hull x y) nil)
         (and (equal x (empty))
              (equal y (empty))))
  :enable (hull
           fix))

(defrule equal-of-hull-and-empty
  (equal (equal (hull x y) (empty))
         (and (equal x (empty))
              (equal y (empty))))
  :enable (hull
           fix))

(defrule subintervalp-of-hull
  (equal (subintervalp (hull x y) a)
         (and (subintervalp x a)
              (subintervalp y a)))
  :enable (subintervalp
           hull
           min-of-interval
           max-of-interval
           bounded-below-p-of-interval
           bounded-above-p-of-interval))

(defruled min-of-hull
  (equal (min (hull x y))
         (cond ((emptyp x) (min y))
               ((emptyp y) (min x))
               (t (if (and (min x) (min y))
                      (acl2::min (min x) (min y))
                    nil))))
  :enable (hull
           min-of-interval))

(defruled min-of-hull-when-bounded-below-p
  (implies (and (bounded-below-p x)
                (bounded-below-p y))
           (equal (min (hull x y))
                  (acl2::min (min x) (min y))))
  :use min-of-hull)

(defrule min-of-hull-when-bounded-below-p-cheap
  (implies (and (bounded-below-p x)
                (bounded-below-p y))
           (equal (min (hull x y))
                  (acl2::min (min x) (min y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :by min-of-hull-when-bounded-below-p)

(defruled bounded-below-p-of-hull
  (equal (bounded-below-p (hull x y))
         (cond ((emptyp x) (bounded-below-p y))
               ((emptyp y) (bounded-below-p x))
               (t (and (bounded-below-p x) (bounded-below-p y)))))
  :enable (min-of-hull
           bounded-below-p)
  :disable min-under-iff)

(defrule bounded-below-p-of-hull-when-bounded-below-p
  (implies (and (bounded-below-p x)
                (bounded-below-p y))
           (bounded-below-p (hull x y)))
  :use bounded-below-p-of-hull)

(defruled max-of-hull
  (equal (max (hull x y))
         (cond ((emptyp x) (max y))
               ((emptyp y) (max x))
               (t (if (and (max x) (max y))
                      (acl2::max (max x) (max y))
                    nil))))
  :enable (hull
           max-of-interval))

(defruled max-of-hull-when-bounded-above-p
  (implies (and (bounded-above-p x)
                (bounded-above-p y))
           (equal (max (hull x y))
                  (acl2::max (max x) (max y))))
  :use max-of-hull)

(defrule max-of-hull-when-bounded-above-p-cheap
  (implies (and (bounded-above-p x)
                (bounded-above-p y))
           (equal (max (hull x y))
                  (acl2::max (max x) (max y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :by max-of-hull-when-bounded-above-p)

(defruled bounded-above-p-of-hull
  (equal (bounded-above-p (hull x y))
         (cond ((emptyp x) (bounded-above-p y))
               ((emptyp y) (bounded-above-p x))
               (t (and (bounded-above-p x) (bounded-above-p y)))))
  :enable (max-of-hull
           bounded-above-p)
  :disable max-under-iff)

(defrule bounded-above-p-of-hull-when-bounded-above-p
  (implies (and (bounded-above-p x)
                (bounded-above-p y))
           (bounded-above-p (hull x y)))
  :use bounded-above-p-of-hull)

(defrule boundedp-of-hull-when-boundedp
  (implies (and (boundedp x)
                (boundedp y))
           (boundedp (hull x y)))
  :enable boundedp)
