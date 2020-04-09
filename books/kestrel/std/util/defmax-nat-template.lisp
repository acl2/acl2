; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/basic/defs" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Mathematically, DEFMAX-NAT introduces a function of the form
;
; f(x1,...,xn) = max {y in Nat | psi<x1,...,xn,y>}
;
; where:
; - n >= 0;
; - Nat is the set of natural numbers;
; - psi<x1,...,xn,y> is a formula that depends on x1,...,xn and y;
; - max is regarded as returning a special value (distinct from natural numbers)
;   when the set has no maximum.

; This file formalizes this function,
; along with related functions, theorems, and proofs,
; in schematic form, for n = 1 (using x for x1,...,xn).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The guard on x1,...,xn.
; This can be anything, so we use a constrained function XP here.

(encapsulate
  (((xp *) => *))
  (local (defun xp (x) x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The set {y in Nat | psi<x1,...,xn,y>}.
; This can be anything, so we use a constrained function ELEMENTP here,
; which tests the membership of its 2nd argument Y
; in the set defined by its 1st argument X.
; The set is (LAMBDA (Y) (AND (NATP Y) (ELEMENTP X Y))).
; ELEMENTP corresponds to psi, viewed as a predicate.
; This only needs to be well-defined for
; X satisfying its guard and Y being a natural number,
; hence the guard below.

(encapsulate
  (((elementp * *) => * :formals (x y) :guard (and (xp x) (natp y))))
  (local (defun elementp (x y) (cons x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; True iff Y is an upper bound of the set defined by X.
; That is, every Y1 in the set is less than or equal to Y.

(defun-sk uboundp (x y)
  (declare (xargs :guard (and (xp x) (natp y))))
  (forall (y1)
          (impliez (and (natp y1)
                        (elementp x y1))
                   (>= (nfix y) y1)))
  :rewrite (implies (and (uboundp x y)
                         (natp y1)
                         (elementp x y1))
                    (>= (nfix y) y1)))

(defthm booleanp-of-uboundp
  (booleanp (uboundp x y)))

(in-theory (disable uboundp uboundp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; True iff the set defined by X has a maximum.
; That is, there is a natural number Y in the set
; that is also an upper of the set.
; Note that (EXISTSP-WITNESS X) is that Y.

(defun-sk existsp (x)
  (declare (xargs :guard (xp x)))
  (exists (y)
          (and (natp y)
               (elementp x y)
               (uboundp x y)))
  :skolem-name existsp-witness)

(defthm booleanp-of-existsp
  (booleanp (existsp x)))

(in-theory (disable existsp existsp-suff))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Definition of the function f.
; If the set has no maximum, the function returns NIL.
; The theorems below show that the definition is correct.

(defun f (x)
  (declare (xargs :guard (xp x)))
  (if (existsp x)
      (existsp-witness x)
    nil))

(defthm maybe-natp-of-f
  (maybe-natp (f x))
  :hints (("Goal" :in-theory (enable maybe-natp existsp))))

(defthm natp-of-f-equal-existsp
  (equal (natp (f x))
         (existsp x))
  :hints (("Goal" :in-theory (enable existsp))))

(defthm natp-of-f-when-existsp
  (implies (existsp x)
           (natp (f x)))
  :rule-classes :type-prescription)

(defthm f-iff-existsp
  (iff (f x)
       (existsp x))
  :hints (("Goal" :in-theory (enable existsp))))

(defthm not-f-when-not-existsp
  (implies (not (existsp x))
           (not (f x)))
  :rule-classes :type-prescription)

(defthm elementp-of-f-when-existsp
  (implies (existsp x)
           (elementp x (f x)))
  :hints (("Goal" :in-theory (enable existsp))))

(defthm uboundp-of-f-when-existsp
  (implies (existsp x)
           (uboundp x (f x)))
  :hints (("Goal" :in-theory (enable existsp))))

(defthm f-geq-when-existsp-linear
  (implies (and (existsp x)
                (elementp x y1) ; bind free Y1
                (natp y1))
           (>= (f x) y1))
  :rule-classes :linear
  :hints (("Goal"
           :use (uboundp-of-f-when-existsp
                 (:instance uboundp-necc (y (f x)))))))

(defthm f-geq-when-existsp-rewrite
  (implies (and (existsp x)
                (elementp x y1)
                (natp y1))
           (>= (f x) y1))
  :hints (("Goal" :by f-geq-when-existsp-linear)))

(defthm f-leq-when-existsp-linear
  (implies (and (existsp x)
                (uboundp x y1) ; bind free y1
                (natp y1))
           (<= (f x) y1))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (disable f)
           :use (:instance uboundp-necc (y1 (f x)) (y y1)))))

(defthm f-leq-when-existsp-rewrite
  (implies (and (existsp x)
                (uboundp x y1) ; bind free y1
                (natp y1))
           (<= (f x) y1))
  :hints (("Goal" :by f-leq-when-existsp-linear)))

(in-theory (disable f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helper theorem #1:
; the set has a maximum if it is not empty and has some upper bound.
; This lets us establish the existence of the maximum without calculating it,
; if we can exhibit a member and an upper bound of the set.

; The helper theorem (EXISTSP-WHEN-NONEMPTY-AND-BOUNDED) is proved as follows.
; Given a member Y0 of the set and an upper bound Y1 of the set,
; we find the maximum by starting from Y1 and counting down towards Y0.
; We stop as soon as we find a member of the set (possibly Y1 itself).
; If the current Y1 is not a member, we decrease it by 1 and re-check;
; this must eventually terminate, at Y0 in the worst case.

; If Y0 is a member and Y1 is an upper bound, then Y1 >= Y0.

(defthm ubound-geq-member
  (implies (and (natp y0)
                (elementp x y0)
                (natp y1)
                (uboundp x y1))
           (>= y1 y0))
  :rule-classes nil
  :hints (("Goal" :use (:instance uboundp-necc (y y1) (y1 y0)))))

; If Y0 is a member and Y1 is an upper bound not in the set, then Y1 > Y0,
; from the previous theorem and from the fact that they cannot be equal.

(defthm ubound-nonmember-gt-member
  (implies (and (natp y0)
                (elementp x y0)
                (natp y1)
                (uboundp x y1)
                (not (elementp x y1)))
           (> y1 y0))
  :rule-classes nil
  :hints (("Goal" :use ubound-geq-member)))

; This is how we find the maximum, starting from Y1 and counting down.
; This function is only relevant when Y0 is a member and Y1 is an upper bound,
; so the outer IF tests that.
; Under these conditions, if Y1 is not in the set,
; it must be greater than Y0 and in particular greater than 0,
; which ensures the termination of this counting function.
; Below we show that FIND-MAX indeed returns the maximum.

(defun find-max (x y1 y0)
  (declare (xargs :hints (("Goal" :use ubound-nonmember-gt-member))))
  (if (and (natp y0)
           (elementp x y0)
           (natp y1)
           (uboundp x y1))
      (if (elementp x y1)
          y1
        (find-max x (1- y1) y0))
    0)) ; irrelevant

; A key property of FIND-MAX is that if Y1 is not in the set,
; then Y1-1 is still an upper bound.

(defthm find-max-uboundp-preservation
  (implies (and (natp y0)
                (elementp x y0)
                (natp y1)
                (uboundp x y1)
                (not (elementp x y1)))
           (uboundp x (1- y1)))
  :hints (("Goal"
           :expand ((uboundp x (1- y1)))
           :use (:instance uboundp-necc
                 (y y1)
                 (y1 (uboundp-witness x (1- y1)))))))

; FIND-MAX eventually returns an element of the set.
; This proof makes use of the preservation theorem above.

(defthm elementp-of-find-max
  (implies (and (natp y0)
                (elementp x y0)
                (natp y1)
                (uboundp x y1))
           (elementp x (find-max x y1 y0)))
  :hints ('(:use (:instance uboundp-necc (y y1) (y1 0)))
          '(:use (:instance uboundp-necc (y 0) (y1 y0)))))

; FIND-MAX eventually returns an upper bound of the set.
; This proof makes use of the preservation theorem above.

(defthm uboundp-of-find-max
  (implies (and (natp y0)
                (elementp x y0)
                (natp y1)
                (uboundp x y1))
           (uboundp x (find-max x y1 y0)))
  :hints ('(:use (:instance uboundp-necc (y y1) (y1 0)))
          '(:use (:instance uboundp-necc (y 0) (y1 y0)))))

; Since FIND-MAX returns a member that is also an upper bound,
; the set has a maximum (returned by FIND-MAX).
; This is the first helper theorem generated by DEFMAX-NAT.
; It can be used via
; :USE (:INSTANCE EXISTSP-WHEN-NONEMPTY-AND-BOUNDED
;                 (Y0 <some-member-of-the-set>)
;                 (Y1 <some-upper-bound-of-the-set>)).

(defthm existsp-when-nonempty-and-bounded
  (implies (and (natp y0)
                (elementp x y0)
                (natp y1)
                (uboundp x y1))
           (existsp x))
  :rule-classes nil
  :hints (("Goal" :use (:instance existsp-suff (y (find-max x y1 y0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helper theorem #2:
; a natural number that is both a member and an upper bound of the set
; is the maximum.

; This helper theorem is proved as follows.
; First, use the helper theorem #1 above to establish (EXISTSP X),
; using Y as both Y0 and Y1.
; From F-GEQ-WHEN-EXISTSP-REWRITE, we have (F X) >= Y.
; From the (UBOUNDP X Y) hypothesis, we have Y >= (F X),
; because (F X) is in the set by ELEMENTP-OF-F-WHEN-EXISTSP.
; Since both (F X) and Y are natural numbers, they must be equal.

; This is the second helper theorem generated by DEFMAX-NAT.
; It can be used via
; :USE (:INSTANCE EQUAL-WHEN-MEMBER-AND-BOUND
;                 (Y <some-member-and-upper-bound-of-the-set>)).

(defthm equal-when-member-and-ubound
  (implies (and (natp y)
                (elementp x y)
                (uboundp x y))
           (equal (f x) y))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable f-geq-when-existsp-rewrite)
           :use ((:instance existsp-when-nonempty-and-bounded (y0 y) (y1 y))
                 (:instance f-geq-when-existsp-rewrite (y1 y))
                 (:instance uboundp-necc (y1 (f x)))))))
