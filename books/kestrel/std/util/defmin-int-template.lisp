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

; Mathematically, DEFMIN-INT introduces a function of the form
;
; f(x1,...,xn) = min {y in Int | psi<x1,...,xn,y>}
;
; where:
; - n >= 0;
; - Int is the set of integer numbers;
; - psi<x1,...,xn,y> is a formula that depends on x1,...,xn and y;
; - min is regarded as returning a special value (distinct from integer numbers)
;   when the set has no minimum.

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

; The set {y in Int | psi<x1,...,xn,y>}.
; This can be anything, so we use a constrained function ELEMENTP here,
; which tests the membership of its 2nd argument Y
; in the set defined by its 1st argument X.
; The set is (LAMBDA (Y) (AND (INTEGERP Y) (ELEMENTP X Y))).
; ELEMENTP corresponds to psi, viewed as a predicate.
; This only needs to be well-defined for
; X satisfying its guard and Y being an integer number,
; hence the guard below.

(encapsulate
  (((elementp * *) => * :formals (x y) :guard (and (xp x) (integerp y))))
  (local (defun elementp (x y) (cons x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; True iff Y is a lower bound of the set defined by X.
; That is, every Y1 in the set is less than or equal to Y.

(defun-sk lboundp (x y)
  (declare (xargs :guard (and (xp x) (integerp y))))
  (forall (y1)
          (impliez (and (integerp y1)
                        (elementp x y1))
                   (<= (ifix y) y1)))
  :rewrite (implies (and (lboundp x y)
                         (integerp y1)
                         (elementp x y1))
                    (<= (ifix y) y1)))

(defthm booleanp-of-lboundp
  (booleanp (lboundp x y)))

(in-theory (disable lboundp lboundp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; True iff the set defined by X has a minimum.
; That is, there is an integer number Y in the set
; that is also a lower bound of the set.
; Note that (EXISTSP-WITNESS X) is that Y.

(defun-sk existsp (x)
  (declare (xargs :guard (xp x)))
  (exists (y)
          (and (integerp y)
               (elementp x y)
               (lboundp x y)))
  :skolem-name existsp-witness)

(defthm booleanp-of-existsp
  (booleanp (existsp x)))

(in-theory (disable existsp existsp-suff))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Definition of the function f.
; If the set has no minimum, the function returns NIL.
; The theorems below show that the definition is correct.

(defun f (x)
  (declare (xargs :guard (xp x)))
  (if (existsp x)
      (existsp-witness x)
    nil))

(defthm maybe-integerp-of-f
  (maybe-integerp (f x))
  :hints (("Goal" :in-theory (enable maybe-integerp existsp))))

(defthm integerp-of-f-equal-existsp
  (equal (integerp (f x))
         (existsp x))
  :hints (("Goal" :in-theory (enable existsp))))

(defthm integerp-of-f-when-existsp
  (implies (existsp x)
           (integerp (f x)))
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

(defthm lboundp-of-f-when-existsp
  (implies (existsp x)
           (lboundp x (f x)))
  :hints (("Goal" :in-theory (enable existsp))))

(defthm f-leq-when-existsp-linear
  (implies (and (existsp x)
                (elementp x y1) ; bind free Y1
                (integerp y1))
           (<= (f x) y1))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (disable f)
           :use (lboundp-of-f-when-existsp
                 (:instance lboundp-necc (y (f x)))))))

(defthm f-leq-when-existsp-rewrite
  (implies (and (existsp x)
                (elementp x y1)
                (integerp y1))
           (<= (f x) y1))
  :hints (("Goal" :by f-leq-when-existsp-linear)))

(defthm f-geq-when-existsp-linear
  (implies (and (existsp x)
                (lboundp x y1) ; bind free y1
                (integerp y1))
           (>= (f x) y1))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (disable f)
           :use (:instance lboundp-necc (y1 (f x)) (y y1)))))

(defthm f-geq-when-existsp-rewrite
  (implies (and (existsp x)
                (lboundp x y1) ; bind free y1
                (integerp y1))
           (>= (f x) y1))
  :hints (("Goal" :by f-geq-when-existsp-linear)))

(in-theory (disable f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helper theorem #1:
; the set has a minimum if it is not empty and has some lower bound.
; This lets us establish the existence of the minimum without calculating it,
; if we can exhibit a member and a lower bound of the set.

; The helper theorem (EXISTSP-WHEN-NONEMPTY-AND-BOUNDED) is proved as follows.
; Given a member Y0 of the set and a lower bound Y1 of the set,
; we find the minimum by starting from Y1 and counting up towards Y0.
; We stop as soon as we find a member of the set (possibly Y1 itself).
; If the current Y1 is not a member, we increase it by 1 and re-check;
; this must eventually terminate, at Y0 in the worst case.

; If Y0 is a member and Y1 is a lower bound, then Y1 <= Y0.

(defthm lbound-leq-member
  (implies (and (integerp y0)
                (elementp x y0)
                (integerp y1)
                (lboundp x y1))
           (<= y1 y0))
  :rule-classes nil
  :hints (("Goal" :use (:instance lboundp-necc (y y1) (y1 y0)))))

; If Y0 is a member and Y1 is a lower bound not in the set, then Y1 < Y0,
; from the previous theorem and from the fact that they cannot be equal.

(defthm lbound-nonmember-lt-member
  (implies (and (integerp y0)
                (elementp x y0)
                (integerp y1)
                (lboundp x y1)
                (not (elementp x y1)))
           (< y1 y0))
  :rule-classes nil
  :hints (("Goal" :use lbound-leq-member)))

; This is how we find the minimum, starting from Y1 and counting up.
; This function is only relevant when Y0 is a member and Y1 is a lower bound,
; so the outer IF tests that.
; Under these conditions, if Y1 is not in the set,
; it must be less than Y0,
; which ensures the termination of this counting function;
; the measure is the difference between Y0 and Y1.
; Below we show that FIND-MIN indeed returns the minimum.

(defun find-min (x y1 y0)
  (declare (xargs :measure (nfix (- y0 y1))
                  :hints (("Goal" :use lbound-nonmember-lt-member))))
  (if (and (integerp y0)
           (elementp x y0)
           (integerp y1)
           (lboundp x y1))
      (if (elementp x y1)
          y1
        (find-min x (1+ y1) y0))
    0)) ; irrelevant

; A key property of FIND-MIN is that if Y1 is not in the set,
; then Y1-1 is still a lower bound.

(defthm find-min-lboundp-preservation
  (implies (and (integerp y0)
                (elementp x y0)
                (integerp y1)
                (lboundp x y1)
                (not (elementp x y1)))
           (lboundp x (1+ y1)))
  :hints (("Goal"
           :expand ((lboundp x (1+ y1)))
           :use (:instance lboundp-necc
                 (y y1)
                 (y1 (lboundp-witness x (1+ y1)))))))

; FIND-MIN eventually returns an element of the set.
; This proof makes use of the preservation theorem above.

(defthm elementp-of-find-min
  (implies (and (integerp y0)
                (elementp x y0)
                (integerp y1)
                (lboundp x y1))
           (elementp x (find-min x y1 y0)))
  :hints ('(:use (:instance lboundp-necc (y y1) (y1 0)))
          '(:use (:instance lboundp-necc (y 0) (y1 y0)))))

; FIND-MIN eventually returns a lower bound of the set.
; This proof makes use of the preservation theorem above.

(defthm lboundp-of-find-min
  (implies (and (integerp y0)
                (elementp x y0)
                (integerp y1)
                (lboundp x y1))
           (lboundp x (find-min x y1 y0)))
  :hints ('(:use (:instance lboundp-necc (y y1) (y1 0)))
          '(:use (:instance lboundp-necc (y 0) (y1 y0)))))

; Since FIND-MIN returns a member that is also a lower bound,
; the set has a minimum (returned by FIND-MIN).
; This is the first helper theorem generated by DEFMIN-INT.
; It can be used via
; :USE (:INSTANCE EXISTSP-WHEN-NONEMPTY-AND-BOUNDED
;                 (Y0 <some-member-of-the-set>)
;                 (Y1 <some-lower-bound-of-the-set>)).

(defthm existsp-when-nonempty-and-bounded
  (implies (and (integerp y0)
                (elementp x y0)
                (integerp y1)
                (lboundp x y1))
           (existsp x))
  :rule-classes nil
  :hints (("Goal" :use (:instance existsp-suff (y (find-min x y1 y0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helper theorem #2:
; an integer number that is both a member and a lower bound of the set
; is the minimum.

; This helper theorem is proved as follows.
; First, use the helper theorem #1 above to establish (EXISTSP X),
; using Y as both Y0 and Y1.
; From F-LEQ-WHEN-EXISTSP-REWRITE, we have (F X) <= Y.
; From the (LBOUNDP X Y) hypothesis, we have Y <= (F X),
; because (F X) is in the set by ELEMENTP-OF-F-WHEN-EXISTSP.
; Since both (F X) and Y are integer numbers, they must be equal.

; This is the second helper theorem generated by DEFMIN-INT.
; It can be used via
; :USE (:INSTANCE EQUAL-WHEN-MEMBER-AND-BOUND
;                 (Y <some-member-and-lower-bound-of-the-set>)).

(defthm equal-when-member-and-lbound
  (implies (and (integerp y)
                (elementp x y)
                (lboundp x y))
           (equal (f x) y))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable f-leq-when-existsp-rewrite
                               f-geq-when-existsp-rewrite)
           :use ((:instance existsp-when-nonempty-and-bounded (y0 y) (y1 y))
                 (:instance f-leq-when-existsp-rewrite (y1 y))
                 (:instance lboundp-necc (y1 (f x)))))))
