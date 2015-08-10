; Copyright (C) 2013, ForrestHunt, Inc.
; Written by J Strother Moore, December 19, 2012
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Toy: Finding the Minimal Value of a Function over an Integer Interval

; To recertify:
; (certify-book "find-minimal-1d")

; Abstract: Suppose you have an integer-valued function, FMLA, of one integer
; argument, x, and you wish to find the minimal value of (FMLA x) as x ranges
; over a given interval lo <= x <= hi.  Below is a function that does it
; and a proof that it does it.

; Because of the context in which I wish to apply a result like this one, the
; function that finds the minimal value is tail-recursive.  That means it
; maintains an accumulator with the least value seen so far.  That gives rise
; to a generalization issue.

; None of this is deep mathematics!  The whole point of this exercise is just
; to do a toy example of this type of problem to guide me in the more
; complicated situation of finding a minimal of a dyadic function over the
; cross-product of two integer intervals.  Furthermore, this is a toy I must
; have worked half a dozen times before.  (See the examples of theorems called
; ``...-is-a-universal-quantifier'' in the Nqthm proveall from the 70s and
; 80s.)

(in-package "ACL2")

; Here is fmla : integerp --> integerp.

(encapsulate ((fmla (x) t))
             (local (defun fmla (x) (* x x)))
             (defthm integerp-fmla
               (implies (integerp x)
                        (integerp (fmla x)))
               :rule-classes :type-prescription))

; Scan the interval from lo to hi, accumulating into min the minimal value
; seen.  Min starts at nil, meaning ``nothing seen yet.''

(defun find-minimal1 (lo hi min)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hi)) (ifix lo)))))
  (cond
   ((not (and (integerp lo)
              (integerp hi)))
    min)
   ((> lo hi) min)
   (t (find-minimal1
       (+ 1 lo) hi
       (if (or (null min)
               (< (fmla lo) min))
           (fmla lo)
           min)))))

; Here is the wrapper that initializes the running minimal to nil.  We deal
; exclusively with the workhorse, find-minimal1, in our lemmas below and don't
; see find-minimal again until our final theorem.

(defun find-minimal (lo hi)
  (find-minimal1 lo hi nil))

(defthm find-minimal1-decreases
  (implies min
           (<= (find-minimal1 lo hi min) min))
  :rule-classes :linear)

(defthm integerp-find-minimal1
  (implies (and (integerp lo)
                (integerp hi)
                (or (null min) (integerp min)))
           (equal (integerp (find-minimal1 lo hi min))
                  (if (null min)
                      (<= lo hi)
                      t)))
  :hints (("Goal" :induct (find-minimal1 lo hi min))))

; The hint above is necessary because the proof splits into two cases: min=nil
; and (integerp min).  The second case is immediate by type reasoning.  But the
; system won't open up (find-minimal1 lo hi nil) unless told to.

; The ``trick'' to this proof is to introduce the notion that min is a lower
; bound on (fmla x) over lo <= x <= hi:

(defun below-all (min lo hi)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hi)) (ifix lo)))))
  (cond
   ((not (and (integerp lo)
              (integerp hi)))
    t)
   ((> lo hi) t)
   ((<= min (fmla lo))
    (below-all min (+ 1 lo) hi))
   (t nil)))

(defthm below-all-find-minimal1
  (implies (and (integerp lo)
                (integerp hi)
                (or (null xxx) (integerp xxx)))
           (below-all (find-minimal1 lo hi xxx) lo hi)))

; Now prove that below-all is a universal quantifier: If (below-all min lo hi)
; holds and lo <= x <= hi, min <= (fmla x).

(defthm below-all-is-a-universal-quantifier
  (implies (and (integerp lo)
                (integerp hi)
                (integerp x)
                (<= lo x)
                (<= x hi)
                (below-all min lo hi))
           (<= min (fmla x))))

(defthm find-minimal-correct
  (implies (and (integerp lo)
                (integerp hi)
                (integerp x)
                (<= lo x)
                (<= x hi))
           (and (integerp (find-minimal lo hi))
                (<= (find-minimal lo hi) (fmla x))))
  :rule-classes nil)






