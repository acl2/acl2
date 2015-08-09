; Copyright (C) 2013, ForrestHunt, Inc.
; Written by J Strother Moore, December 19, 2012
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Toy: Finding the Maximal Value of a Function over an Integer Interval

; To recertify:
; (certify-book "find-maximal-1d")

; Abstract: Suppose you have an integer-valued function, FMLA, of one integer
; argument, x, and you wish to find the maximal value of (FMLA x) as x ranges
; over a given interval lo <= x <= hi.  See find-minimal-1d.lisp for the
; original development.

(in-package "ACL2")

(encapsulate ((fmla (x) t))
             (local (defun fmla (x) (* x x)))
             (defthm integerp-fmla
               (implies (integerp x)
                        (integerp (fmla x)))
               :rule-classes :type-prescription))

(defun find-maximal1 (lo hi max)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hi)) (ifix lo)))))
  (cond
   ((not (and (integerp lo)
              (integerp hi)))
    max)
   ((> lo hi) max)
   (t (find-maximal1
       (+ 1 lo) hi
       (if (or (null max)
               (> (fmla lo) max))
           (fmla lo)
           max)))))

(defun find-maximal (lo hi)
  (find-maximal1 lo hi nil))

(defthm find-maximal1-increases
  (implies max
           (>= (find-maximal1 lo hi max) max))
  :rule-classes :linear)

(defthm integerp-find-maximal1
  (implies (and (integerp lo)
                (integerp hi)
                (or (null max) (integerp max)))
           (equal (integerp (find-maximal1 lo hi max))
                  (if (null max)
                      (<= lo hi)
                      t)))
  :hints (("Goal" :induct (find-maximal1 lo hi max))))

(defun above-all (max lo hi)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hi)) (ifix lo)))))
  (cond
   ((not (and (integerp lo)
              (integerp hi)))
    t)
   ((> lo hi) t)
   ((>= max (fmla lo))
    (above-all max (+ 1 lo) hi))
   (t nil)))

(defthm above-all-find-maximal1
  (implies (and (integerp lo)
                (integerp hi)
                (or (null xxx) (integerp xxx)))
           (above-all (find-maximal1 lo hi xxx) lo hi)))

(defthm above-all-is-a-universal-quantifier
  (implies (and (integerp lo)
                (integerp hi)
                (integerp x)
                (<= lo x)
                (<= x hi)
                (above-all max lo hi))
           (>= max (fmla x))))

(defthm find-maximal-correct
  (implies (and (integerp lo)
                (integerp hi)
                (integerp x)
                (<= lo x)
                (<= x hi))
           (and (integerp (find-maximal lo hi))
                (>= (find-maximal lo hi) (fmla x))))
  :rule-classes nil)






