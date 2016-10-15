; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Ben Selfridge was looking for a way to prove two stobjs equal, after having
; proved that their respective fields are equal; see
; stobj-equality-from-fields.lisp for a way to do that.  But in his case, at
; least one of the fields was an array, and what he actually proved was that
; the two array fields agreed at every index.  Here we show how to derive the
; equality of two lists from their equality at every index.  There are probably
; many books that automate this sort of "pick-a-point strategy", but here we
; proceed very directly using an old "badguy" trick that I think I first
; learned from Ken Kunen in the early 1990s, give or take.

; First introduce two lists, along with axioms that they are true lists of the
; same length. (Aside: one would typically have this if the two lists were
; corresponding fields of two stobjs satisfying the same stobj recognizer).

(in-package "ACL2")

(defstub f1 (x) t)
(defstub f2 (x) t)
(defaxiom len-f2-f1
  (equal (len (f2 x))
         (len (f1 x))))
(defaxiom true-listp-f1
  (true-listp (f1 x))
  :rule-classes :type-prescription)
(defaxiom true-listp-f2
  (true-listp (f2 x))
  :rule-classes :type-prescription)

; Also suppose we have proved that for every index in range, the two lists have
; the same element at that index.

(defaxiom nth-i-f2-f1
  (implies (and (natp i)
                (< i (len (f1 x))))
           (equal (nth i (f2 x))
                  (nth i (f1 x)))))

; Now we eliminate the hypothesis that i is in range, to get a better rewrite
; rule.

(defthm nth-i-out-of-range
  (implies (and (natp i)
                (not (< i (len x))))
           (equal (nth i x)
                  nil)))

(defthm nth-i-f2-f1-better
  (implies (natp i)
           (equal (nth i (f2 x))
                  (nth i (f1 x))))
  :hints (("Goal" :cases ((< i (len (f1 x)))))))

; We no longer need the original rewrite rule.
(in-theory (disable nth-i-f2-f1)) ; optional

(local
 (defun badguy (x y)

; Find the least index i, if any, such that (nth i x) does not equal (nth i y).
; Note that (badguy x y) is always a natural number.

   (cond ((or (endp x) (endp y))
          0) ; don't care
         ((equal (car x) (car y))
          (1+ (badguy (cdr x) (cdr y))))
         (t 0))))

; Now we reduce the question of equality of two lists to equality at their
; "badguy" index.  (Aside: you might see some similarity here to the sort of
; axiom introduced by defchoose or defun-sk.)

(local
 (defthm badguy-is-correct
   (implies (and (equal (len x) (len y))
                 (true-listp x)
                 (true-listp y))
            (equal (equal x y)
                   (let ((i (badguy x y)))
                     (equal (nth i x)
                            (nth i y)))))))

; The proof of our desired list equality is now fully automatic, using the
; badguy correctness lemma just above.

(defthm f1-equals-f2
  (equal (f1 x) (f2 x)))
