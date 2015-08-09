; Copyright (C) 2014, Regents of the University of Texas
; Written by J Strother Moore, February 18, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; moore.lisp
; Equivalence of Two Simple Summation Functions

; This challenge came from Yan Peng: given the definitions of sum1 and sum2
; below, prove they are equal.

; The problem is slightly interesting because the two functions recur in very
; different ways, so a straightforward inductive proof is messy.  An easier
; proof is to prove that they are both correct in the sense that they return
; the well-known algebraic expression for the sum of the naturals below n,
; i.e., n*(n+1)/2.  This can be proved about sum1 and it can be proved about
; sum2 and the two proofs are not mixed in any way.  Then it is trivial to
; prove sum1 and sum2 are the same.

(in-package "ACL2")

(defun sum1 (n)
  (declare (xargs :measure (if (or (not (integerp n))
				   (<= n 0))
			     0
			     n)))
  (if (or (not (integerp n)) (<= n 0))
    0
    (+ n (sum1 (- n 1)))))

(defun sum2 (i n0)
  (declare (xargs :measure (if (or (not (integerp i))
				   (< i 0))
			     0
			     (+ 1 i))))
  (if (or (not (integerp i)) (< i 0))
    0
    (+ (- n0 i) (sum2 (- i 1) n0))))

(include-book "arithmetic-5/top" :dir :system)

; This theorem is obvious
(defthm sum1-correct
  (implies (natp n)
           (equal (sum1 n)
                  (/ (* n (+ n 1)) 2))))

; To prove anything about sum2 (by induction) it will be necessary to state a
; theorem in which the two actual parameters are distinct variables, e.g., we
; must focus on (sum2 i n0) not (sum2 i i).  This is standard with inductive
; proofs about functions that modify several arguments in recursion.

; Finding the generalized statement is sometimes hard but is often easier
; if one considers specific examples.

; (sum2 4 9)
; =  9+8+7+6+5
; = (9+8+7+6+5 +4+3+2+1) - (4+3+2+1)
; = (9*10)/2             - (4*5)/2

(defthm sum2-correct-gen
  (implies (and (natp i)
                (natp n0)
                (<= i n0))
           (equal (sum2 i n0)
                  (- (/ (* n0 (+ n0 1)) 2)
                     (/ (* (- (- n0 1) i) (- n0 i)) 2))))
  :hints (("Subgoal *1/2'''" :expand (sum2 0 n0))))

; Without the hint, Subgoal *1/2'' failed, but I saw it was easy if you
; expanded (sum2 0 n0).  So I added the hint.

; Once you know that the two are both algebraically correct, their
; equivalence is trivial.

(defthm sum1-is-sum2
  (implies (natp i)
           (equal (sum1 i) (sum2 i i)))
  :rule-classes nil)

; I would not make the above a :rewrite rule because I prefer to deal with
; (sum1 i) rather than (sum2 i i).  If I were dealing with sum2 routinely --
; because it was used for some reason in another function -- would swap the
; arguments to the equality above so as to rewrite (sum2 i i) to (sum1 i).

