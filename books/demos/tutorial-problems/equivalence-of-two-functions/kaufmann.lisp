; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann, February 25, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; I posted essentially this solution to the acl2-help list on 2/10/2014, with
; explanation essentially as below added in a follow-up email to that list on
; 2/16/2014.

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

; Goal: prove that (sum2 n n) equals (sum1 n).

; This didn't seem to me like an inductively-provable fact, I guess because in
; the inductive step, (sum2 n n) generates the term (sum2 (- n 1) n), which
; isn't an instance of (sum2 n n).  So I tried to think of how to express (sum2
; i j) in terms of sum1, where i and j aren't necessarily equal.

; Well, reading the definition, I can see that (sum2 i j) adds the numbers from
; (j - i) up to j, at least if i <= j.  That's the same as adding all the
; numbers from 0 to j, and then subtracting the numbers from 0 to (j - i - 1).
; That observation is realized in the next lemma.

(defthm sum2-as-sum1
  (implies (and (natp i) (natp j) (<= i j))
           (equal (sum2 i j)
                  (- (sum1 j) (sum1 (1- (- j i)))))))

(defthm main
  (equal (sum2 n n)
         (sum1 n)))
