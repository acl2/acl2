; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

(include-book "lrat-checker")

(defthm member-equal-monotone
  (implies (and (subsetp-equal s1 s2)
                (member-equal a s1))
           (member-equal a s2)))

(defthm truth-monotone-clause
  (implies (and (subsetp-equal a1 a2)
                (equal (evaluate-clause clause a1) t))
           (equal (evaluate-clause clause a2) t)))

(defthm truth-monotone-formula-fal
  (implies (and (subsetp-equal a1 a2)
                (equal (evaluate-formula-fal max fal a1) t))
           (equal (evaluate-formula-fal max fal a2) t)))

(defthm truth-monotone
  (implies (and (subsetp-equal a1 a2)
                (equal (evaluate-formula formula a1) t))
           (equal (evaluate-formula formula a2) t)))
