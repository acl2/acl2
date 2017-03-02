; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "LRAT")

(include-book "lrat-checker")
(include-book "truth-monotone")

; Start proof of subsetp-equal-cons.

(defthm subsetp-equal-cons-lemma
  (implies (subsetp-equal x y)
           (subsetp-equal x (cons a y))))

(defthm subsetp-equal-reflexive
  (subsetp-equal x x))

(defthm subsetp-equal-cons
  (subsetp-equal x (cons a x)))

(defthm cons-preserves-evaluate-formula
  (implies (formula-truep formula a)
           (formula-truep formula (cons x a)))
  :hints (("Goal"
           :use ((:instance truth-monotone
                            (a1 a)
                            (a2 (cons x a))))
           :in-theory (disable truth-monotone))))

(defthm clause-or-assignment-p-cons-is-unit-clause
  (implies (and (clause-or-assignment-p a1)
                (clause-or-assignment-p clause)
                (is-unit-clause clause a1)
                (not (equal (is-unit-clause clause a1)
                            t)))
           (clause-or-assignment-p
            (cons (is-unit-clause clause a1)
                  a1)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm formula-truep-implies-evaluate-clause-t
  (implies
   (and (formula-truep formula assignment)
        (hons-assoc-equal index formula)
        (not (deleted-clause-p (cdr (hons-assoc-equal index formula)))))
   (equal (evaluate-clause (cdr (hons-assoc-equal index formula))
                           assignment)
          t))
  :hints (("Goal" :use formula-truep-necc)))

(defthm evaluate-clause-t-implies-not-is-unit-clause
  (implies (and (clause-or-assignment-p clause)
                (equal (evaluate-clause clause assignment)
                       t))
           (not (is-unit-clause clause assignment))))

(defthm formula-truep-implies-not-is-unit-clause
  (implies (and (hons-assoc-equal index
                                  formula)
                (not (equal (cdr (hons-assoc-equal index formula))
                            *deleted-clause*))
                (formula-p formula)
                (formula-truep formula assignment))
           (not (is-unit-clause (cdr (hons-assoc-equal index formula))
                                assignment)))
  :hints (("Goal" :use formula-truep-necc)))

(defthm unit-propagation-identity
  (implies (and (formula-truep formula assignment)
                (formula-p formula))
           (equal (unit-propagation formula indices assignment)
                  assignment)))

(defthm unit-propagation-implies-unsat
  (implies (and (clause-or-assignment-p assignment)
                (formula-p formula)
                (formula-truep formula assignment)
                (index-listp indices))
           (not (equal (unit-propagation formula indices assignment)
                       t))))
