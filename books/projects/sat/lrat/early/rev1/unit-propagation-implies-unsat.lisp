; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

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

(local (in-theory (disable evaluate-formula)))

(defthm cons-preserves-evaluate-formula
  (implies (equal (evaluate-formula formula a) t)
           (equal (evaluate-formula formula (cons x a)) t))
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

(defthm evaluate-formula-fal-t-implies-evaluate-clause-t
  (implies (and (equal (evaluate-formula-fal max fal assignment)
                       t)
                (natp max)
                (posp index)
                (<= index max)
                (hons-assoc-equal index fal)
                (not (equal (cdr (hons-assoc-equal index fal))
                            0)))
           (equal (evaluate-clause (cdr (hons-assoc-equal index fal))
                                   assignment)
                  t)))

(defthm evaluate-clause-t-implies-not-is-unit-clause
  (implies (and (clause-or-assignment-p clause)
                (equal (evaluate-clause clause assignment)
                       t))
           (not (is-unit-clause clause assignment))))

; I encountered the need for hons-assoc-equal-implies-index-is-in-range, below,
; when trying to prove Claim 4 in sat-drat-claim-2-3.lisp (i.e., Claim 2.3.4 in
; a comment in satisfiable-add-proof-clause.lisp).  The following two lemmas
; help to eliminate some hypotheses, for example in
; evaluate-formula-t-implies-not-is-unit-clause.

(defthm hons-assoc-equal-fal-implies-index-is-in-range
  (implies (and (hons-assoc-equal index fal)
                (not (equal (cdr (hons-assoc-equal index fal))
                            *deleted-clause*))
                (formula-fal-p fal))
           (and (posp index)
                (<= index (formula-fal-max fal))))
  :rule-classes :forward-chaining)

(defthm hons-assoc-equal-formula-fal-implies-index-is-in-range
  (implies (and (hons-assoc-equal index (formula-fal formula))
                (not (equal (cdr (hons-assoc-equal index
                                                   (formula-fal formula)))
                            *deleted-clause*))
                (formula-p formula))
           (and (posp index)
                (<= index (formula-max formula))))
  :hints (("Goal"
           :in-theory (union-theories '(formula-p)
                                      (theory 'minimal-theory))
           :use ((:instance hons-assoc-equal-fal-implies-index-is-in-range
                            (fal (formula-fal formula))))))
  :rule-classes :forward-chaining)

(defthm evaluate-formula-fal-t-implies-not-is-unit-clause
  (implies (and (equal (evaluate-formula-fal max fal assignment)
                       t)
                (natp max)

; By hons-assoc-equal-fal-implies-index-is-in-range, we replace hypotheses of
; (posp index) and (<= index max) by the following.

                (<= (formula-fal-max fal) max)
                (hons-assoc-equal index fal)
                (not (equal (cdr (hons-assoc-equal index fal))
                            0))
                (formula-fal-p fal))
           (not (is-unit-clause (cdr (hons-assoc-equal index fal))
                                assignment))))

(defthm evaluate-formula-t-implies-not-is-unit-clause
  (implies (and (hons-assoc-equal index
                                  (formula-fal formula))
                (not (equal (cdr (hons-assoc-equal index
                                                   (formula-fal formula)))
                            0))
                (formula-p formula)
                (equal (evaluate-formula formula assignment)
                       t))
           (not (is-unit-clause (cdr (hons-assoc-equal index
                                                       (formula-fal formula)))
                                assignment)))
  :hints (("Goal" :in-theory (enable evaluate-formula))))

(defthm unit-propagation-identity
  (implies (and (equal (evaluate-formula formula assignment) t)
                (formula-p formula))
           (equal (unit-propagation formula indices assignment)
                  assignment)))
