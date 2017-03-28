; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we collect key lemmas in support of satisfiable-add-proof-clause.lisp,
; which in turn proves the main lemma for soundness.lisp.  See
; lrat-checker.lisp for the actual checker.

(in-package "ACL2")

(include-book "lrat-checker")
(include-book "truth-monotone")
(include-book "unit-propagation-implies-unsat")
(include-book "unit-propagation-monotone")
(include-book "unit-propagation-correct")

; The first four events below are redundant.

(defthm truth-monotone
  (implies (and (subsetp-equal a1 a2)
                (equal (formula-truep formula a1) t))
           (equal (formula-truep formula a2) t)))

(defthm unit-propagation-implies-unsat
  (implies (and (clause-or-assignment-p assignment)
                (formula-p formula)
                (formula-truep formula assignment)
                (index-listp indices))
           (not (equal (unit-propagation formula indices assignment)
                       t))))

(defthm unit-propagation-monotone
  (implies (and (equal (unit-propagation formula indices a1)
                       t)
                (clause-or-assignment-p a1)
                (clause-or-assignment-p a2)
                (subsetp-equal a1 a2)
                (formula-p formula))
           (equal (unit-propagation formula indices a2)
                  t)))

(defthm unit-propagation-correct
  (implies (and (formula-p formula)
                (clause-or-assignment-p clause)
                (clause-or-assignment-p assignment)
                (formula-truep formula assignment)
                (equal (unit-propagation formula
                                         indices
                                         (negate-clause-or-assignment clause))
                       t))
           (equal (evaluate-clause clause assignment)
                  t)))

(in-theory (disable formula-p))

; The following events were needed in satisfiable-add-proof-clause-drat.lisp.
; The defthms, in particular, were developed for the proof of sat-drat-key.

(defund flip-literal (lit assignment)

; This function was originally called modify-solution, but with the parameters
; reversed.

  (cons lit
        (remove-literal lit
                        (remove-literal (negate lit)
                                        assignment))))

(defthm member-remove-literal
  (iff (member lit1 (remove-literal lit2 x))
       (if (equal lit1 lit2)
           nil
         (member lit1 x))))

(defthm clause-or-assignment-p-flip-literal
  (implies (and (clause-or-assignment-p assignment)
                (literalp lit))
           (clause-or-assignment-p (flip-literal lit assignment)))
  :hints (("Goal" :in-theory (enable flip-literal))))

(defthm member-flip-literal
  (member lit (flip-literal lit assignment))
  :hints (("Goal" :in-theory (enable flip-literal))))
