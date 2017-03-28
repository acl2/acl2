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

(defthm truth-monotone
  (implies (and (subsetp-equal a1 a2)
                (equal (evaluate-formula formula a1) t))
           (equal (evaluate-formula formula a2) t)))

(defthm unit-propagation-implies-unsat
  (implies (and (clause-or-assignment-p assignment)
                (formula-p formula)
                (equal (evaluate-formula formula assignment) t)
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
                (equal (evaluate-formula formula assignment)
                       t)
                (equal (unit-propagation formula
                                         indices
                                         (negate-clause-or-assignment clause))
                       t))
           (equal (evaluate-clause clause assignment)
                  t)))

(in-theory (disable evaluate-formula formula-p satisfiable))

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

; The next events implement a pick-a-point ("badguy") strategy, first used in
; deriving sat-drat-claim-2-for-formula from sat-drat-claim-2 in
; satisfiable-add-proof-clause-drat.lisp.

(defun find-unsat-index (index fal assignment)

; This function, based on evaluate-formula-fal, returns an index i not
; exceeding the given index such that the ith clause in fal does not evaluate
; to t under assignment, if such i exists; else, nil.

  (if (zp index)
      nil
    (let ((pair (hons-get index fal)))
      (if (null pair)
          (find-unsat-index (1- index) fal assignment)
        (let ((clause (cdr pair)))
          (if (deleted-clause-p clause)
              (find-unsat-index (1- index) fal assignment)
            (let ((clause-value (evaluate-clause clause assignment)))
              (if (not (equal clause-value t))
                  index
                (find-unsat-index (1- index) fal assignment)))))))))

(defthmd find-unsat-index-is-badguy-1
  (equal (equal (evaluate-formula-fal index fal assignment)
                t)
         (not (find-unsat-index index fal assignment))))

(defthmd find-unsat-index-is-badguy-1-formula
  (equal (equal (evaluate-formula formula assignment)
                t)
         (not (find-unsat-index (formula-max formula)
                                (formula-fal formula)
                                assignment)))
  :hints (("Goal" :in-theory (enable evaluate-formula
                                     find-unsat-index-is-badguy-1))))

(defthmd find-unsat-index-is-badguy-2
  (let* ((i (find-unsat-index index fal assignment))
         (pair (hons-get i fal)))
    (implies i
             (and pair
                  (not (equal (evaluate-clause (cdr pair) assignment)
                              t))))))

(defthmd evaluate-formula-fal-is-evaluate-clause-badguy
  (equal (equal (evaluate-formula-fal index fal assignment)
                t)
         (not
          (let ((badguy (find-unsat-index index fal assignment)))
            (and badguy
                 (posp badguy)
                 (<= badguy index)
                 (hons-get badguy fal)
                 (not (equal (cdr (hons-get badguy fal))
                             0))
                 (not (equal (evaluate-clause
                              (cdr (hons-get badguy fal))
                              assignment)
                             t)))))))

(defthmd evaluate-formula-is-evaluate-clause-badguy
  (equal (equal (evaluate-formula formula assignment)
                t)
         (not
          (let ((badguy (find-unsat-index (formula-max formula)
                                          (formula-fal formula)
                                          assignment)))
            (and badguy
                 (posp badguy)
                 (<= badguy (formula-max formula))
                 (hons-get badguy (formula-fal formula))
                 (not (equal (cdr (hons-get badguy (formula-fal formula)))
                             0))
                 (not (equal (evaluate-clause
                              (cdr (hons-get badguy (formula-fal formula)))
                              assignment)
                             t))))))
  :hints (("Goal" :in-theory (enable evaluate-formula
                                     evaluate-formula-fal-is-evaluate-clause-badguy))))

(defthmd evaluate-formula-fal-is-evaluate-clause-badguy-alt
  (equal (equal (evaluate-formula-fal index fal assignment)
                t)
         (not (find-unsat-index index fal assignment))))

(defthmd evaluate-formula-is-evaluate-clause-badguy-alt
  (equal (equal (evaluate-formula formula assignment)
                t)
         (not (find-unsat-index (formula-max formula)
                                (formula-fal formula)
                                assignment)))
  :hints (("Goal"
           :in-theory
           (enable evaluate-formula
                   evaluate-formula-fal-is-evaluate-clause-badguy-alt))))
