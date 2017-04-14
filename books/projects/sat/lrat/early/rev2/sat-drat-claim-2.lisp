; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

(include-book "satisfiable-add-proof-clause-base")

(defthm truth-remove-irrelevant-lit-1
  (implies (and (equal (evaluate-clause clause assignment)
                       t)
                (not (member lit clause)))
           (equal (evaluate-clause clause
                                   (remove-literal lit assignment))
                  t)))

(defthm truth-remove-irrelevant-lit-cons
  (implies (and (equal (evaluate-clause clause assignment)
                       t)
                (not (member lit clause)))
           (equal (evaluate-clause clause
                                   (cons lit assignment))
                  t)))

(defthm truth-remove-irrelevant-lit-2
  (implies (and (equal (evaluate-clause clause assignment)
                       t)
                (not (member lit clause))
                (not (member (negate lit) clause)))
           (equal (evaluate-clause clause
                                   (flip-literal lit assignment))
                  t))
  :hints (("Goal" :in-theory (enable flip-literal))))

(defthm truth-remove-irrelevant-lit-3
  (implies (equal (evaluate-clause (remove-literal lit clause)
                                   assignment)
                  t)
           (equal (evaluate-clause clause assignment)
                  t)))

(defthm subsetp-preserves-assignment
  (implies (and (subsetp a2 a1)
                (clause-or-assignment-p a1)
                (literal-listp a2)
                (unique-literalsp a2))
           (clause-or-assignment-p a2))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm formula-truep-implies-evaluate-clause-t

; It remains to prove Claim 2.  Since A |= F, A |= D.

; This is redundant here (proved in unit-propagation-implies-unsat.lisp).

  (implies
   (and (formula-truep formula assignment)
        (hons-assoc-equal index (formula-fal formula))
        (not (equal (cdr (hons-assoc-equal index (formula-fal formula)))
                    *deleted-clause*)))
   (equal (evaluate-clause (cdr (hons-assoc-equal index (formula-fal formula)))
                           assignment)
          t)))

(defthm subsetp-cons-remove-literal
  (subsetp a (cons lit (remove-literal lit a))))

(defthm sat-drat-claim-2-1
  (implies (and (not (member (negate (car (access add-step entry :clause)))
                             (cdr (hons-assoc-equal index
                                                    (formula-fal formula)))))
                (formula-p formula)
                (solution-p assignment formula)
                (hons-assoc-equal index (formula-fal formula))
                (not (equal (cdr (hons-assoc-equal index
                                                   (formula-fal formula)))
                            *deleted-clause*)))
           (equal (evaluate-clause
                   (cdr (hons-assoc-equal index (formula-fal formula)))
                   (flip-literal (car (access add-step entry :clause))
                                 assignment))
                  t))
  :hints (("Goal"
           :in-theory (enable flip-literal)
           :restrict ((truth-monotone-clause
                       ((a1 (remove-literal (- (cadr (car entry)))
                                            assignment)))))))
  :rule-classes nil)

(defthm clause-or-assignmentp-cdr-hons-assoc-equal-for-formula
  (let ((clause (cdr (hons-assoc-equal index (formula-fal formula)))))
    (implies (and (formula-p formula)
                  (not (deleted-clause-p clause)))
             (clause-or-assignment-p clause)))
  :hints (("Goal" :in-theory (enable formula-p))))

(defthm sat-drat-claim-2-2-1
  (implies (and (member (negate (car (access add-step entry :clause)))
                        (cdr (hons-assoc-equal index
                                               (formula-fal formula))))
                (equal (evaluate-clause
                        (remove-literal
                         (negate (car (access add-step entry :clause)))
                         (cdr (hons-assoc-equal index (formula-fal formula))))
                        assignment)
                       t)
                (formula-p formula)
                (not (equal (cdr (hons-assoc-equal index
                                                   (formula-fal formula)))
                            *deleted-clause*)))
           (equal (evaluate-clause
                   (remove-literal
                    (negate (car (access add-step entry :clause)))
                    (cdr (hons-assoc-equal index (formula-fal formula))))
                   (flip-literal (car (access add-step entry :clause))
                                 assignment))
                  t))
  :instructions (:bash (:dv 1)
                       (:then (:rewrite truth-remove-irrelevant-lit-2)
                              :prove))
  :rule-classes nil)

(defthm sat-drat-claim-2-2
  (implies (and (member (negate (car (access add-step entry :clause)))
                        (cdr (hons-assoc-equal index
                                               (formula-fal formula))))
                (equal (evaluate-clause
                        (remove-literal
                         (negate (car (access add-step entry :clause)))
                         (cdr (hons-assoc-equal index (formula-fal formula))))
                        assignment)
                       t)
                (formula-p formula))
           (equal (evaluate-clause
                   (cdr (hons-assoc-equal index (formula-fal formula)))
                   (flip-literal (car (access add-step entry :clause))
                                 assignment))
                  t))
  :hints (("Goal" :use sat-drat-claim-2-2-1))
  :rule-classes nil)

(encapsulate
  ()
  (local (include-book "sat-drat-claim-2-3"))
  (set-enforce-redundancy t)
  (defthm sat-drat-claim-2-3
    (mv-let (ncls ndel new-formula)
      (verify-clause formula
                     (access add-step entry :clause)
                     (access add-step entry :rup-indices)
                     (access add-step entry :drat-hints)
                     ncls
                     ndel)
      (declare (ignore ndel))
      (implies (and (member (negate (car (access add-step entry :clause)))
                            (cdr (hons-assoc-equal index
                                                   (formula-fal formula))))
                    (not (equal (evaluate-clause
                                 (remove-literal
                                  (negate (car (access add-step entry :clause)))
                                  (cdr (hons-assoc-equal index (formula-fal formula))))
                                 assignment)
                                t))
                    ncls
                    (proof-entry-p entry)
                    (not (proof-entry-deletion-p entry))
                    (formula-p formula)
                    (solution-p assignment formula)
                    (not (equal (unit-propagation formula
                                                  (access add-step entry
                                                          :rup-indices)
                                                  (negate-clause-or-assignment
                                                   (access add-step entry
                                                           :clause)))
                                t))
                    (not (satisfiable (add-proof-clause
                                       (access add-step entry :index)
                                       (access add-step entry :clause)
                                       new-formula))))
               (equal (evaluate-clause
                       (cdr (hons-assoc-equal index (formula-fal formula)))
                       (flip-literal (car (access add-step entry :clause))
                                     assignment))
                      t)))
    :rule-classes nil))

(defthm sat-drat-claim-2
  (mv-let (ncls ndel new-formula)
    (verify-clause formula
                   (access add-step entry :clause)
                   (access add-step entry :rup-indices)
                   (access add-step entry :drat-hints)
                   ncls
                   ndel)
    (declare (ignore ndel))
    (implies (and ncls
                  (proof-entry-p entry)
                  (not (proof-entry-deletion-p entry))
                  (formula-p formula)
                  (solution-p assignment formula)
                  (not (equal (unit-propagation formula
                                                (access add-step entry
                                                        :rup-indices)
                                                (negate-clause-or-assignment
                                                 (access add-step entry
                                                         :clause)))
                              t))
                  (not (satisfiable (add-proof-clause
                                     (access add-step entry :index)
                                     (access add-step entry :clause)
                                     new-formula)))
                  (hons-assoc-equal index (formula-fal formula))
                  (not (equal (cdr (hons-assoc-equal index
                                                     (formula-fal formula)))
                              0)))
             (equal (evaluate-clause
                     (cdr (hons-assoc-equal index (formula-fal formula)))
                     (flip-literal (car (access add-step entry :clause))
                                   assignment))
                    t)))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :use (sat-drat-claim-2-1 sat-drat-claim-2-2 sat-drat-claim-2-3)))
  :rule-classes nil)
