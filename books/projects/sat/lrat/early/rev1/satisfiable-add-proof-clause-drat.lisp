; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

(include-book "satisfiable-add-proof-clause-base")

; We include the following book at the top level, rather than locally to an
; encapsulate, because some of its lemmas other than the last one contribute to
; proofs in this book.
(include-book "sat-drat-claim-1")

(encapsulate
  ()
  (set-enforce-redundancy t)
  (defthm sat-drat-claim-1
    (implies (and (not (satisfiable (add-proof-clause index clause formula)))
                  (formula-p formula)
                  (solution-p assignment formula)
                  (clause-or-assignment-p clause)
                  (posp index)
                  (< (formula-max formula) index))
             (subsetp (negate-clause-or-assignment clause)
                      assignment))))

(encapsulate
  ()
  (local (include-book "sat-drat-claim-2"))
  (set-enforce-redundancy t)
  (defthm sat-drat-claim-2
    (implies (and (verify-clause formula
                                 (access add-step entry :clause)
                                 (access add-step entry :rup-indices)
                                 (access add-step entry :drat-hints))
                  (proof-entry-p entry)
                  (formula-p formula)
                  (solution-p assignment formula)
                  (not (equal (unit-propagation formula
                                                (access add-step entry
                                                        :rup-indices)
                                                (negate-clause-or-assignment
                                                 (access add-step entry
                                                         :clause)))
                              t))
                  (< (formula-max formula)
                     (access add-step entry :index))
                  (not (satisfiable (add-proof-clause
                                     (access add-step entry :index)
                                     (access add-step entry :clause)
                                     formula)))
                  (hons-assoc-equal index (formula-fal formula))
                  (not (equal (cdr (hons-assoc-equal index
                                                     (formula-fal formula)))
                              0)))
             (equal (evaluate-clause
                     (cdr (hons-assoc-equal index (formula-fal formula)))
                     (flip-literal (car (access add-step entry :clause))
                                   assignment))
                    t))
    :rule-classes nil))

(defthm sat-drat-claim-2-for-formula
  (implies (and (verify-clause formula
                               (access add-step entry :clause)
                               (access add-step entry :rup-indices)
                               (access add-step entry :drat-hints))
                (proof-entry-p entry)
                (formula-p formula)
                (solution-p assignment formula)
                (not (equal (unit-propagation formula
                                              (access add-step entry
                                                      :rup-indices)
                                              (negate-clause-or-assignment
                                               (access add-step entry
                                                       :clause)))
                            t))
                (< (formula-max formula)
                   (access add-step entry :index))
                (not (satisfiable (add-proof-clause
                                   (access add-step entry :index)
                                   (access add-step entry :clause)
                                   formula))))
           (equal (evaluate-formula
                   formula
                   (flip-literal (car (access add-step entry :clause))
                                 assignment))
                  t))
  :hints (("Goal"
           :in-theory
           (enable evaluate-formula-is-evaluate-clause-badguy)
           :use
           ((:instance sat-drat-claim-2
                       (index (find-unsat-index
                               (formula-max formula)
                               (formula-fal formula)
                               (flip-literal (car (access add-step entry
                                                          :clause))
                                             assignment)))))))
  :rule-classes nil)

(defthm sat-drat-key
  (implies (and (verify-clause formula
                               (access add-step entry :clause)
                               (access add-step entry :rup-indices)
                               (access add-step entry :drat-hints))
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
                (consp (access add-step entry :clause))
                (< (formula-max formula)
                   (access add-step entry :index)))
           (satisfiable (add-proof-clause
                         (access add-step entry :index)
                         (access add-step entry :clause)
                         formula)))
  :hints (("Goal"
           :restrict
           ((evaluate-formula-add-proof-clause
             ((lit (cadr (car entry)))))
            (satisfiable-suff
             ((assignment (flip-literal (cadr (car entry)) assignment)))))
           :use sat-drat-claim-2-for-formula)))

(defthm satisfiable-add-proof-clause-drat
   (implies (and (verify-clause formula
                                (access add-step entry :clause)
                                (access add-step entry :rup-indices)
                                (access add-step entry :drat-hints))
                 (proof-entry-p entry)
                 (not (proof-entry-deletion-p entry))
                 (formula-p formula)
                 (satisfiable formula)
                 (not (equal (unit-propagation formula
                                               (access add-step entry
                                                       :rup-indices)
                                               (negate-clause-or-assignment
                                                (access add-step entry
                                                        :clause)))
                             t))
                 (consp (access add-step entry :clause))
                 (< (formula-max formula)
                    (access add-step entry :index)))
            (satisfiable (add-proof-clause
                          (access add-step entry :index)
                          (access add-step entry :clause)
                          formula)))
   :hints (("Goal"
            :in-theory (union-theories '(sat-drat-key)
                                       (theory 'minimal-theory))
            :expand ((satisfiable formula))))
   :rule-classes nil)
