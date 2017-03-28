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
                  (solution-p assignment formula)
                  (clause-or-assignment-p clause))
             (subsetp (negate-clause-or-assignment clause)
                      assignment))))

; The following might not be necessary, but it has perhaps been helpful during
; development of the events below.
(local (in-theory (disable verify-clause)))

(encapsulate
  ()
  (local (include-book "sat-drat-claim-2"))
  (set-enforce-redundancy t)
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
    :rule-classes nil))

(defthm sat-drat-claim-2-for-formula
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
                                     new-formula))))
             (formula-truep
              formula
              (flip-literal (car (access add-step entry :clause))
                            assignment))))
  :hints (("Goal"
           :in-theory
           (enable formula-truep)
           :use
           ((:instance sat-drat-claim-2
                       (index (formula-truep-witness
                               formula
                               (flip-literal (car (access add-step entry
                                                          :clause))
                                             assignment)))))))
  :rule-classes nil)

(include-book "satisfiable-maybe-shrink-formula")

(defthm sat-drat-key
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
                  (consp (access add-step entry :clause)))
             (satisfiable (add-proof-clause
                           (access add-step entry :index)
                           (access add-step entry :clause)
                           new-formula))))
  :hints (("Goal"
           :in-theory (enable verify-clause)
           :restrict
           ((formula-truep-add-proof-clause
             ((lit (cadr (car entry)))))
            (satisfiable-suff
             ((assignment (flip-literal (cadr (car entry)) assignment)))))
           :use sat-drat-claim-2-for-formula)))

(defthm satisfiable-add-proof-clause-drat
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
                  (satisfiable formula)
                  (not (equal (unit-propagation formula
                                                (access add-step entry
                                                        :rup-indices)
                                                (negate-clause-or-assignment
                                                 (access add-step entry
                                                         :clause)))
                              t))
                  (consp (access add-step entry :clause)))
             (satisfiable (add-proof-clause
                           (access add-step entry :index)
                           (access add-step entry :clause)
                           new-formula))))
  :hints
  (("Goal"
    :in-theory (union-theories '(sat-drat-key)
                               (theory 'minimal-theory))
    :expand ((satisfiable formula))
    :use ((:instance sat-drat-key
                     (assignment (satisfiable-witness formula))))))
  :rule-classes nil)
