; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

(include-book "satisfiable-add-proof-clause-base")
(include-book "satisfiable-maybe-shrink-formula")

(defthm formula-truep-cons-forward
  (implies (and ; (formula-truep formula assignment)
            (consp pair)
            (not (equal (cdr pair) *deleted-clause*)))
           (implies
            (formula-truep (make-formula (cons pair (formula-fal formula)))
                           assignment)
            (equal (evaluate-clause (cdr pair) assignment)
                   t)))
  :hints (("Goal" :restrict ((formula-truep-necc
                              ((index (car pair)))))))
  :rule-classes nil)

(defthm formula-truep-cons-backward
  (implies (and (formula-truep formula assignment)
                (consp pair)
                (not (equal (cdr pair) *deleted-clause*)))
           (implies
            (equal (evaluate-clause (cdr pair) assignment)
                   t)
            (formula-truep (make-formula (cons pair (formula-fal formula)))
                           assignment)))
  :hints (("Goal"
           :expand ((formula-truep (cons pair formula)
                                   assignment))
           :restrict
           ((formula-truep-necc
             ((index (formula-truep-witness (cons pair formula)
                                            assignment)))))))
  :rule-classes nil)

(defthm formula-truep-cons
  (implies (and (formula-truep formula assignment)
                (consp pair)
                (not (equal (cdr pair) *deleted-clause*)))
           (equal
            (formula-truep (make-formula (cons pair (formula-fal formula)))
                           assignment)
            (equal (evaluate-clause (cdr pair) assignment)
                   t)))
  :hints (("Goal" :use (formula-truep-cons-forward
                        formula-truep-cons-backward))))

(defthm satisfiable-add-proof-clause-rup-basic
  (implies (and (proof-entry-p entry)
                (formula-p formula)
                (satisfiable formula)
                (equal (unit-propagation formula
                                         (access add-step entry :rup-indices)
                                         (negate-clause-or-assignment
                                          (access add-step entry :clause)))
                       t))
           (satisfiable (add-proof-clause
                         (access add-step entry :index)
                         (access add-step entry :clause)
                         formula)))
  :hints (("Goal"
           :expand ((satisfiable formula))
           :restrict ((satisfiable-suff
                       ((assignment (satisfiable-witness formula)))))))
  :rule-classes nil)

(defthm satisfiable-add-proof-clause-rup
  (mv-let (ncls ndel new-formula)
    (verify-clause formula
                   (access add-step entry :clause)
                   (access add-step entry :rup-indices)
                   (access add-step entry :drat-hints)
                   ncls
                   ndel)
    (declare (ignore ncls ndel))
    (implies (and (proof-entry-p entry)
                  (formula-p formula)
                  (satisfiable formula)
                  (equal (unit-propagation formula
                                           (access add-step entry :rup-indices)
                                           (negate-clause-or-assignment
                                            (access add-step entry :clause)))
                         t))
             (satisfiable (add-proof-clause
                           (access add-step entry :index)
                           (access add-step entry :clause)
                           new-formula))))
  :hints (("Goal"
           :in-theory (enable formula-p)
           :use satisfiable-add-proof-clause-rup-basic))
  :rule-classes nil)
