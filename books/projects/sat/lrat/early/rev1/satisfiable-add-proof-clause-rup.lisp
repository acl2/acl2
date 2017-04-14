; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

(include-book "satisfiable-add-proof-clause-base")

(defthm evaluate-formula-fal-extra-cons
  (implies (< i1 i2)
           (equal (evaluate-formula-fal i1
                                        (cons (cons i2 clause)
                                              fal)
                                        assignment)
                  (evaluate-formula-fal i1 fal assignment))))

(defthm evaluate-formula-fal-t-monotone
  (implies (and (integerp index)
                (integerp max)
                (equal (evaluate-formula-fal max fal assignment)
                       t)
                (<= index max))
           (equal (evaluate-formula-fal index fal assignment)
                  t)))

(defthm natp-formula-fal-max
  (implies (force (formula-fal-p fal))
           (natp (formula-fal-max fal)))
  :rule-classes :type-prescription)

(defthm formula-fal-max-is-max
  (implies (and (< (formula-fal-max fal) index)
                (hons-assoc-equal index fal))
           (equal (cdr (hons-assoc-equal index fal))
                  *deleted-clause*)))

(defthm evaluate-formula-fal-large-index
  (implies (and (force (formula-fal-p fal))
                (integerp index)
                (< (formula-fal-max fal) index))
           (equal (evaluate-formula-fal index fal assignment)
                  (evaluate-formula-fal (formula-fal-max fal) fal assignment))))

(defthm satisfiable-add-proof-clause-rup-1-1-1
  (implies (and (equal (evaluate-clause clause assignment)
                       t)
                (natp max)
                (formula-fal-p fal)
                (clause-or-assignment-p assignment)
                (equal (evaluate-formula-fal max fal assignment)
                       t)
                (<= (formula-fal-max fal) max)
                (< (formula-fal-max fal) index))
           (equal (evaluate-formula-fal index
                                        (cons (cons index clause)
                                              fal)
                                        assignment)
                  t))
  :hints (("Goal"
           :expand ((evaluate-formula-fal index
                                          (cons (cons index clause) fal)
                                          assignment))
           :do-not-induct t)))

(defthm satisfiable-add-proof-clause-rup-1-1
  (implies (and (equal (evaluate-clause clause assignment)
                       t)
                (formula-p formula)
                (clause-or-assignment-p assignment)
                (equal (evaluate-formula formula assignment)
                       t)
                (< (formula-max formula) index))
           (equal (evaluate-formula (cons index
                                          (cons (cons index clause)
                                                (formula-fal formula)))
                                    assignment)
                  t))
  :hints (("Goal" :in-theory (enable formula-p evaluate-formula)))
  :rule-classes nil)

(defthm satisfiable-add-proof-clause-rup-1
  (let ((index (car index/clause))
        (clause (cdr index/clause)))
    (implies (and (equal (unit-propagation formula
                                           rup-indices
                                           (negate-clause-or-assignment clause))
                         t)
                  (consp index/clause)
                  (clause-or-assignment-p clause)
                  (index-listp rup-indices)
                  (formula-p formula)
                  (clause-or-assignment-p assignment)
                  (equal (evaluate-formula formula assignment)
                         t)
                  (< (formula-max formula) index))
             (equal (evaluate-formula (cons index
                                            (cons index/clause
                                                  (formula-fal formula)))
                                      assignment)
                    t)))
  :hints (("Goal" :use ((:instance satisfiable-add-proof-clause-rup-1-1
                                   (index (car index/clause))
                                   (clause (cdr index/clause)))))))

(defthm satisfiable-add-proof-clause-rup
  (implies (and (proof-entry-p entry)
                (formula-p formula)
                (satisfiable formula)
                (equal (unit-propagation formula
                                         (access add-step entry :rup-indices)
                                         (negate-clause-or-assignment
                                          (access add-step entry :clause)))
                       t)
                (< (formula-max formula)
                   (access add-step entry :index)))
           (satisfiable (add-proof-clause
                         (access add-step entry :index)
                         (access add-step entry :clause)
                         formula)))
  :hints (("Goal"
           :expand ((satisfiable formula))
           :restrict ((satisfiable-suff
                       ((assignment (satisfiable-witness formula)))))))
  :rule-classes nil)
