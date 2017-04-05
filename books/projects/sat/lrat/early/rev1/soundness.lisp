; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../../README.

(in-package "ACL2")

(include-book "lrat-checker")

(defun extend-with-proof (formula proof)

; This function is essentially verify-proof, except that instead of returning a
; Boolean, it returns the extended formula, and it avoids the checks.  And
; there is one other difference: We stop if/when we hit the empty clause in
; proof, since we want to prove that the empty clause gives us an unsat
; formula, but later steps might delete the empty clause!

  (declare (xargs :guard (and (formula-p formula)
                              (proofp proof))))
  (if (atom proof)
      formula
    (let* ((entry (car proof))
           (delete-flg (proof-entry-deletion-p entry)))
      (if delete-flg
          (let* ((indices (proof-entry-deletion-indices entry))
                 (new-formula (delete-clauses indices formula)))
            (extend-with-proof new-formula (cdr proof)))
        (let* ((clause (access add-step entry :clause))
               (index (access add-step entry :index))
               (index (if (and (posp index)
                               (< (formula-max formula) index))
                          index
                        (1+ (formula-max formula))))
               (new-formula (add-proof-clause index clause formula)))
          (if (null clause)
              new-formula ; see comment above
            (extend-with-proof new-formula (cdr proof))))))))

(defthm formula-fal-p-delete-clauses-fal
  (implies (formula-fal-p fal)
           (formula-fal-p (delete-clauses-fal index-list fal))))

(defthm formula-fal-max-delete-clauses-fal
  (implies (formula-fal-p fal)
           (equal (formula-fal-max (delete-clauses-fal index-list fal))
                  (formula-fal-max fal))))

(defthm formula-p-delete-clauses-fal
  (implies (formula-p formula)
           (formula-p
            (cons (formula-max formula)
                  (delete-clauses-fal index-list (formula-fal formula))))))

(defthm formula-p-add-proof-clause
  (implies (and (posp index)
                (clause-or-assignment-p clause)
                (formula-p formula)
                (< (formula-max formula) index))
           (formula-p (add-proof-clause index clause formula))))

(encapsulate
  ()

; Start proof of delete-clauses-fal-preserves-evaluate-formula-fal.

  (local
   (defthm hons-assoc-equal-delete-clauses-fal-member-equal-case
     (implies (equal (hons-assoc-equal index fal)
                     (cons index 0))
              (equal (hons-assoc-equal index (delete-clauses-fal index-list fal))
                     (cons index 0)))))

  (local
   (defthm hons-assoc-equal-delete-clauses-fal
     (equal (hons-assoc-equal index (delete-clauses-fal index-list fal))
            (if (member-equal index index-list)
                (cons index 0)
              (hons-assoc-equal index fal)))))

  (local
   (defthm delete-clauses-fal-preserves-evaluate-formula-fal
     (implies
      (and (formula-fal-p fal)
           (clause-or-assignment-p assignment)
           (equal (evaluate-formula-fal index fal assignment)
                  t))
      (equal (evaluate-formula-fal index
                                   (delete-clauses-fal index-list fal)
                                   assignment)
             t))
     :hints (("Goal"
              :induct (evaluate-formula-fal index fal assignment)
              :do-not-induct t
              :do-not '(generalize)))))

  (defthm delete-clauses-fal-preserves-satisfiable
    (implies (and (formula-p formula)
                  (satisfiable formula))
             (satisfiable (cons (formula-max formula)
                                (delete-clauses-fal index-list
                                                    (formula-fal formula)))))
    :hints (("Goal"
             :in-theory (disable satisfiable)
             :expand ((satisfiable formula))
             :restrict ((satisfiable-suff
                         ((assignment (satisfiable-witness formula)))))))))

(encapsulate
  ()

  (local (include-book "satisfiable-add-proof-clause"))

  (defthm satisfiable-add-proof-clause
    (implies (and (verify-clause formula
                                 (access add-step entry :clause)
                                 (access add-step entry :rup-indices)
                                 (access add-step entry :drat-hints))
                  (proof-entry-p entry)
                  (not (proof-entry-deletion-p entry))
                  (formula-p formula)
                  (satisfiable formula)
                  (< (formula-max formula)
                     (access add-step entry :index)))
             (satisfiable (add-proof-clause
                           (access add-step entry :index)
                           (access add-step entry :clause)
                           formula)))))

(in-theory (disable satisfiable add-proof-clause formula-p verify-clause))

(defthm formula-p-implies-natp-formula-max
  (implies (formula-p formula)
           (natp (formula-max formula)))
  :hints (("Goal" :in-theory (enable formula-p)))
  :rule-classes :forward-chaining)

(encapsulate
  ()

  (local
   (defthm not-satisfiable-add-proof-clause-nil
     (implies (and (formula-p formula)
                   (posp index)
                   (< (formula-max formula) index))
              (not (satisfiable (add-proof-clause index nil formula))))
     :hints (("Goal" :in-theory (enable add-proof-clause satisfiable)))
     :rule-classes nil))

  (defthm verify-clause-implies-unsatisfiable
    (implies (and (formula-p formula)
                  (proof-entry-p entry)
                  (satisfiable formula)
                  (not (eq (car entry) t))
                  (< (formula-max formula)
                     (access add-step entry :index)))
             (not (verify-clause formula
                                 nil
                                 (access add-step entry :rup-indices)
                                 (access add-step entry :drat-hints))))
    :hints (("Goal" :use ((:instance not-satisfiable-add-proof-clause-nil
                                     (index (access add-step entry :index)))
                          (:instance satisfiable-add-proof-clause
                                     (entry (change add-step entry
                                                    :clause nil))))))))

(defthm extend-with-proof-preserves-satisfiable
  (implies (and (formula-p formula)
                (proofp proof)
                (verify-proof formula proof)
                (satisfiable formula))
           (satisfiable (extend-with-proof formula proof))))

(defthm main-lemma
  (implies (and (formula-p formula)
                (proofp proof)
                (verify-proof formula proof)
                (satisfiable formula))
           (satisfiable (extend-with-proof formula proof))))

(defthm proof-contradiction-p-implies-false-lemma
  (implies (posp index)
           (not (evaluate-formula-fal
                 (car (add-proof-clause index nil formula))
                 (cdr (add-proof-clause index nil formula))
                 assignment)))
  :hints (("Goal" :in-theory (enable add-proof-clause))))

(defthm proof-contradiction-p-implies-false
  (implies (and (formula-p formula)
                (proofp proof)
                (proof-contradiction-p proof))
           (equal (evaluate-formula (extend-with-proof formula proof)
                                    assignment)
                  nil)))

(defthm proof-contradiction-p-implies-not-satisfiable
  (implies (and (formula-p formula)
                (proofp proof)
                (proof-contradiction-p proof))
           (not (satisfiable (extend-with-proof formula proof))))
  :hints (("Goal" :in-theory (e/d (satisfiable) (extend-with-proof)))))

(defthm main-theorem
  (implies (and (formula-p formula)
                (refutation-p proof formula))
           (not (satisfiable formula))))
