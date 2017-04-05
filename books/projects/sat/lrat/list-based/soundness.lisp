; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

(in-package "LRAT")

(include-book "lrat-checker")
(include-book "satisfiable-maybe-shrink-formula")

(defun extend-with-proof (ncls ndel formula proof)

; This function is essentially verify-proof, except that instead of returning a
; Boolean, it returns the extended formula.  And there is one other difference:
; We stop if/when we hit the empty clause in proof, since we want to prove that
; the empty clause gives us an unsat formula, but later steps might delete the
; empty clause!

  (cond
   ((atom proof) formula)
   (t
    (let* ((entry (car proof))
           (delete-flg (proof-entry-deletion-p entry)))
      (cond
       (delete-flg
        (let* ((indices (proof-entry-deletion-indices entry))
               (new-formula (delete-clauses indices formula))
               (len (length indices))
               (ncls

; We expect that (<= len ncls).  It is tempting to assert that here (with
; assert$), but it's not necessary so we avoid the overhead (mostly in proof,
; but perhaps also a bit in execution).

                (- ncls len))
               (ndel (+ ndel len)))
          (extend-with-proof ncls ndel new-formula (cdr proof))))
       (t ; addition
        (let ((clause (access add-step entry :clause)))
          (mv-let (ncls ndel formula)
            (verify-clause formula entry ncls ndel)
            (let* ((index (access add-step entry :index))
                   (new-formula (add-proof-clause index clause formula)))
              (if (null clause)
                  new-formula ; see comment above
                (extend-with-proof
                 (1+ ncls)
                 ndel
                 new-formula
                 (cdr proof))))))))))))

(defthm formula-p-delete-clauses
  (implies (and (formula-p fal)
                (index-listp index-list))
           (formula-p (delete-clauses index-list fal))))

(defthm formula-p-add-proof-clause
  (implies (and (posp index)
                (clause-or-assignment-p clause)
                (formula-p formula))
           (formula-p (add-proof-clause index clause formula))))

(encapsulate
  ()

  (local
   (defthm hons-assoc-equal-delete-clauses-member-equal-case
     (implies (equal (hons-assoc-equal index fal)
                     (cons index *deleted-clause*))
              (equal (hons-assoc-equal index (delete-clauses index-list fal))
                     (cons index *deleted-clause*)))))

  (local
   (defthm hons-assoc-equal-delete-clauses
     (equal (hons-assoc-equal index (delete-clauses index-list fal))
            (if (member-equal index index-list)
                (cons index *deleted-clause*)
              (hons-assoc-equal index fal)))))

  (local
   (defthm delete-clauses-preserves-formula-truep
     (implies (and (formula-p formula)
                   (clause-or-assignment-p assignment)
                   (formula-truep formula assignment))
              (formula-truep (delete-clauses index-list formula)
                             assignment))
     :hints (("Goal"
              :in-theory (disable formula-truep)
              :expand ((formula-truep (delete-clauses index-list formula)
                                      assignment))
              :restrict ((formula-truep-necc
                          ((index (formula-truep-witness
                                   (delete-clauses index-list formula)
                                   assignment)))))))))

  (defthm delete-clauses-preserves-satisfiable
    (implies (and (formula-p formula)
                  (satisfiable formula))
             (satisfiable (delete-clauses index-list formula)))
    :hints (("Goal"
             :in-theory (disable satisfiable formula-truep)
             :expand ((satisfiable formula))
             :restrict ((satisfiable-suff
                         ((assignment (satisfiable-witness formula)))))))))

(encapsulate
  ()
  (local (include-book "satisfiable-add-proof-clause"))

  (defthm satisfiable-add-proof-clause
    (mv-let (ncls ndel new-formula)
      (verify-clause formula entry ncls ndel)
      (declare (ignore ndel))
      (implies (and ncls
                    (proof-entry-p entry)
                    (not (proof-entry-deletion-p entry))
                    (formula-p formula)
                    (satisfiable formula))
               (satisfiable (add-proof-clause
                             (access add-step entry :index)
                             (access add-step entry :clause)
                             new-formula))))))

(in-theory (disable add-proof-clause verify-clause))

(defthm formula-truep-cons-shrink-formula
  (implies (and (formula-p formula)
                (clause-or-assignment-p assignment)
                (formula-truep (cons pair (shrink-formula formula))
                               assignment))
           (formula-truep (cons pair formula)
                          assignment))
  :hints (("Goal"
           :expand ((formula-truep (cons pair formula)
                                   assignment))
           :restrict ((formula-truep-necc
                       ((index (formula-truep-witness (cons pair formula)
                                                      assignment))))))))

(defthm satisfiable-cons-shrink-formula
  (implies (formula-p formula)
           (implies (satisfiable (cons pair (shrink-formula formula)))
                    (satisfiable (cons pair formula))))
  :hints (("Goal"
           :expand ((satisfiable (cons pair (shrink-formula formula))))
           :restrict
           ((satisfiable-suff
             ((assignment
               (satisfiable-witness (cons pair
                                          (shrink-formula formula))))))))))

(encapsulate
  ()

  (local
   (defthm not-satisfiable-add-proof-clause-nil
     (implies (and (formula-p formula)
                   (posp index))
              (not (satisfiable (add-proof-clause index nil formula))))
     :hints (("Goal"
              :in-theory (enable add-proof-clause satisfiable)
              :restrict ((formula-truep-necc ((index index))))))
     :rule-classes nil))

  (defthm verify-clause-implies-unsatisfiable
    (implies (and (formula-p formula)
                  (proof-entry-p entry)
                  (equal (access add-step entry :clause) nil)
                  (satisfiable formula))
             (not (car (verify-clause formula entry ncls ndel))))
    :hints (("Goal"
             :in-theory (enable verify-clause add-proof-clause
                                maybe-shrink-formula)
             :use ((:instance not-satisfiable-add-proof-clause-nil
                              (index (access add-step entry :index)))
                   (:instance satisfiable-add-proof-clause
                              (entry (change add-step entry
                                             :clause nil))))))))

(defthm formula-p-mv-nth-2-verify-clause
  (implies (formula-p formula)
           (formula-p (mv-nth 2
                              (verify-clause formula entry ncls ndel))))
  :hints (("Goal" :in-theory (enable verify-clause maybe-shrink-formula))))

(defthm extend-with-proof-preserves-satisfiable
  (implies (and (formula-p formula)
                (proofp proof)
                (verify-proof-rec ncls ndel formula proof)
                (satisfiable formula))
           (satisfiable (extend-with-proof ncls ndel formula proof)))
  :rule-classes nil)

(defthm not-formula-truep-add-nil-clause
  (not (formula-truep (cons (list (car (car (car proof))))
                            fal)
                      assignment))
  :hints (("Goal" :restrict ((formula-truep-necc
                              ((index (car (car (car proof))))))))))

(defthm proof-contradiction-p-implies-false
  (implies (and (formula-p formula)
                (proofp proof)
                (proof-contradiction-p proof))
           (equal (formula-truep (extend-with-proof ncls ndel formula proof)
                                 assignment)
                  nil))
  :hints (("Goal" :in-theory (enable verify-clause add-proof-clause
                                     maybe-shrink-formula))))

(defthm proof-contradiction-p-implies-not-satisfiable
  (implies (and (formula-p formula)
                (proofp proof)
                (proof-contradiction-p proof))
           (not (satisfiable (extend-with-proof ncls ndel formula proof))))
  :hints (("Goal" :in-theory (e/d (satisfiable) (extend-with-proof)))))

(defthm main-theorem-list-based
  (implies (and (formula-p formula)
                (refutation-p proof formula))
           (not (satisfiable formula)))
  :hints (("Goal" :use ((:instance extend-with-proof-preserves-satisfiable
                                   (ncls (len (fast-alist-fork formula nil)))
                                   (ndel 0))))))
