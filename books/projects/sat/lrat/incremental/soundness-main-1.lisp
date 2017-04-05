; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "LRAT")

(include-book "incremental")

(defthm integerp-car-verify-clause$
  (implies (force (integerp ncls))
           (or (integerp (car (verify-clause$ formula proof-entry
                                              ncls ndel a$)))
               (equal (car (verify-clause$ formula proof-entry
                                           ncls ndel a$))
                      nil)))
  :rule-classes :type-prescription)

(defthm natp-mv-nth-1-verify-clause$
  (implies (and (force (integerp ncls))
                (force (natp ndel))
                (car (verify-clause$ formula proof-entry
                                     ncls ndel a$)))
           (natp (mv-nth 1 (verify-clause$ formula proof-entry
                                           ncls ndel a$))))
  :rule-classes :type-prescription)

(local (include-book "../stobj-based/equiv"))

(defthm a$ptr-0-for-verify-clause$-alt
  (implies (and (a$p a$)
                (equal (nth *a$ptr* a$) 0)
                (formula-p$ formula a$)
                (clausep$ (access add-step add-step :clause) a$)
                (car (verify-clause$ formula add-step ncls ndel a$)))
           (equal (car (mv-nth 3 (verify-clause$ formula add-step ncls ndel a$)))
                  0))
  :hints (("Goal"
           :use a$ptr-0-for-verify-clause$
           :in-theory (disable a$ptr-0-for-verify-clause$))))

(defthm a$p-mv-nth-3-verify-clause$-alt
  (implies (and (a$p a$)
                (formula-p$ formula a$)
                (clausep$ (access add-step add-step :clause) a$))
           (consp (mv-nth 3 (verify-clause$ formula add-step ncls ndel
                                            a$))))
  :hints (("Goal"
           :use a$p-mv-nth-3-verify-clause$
           :in-theory (e/d (a$p) (a$p-mv-nth-3-verify-clause$)))))

(encapsulate
  ()
  (local (include-book "../list-based/satisfiable-add-proof-clause"))

  (defthm satisfiable-add-proof-clause-alt
    (mv-let (ncls ndel new-formula)
      (verify-clause formula entry ncls ndel)
      (declare (ignore ndel))
      (implies (and ncls
                    (proof-entry-p entry)
                    (not (proof-entry-deletion-p entry))
                    (formula-p formula)
                    (satisfiable formula)
                    (equal clause (access add-step entry :clause)))
               (satisfiable (add-proof-clause
                             (access add-step entry :index)
                             clause
                             new-formula))))
    :hints (("Goal"
             :use satisfiable-add-proof-clause
             :in-theory (disable satisfiable-add-proof-clause)))))

(encapsulate
  ()
  (local (include-book "../list-based/soundness"))
  (defthm delete-clauses-preserves-satisfiable
    (implies (and (formula-p formula)
                  (satisfiable formula))
             (satisfiable (delete-clauses index-list formula)))))

(defthm satisfiability-preserved-by-incl-verify-proofp$-rec
  (implies
   (and (integerp ncls)
        (natp ndel)
        (proofp$ proof a$)
        (formula-p$ formula a$)
        (a$p a$)
        (consp a$)
        (equal (car a$) 0)
        (car (incl-verify-proof$-rec ncls ndel formula proof a$))
        (satisfiable formula))
   (satisfiable
    (mv-nth
     1
     (incl-verify-proof$-rec ncls ndel formula proof a$))))
  :hints (("Goal"
           :induct (incl-verify-proof$-rec ncls ndel formula proof a$)
           :in-theory
           (e/d ()
                (add-proof-clause verify-clause$ delete-clauses)))))
