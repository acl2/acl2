; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

(in-package "LRAT")

(include-book "incremental")

(skip-proofs
(defthm satisfiability-preserved-when-incl-valid-proofp$
  (implies (and (car (incl-valid-proofp$ formula proof max-var a$))
                (satisfiable formula)
                (formula-p formula)
                (a$p a$)
                (equal (a$ptr a$) 0)
                (integerp max-var)
                (<= (formula-max-var formula 0)
                    max-var))
           (satisfiable
            (mv-nth 1
                    (incl-valid-proofp$ formula proof max-var a$)))))
)

(defthm not-satisfiable-add-proof-clause-nil
  (not (satisfiable (cons (cons index nil) formula)))
  :hints (("Goal"
           :in-theory (enable add-proof-clause satisfiable)
           :restrict ((formula-truep-necc ((index index)))))))

(defthm incl-verify-proofp$-rec-complete-implies-not-satisfiable
  (implies
   (and (proofp proof)
        (equal (car (incl-verify-proof$-rec ncls ndel formula proof a$))
               :complete))
   (not
    (satisfiable
     (mv-nth
      1
      (incl-verify-proof$-rec ncls ndel formula proof a$)))))
  :hints (("Goal"
           :induct t
           :in-theory (disable delete-clauses verify-clause$))))

(defthmd incl-valid-proofp$-complete-implies-not-satisfiable
  (implies
   (and (formula-p formula)
        (a$p a$)
        (equal (a$ptr a$) 0)
        (integerp max-var)
        (<= (formula-max-var formula 0) max-var)
        (equal (car (incl-valid-proofp$ formula proof max-var a$))
               :complete))
   (not (satisfiable
         (mv-nth 1
                 (incl-valid-proofp$ formula proof max-var a$))))))

(defthm soundness-incl-valid-proofp$
  (implies
   (and (formula-p formula)
        (a$p a$)
        (equal (a$ptr a$) 0)
        (integerp max-var)
        (<= (formula-max-var formula 0) max-var)
        (equal (car (incl-valid-proofp$ formula proof max-var a$))
               :complete))
   (not (satisfiable formula)))
  :hints (("Goal"
           :use incl-valid-proofp$-complete-implies-not-satisfiable
           :in-theory (disable incl-valid-proofp$))))

(defthm soundness-main
  (implies
   (and (equal (car (incl-valid-proofp$-top-rec formula
                                                clrat-file posn chunk-size
                                                clrat-file-length
                                                old-suffix debug max-var a$ ctx
                                                state))
               :complete)
        (formula-p formula)
        (a$p a$)
        (equal (a$ptr a$) 0)
        (integerp max-var)
        (<= (formula-max-var formula 0) max-var))
   (not (satisfiable formula)))
  :hints (("Goal"
           :in-theory (disable incl-valid-proofp$ clrat-read-next a$ptr)
           :induct t)))

