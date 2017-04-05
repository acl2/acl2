; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "LRAT")

(include-book "incremental")

; Start proof of satisfiability-preserved-when-incl-valid-proofp$

(local (in-theory (enable formula-max-var-is-formula-max-var-1-forced
                          proof-max-var-is-proof-max-var-1)))

(encapsulate
  ()
  (local (include-book "soundness-main-1"))
  (set-enforce-redundancy t)
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
       (incl-verify-proof$-rec ncls ndel formula proof a$))))))

(encapsulate
  ()

; We want to prove satisfiable-shrink-formula below.  Aha, we have such a
; theorem already, except it's for maybe-shrink-formula instead of
; shrink-formula.  Let's take advantage of that.

  (local (include-book "../list-based/satisfiable-maybe-shrink-formula"))

  (defthmd satisfiable-maybe-shrink-formula
    (implies
     (formula-p formula)
     (equal (satisfiable (mv-nth 2 (maybe-shrink-formula
                                    ncls ndel formula factor)))
            (satisfiable formula))))

  (defthm satisfiable-shrink-formula
    (implies (formula-p formula)
             (equal (satisfiable (shrink-formula formula))
                    (satisfiable formula)))
    :hints (("Goal"
             :use ((:instance satisfiable-maybe-shrink-formula
                              (ndel 1) (factor 0) (ncls 0)))
             :in-theory (enable maybe-shrink-formula)))))

(defthm satisfiability-preserved-when-incl-valid-proofp$
  (implies (and (car (incl-valid-proofp$ formula proof max-var a$))
                (satisfiable formula)
                (formula-p formula)
                (a$p a$)
                (equal (a$ptr a$) 0)
                (integerp max-var)
                (<= (formula-max-var-1 formula)
                    max-var))
           (satisfiable
            (mv-nth 1
                    (incl-valid-proofp$ formula proof max-var a$)))))

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
        (<= (formula-max-var-1 formula) max-var)
        (integerp max-var)
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
        (<= (formula-max-var-1 formula) max-var)
        (equal (car (incl-valid-proofp$ formula proof max-var a$))
               :complete)
        (integerp max-var))
   (not (satisfiable formula)))
  :hints (("Goal"
           :use incl-valid-proofp$-complete-implies-not-satisfiable
           :in-theory (disable incl-valid-proofp$))))

; Ugh, here we need a version of formula-max-monotone-for-incl-valid-proofp$
; that is about formula-max-var-1.
(defthm formula-max-var-1-monotone-for-incl-valid-proofp$
  (implies (and (<= (formula-max-var-1 formula)
                    old-max-var)
                (natp old-max-var)
                (formula-p formula)
                (a$p a$)
                (equal (a$ptr a$) 0)
                (car (incl-valid-proofp$ formula proof old-max-var a$)))
           (<= (formula-max-var-1
                (mv-nth
                 1
                 (incl-valid-proofp$ formula proof old-max-var a$)))
               (mv-nth
                2
                (incl-valid-proofp$ formula proof old-max-var a$))))
  :hints (("Goal"
           :use
           formula-max-monotone-for-incl-valid-proofp$
           :in-theory
           (disable formula-max-monotone-for-incl-valid-proofp$))))

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

