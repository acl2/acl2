; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

(in-package "LRAT")

(include-book "incremental")

(skip-proofs
(defthm a$p-mv-nth-4-incl-valid-proofp$
  (implies (and (a$p a$)
                (equal (a$ptr a$) 0)
                (formula-p formula)
                (natp max-var)
                (<= (formula-max-var formula 0)
                    old-max-var))
           (a$p (mv-nth 4
                        (incl-valid-proofp$
                         formula
                         proof
                         max-var a$)))))
)

(skip-proofs
(defthm soundness-incl-valid-proofp$
  (implies
   (and (formula-p formula)
        (posp clrat-file-length)
        (a$p a$)
        (integerp max-var)
        (natp posn)
        (<= (formula-max-var formula 0) max-var)
        (mv-nth 2
                (incl-valid-proofp$ formula proof max-var a$)))
   (not (satisfiable formula)))
  :hints (("Goal" :in-theory (disable incl-valid-proofp$ clrat-read-next))))
)

(skip-proofs
(defthm soundness-main
  (implies
   (and (equal (car (incl-valid-proofp$-top-rec formula
                                                clrat-file posn chunk-size
                                                clrat-file-length
                                                old-suffix debug max-var a$ ctx
                                                state))
               :complete)
        (formula-p formula)
        (posp clrat-file-length)
        (a$p a$)
        (equal (a$ptr a$) 0)
        (integerp max-var)
        (natp posn)
        (<= (formula-max-var formula 0) max-var))
   (not (satisfiable formula)))
  :hints (("Goal" :in-theory (disable incl-valid-proofp$ clrat-read-next))))
)

