; Proof of correctness of get-hyps-and-conc
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "get-hyps-and-conc")
(include-book "kestrel/evaluators/if-and-implies-eval" :dir :system)
(local (include-book "get-conjuncts-proofs"))

;; just changes the evaluator
(local
  (defthm all-eval-to-true-with-if-and-implies-eval-of-get-conjuncts
    (iff (all-eval-to-true-with-if-and-implies-eval (get-conjuncts term) a)
         (if-and-implies-eval term a))
    :hints (("Goal" :use (:functional-instance all-eval-to-true-with-if-eval-of-get-conjuncts
                                               (if-eval if-and-implies-eval)
                                               (if-eval-list if-and-implies-eval-list)
                                               (all-eval-to-true-with-if-eval all-eval-to-true-with-if-and-implies-eval))))))

;; Putting the hyps and conclusion back together into an IMPLIES gives a term
;; equivalent to TERM.
(defthm get-hyps-and-conc-correct
  (iff (if-and-implies-eval `(implies ,(conjoin (mv-nth 0 (get-hyps-and-conc term)))
                                      ,(mv-nth 1 (get-hyps-and-conc term)))
                            a)
       (if-and-implies-eval term a))
  :hints (("Goal" :in-theory (enable get-hyps-and-conc))))
