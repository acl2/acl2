; Soundness of irrelevance elimination
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We prove that eliminate-irrelevance-clause, the waterfall's irrelevance
;; elimination process, is sound: If the clause it returns is true, then so is
;; the clause it was given.  The proof is easy, since the clause returned is a
;; subset of the clause given, so it does not depend on how the irrelevant
;; literals are chosen.

(include-book "irrelevance-logic")
(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)

;; Clauses are built using IF (see disjoin) and NOT.
(defevaluator+ irrelevance-ev if not)

;; Removing literals from a false clause leaves a false clause.
(defthm all-eval-to-false-with-irrelevance-ev-of-set-difference-equal
  (implies (all-eval-to-false-with-irrelevance-ev cl a)
           (all-eval-to-false-with-irrelevance-ev (set-difference-equal cl lits) a))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

;; The main theorem: If eliminate-irrelevance-clause applies and the clause it
;; returns is true, then the clause it was given is true.
(defthm irrelevance-ev-when-eliminate-irrelevance-clause
  (implies (and (equal (mv-nth 0 (eliminate-irrelevance-clause cl hist pspv wrld state))
                       'hit)
                (irrelevance-ev (conjoin-clauses
                                 (mv-nth 1 (eliminate-irrelevance-clause cl hist pspv wrld state)))
                                a))
           (irrelevance-ev (disjoin cl) a))
  :hints (("Goal" :in-theory (e/d (eliminate-irrelevance-clause)
                                  (irrelevant-lits m&m)))))
