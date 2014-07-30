; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "skeletonp")
(include-book "elim") ;; BOZO for strip-conclusions-of-restn
(%interactive)


(%autoadmit tactic.crewrite-all-okp)

(%autoprove booleanp-of-tactic.crewrite-all-okp
            (%enable default tactic.crewrite-all-okp))


(%autoadmit tactic.crewrite-all-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.crewrite-all-tac
            (%enable default tactic.crewrite-all-tac))

(%autoprove forcing-tactic.crewrite-all-okp-of-tactic.crewrite-all-tac
            (%enable default
                     tactic.crewrite-all-tac
                     tactic.crewrite-all-okp))

(%autoadmit tactic.crewrite-all-compile)

(local (%enable default
                tactic.crewrite-all-okp
                tactic.crewrite-all-compile))


(%autoprove forcing-logic.appeal-listp-of-tactic.crewrite-all-compile
            (%auto)
            (%generalize (car (cdr (tatic.skeleton->extras x))) plans)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))))))
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X)))))))))))

(%autoprove forcing-logic.strip-conclusions-of-tactic.crewrite-all-compile
            (%auto)
            (%generalize (car (cdr (tatic.skeleton->extras x))) plans)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))))))
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X)))))))))))

(%autoprove forcing-logic.proof-listp-of-tactic.crewrite-all-compile
            (%disable default
                      unusual-memberp-rules
                      memberp-when-not-consp
                      MEMBERP-WHEN-MEMBERP-OF-CDR)
            (%auto)
            (%generalize (car (cdr (tatic.skeleton->extras x))) plans)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))))))
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X)))))))))))

(%ensure-exactly-these-rules-are-missing "../../tactics/crewrite-all")