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
(include-book "elim") ;; bozo for strip-conclusions-of-restn, etc.
(%interactive)



(%autoadmit tactic.crewrite-first-okp)

(%autoprove booleanp-of-tactic.crewrite-first-okp
            (%enable default tactic.crewrite-first-okp))


(%autoadmit tactic.crewrite-first-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.crewrite-first-tac
            (%enable default tactic.crewrite-first-tac))

(%autoprove forcing-tactic.crewrite-first-okp-of-tactic.crewrite-first-tac
            (%enable default
                     tactic.crewrite-first-tac
                     tactic.crewrite-first-okp))


(%autoadmit tactic.crewrite-first-compile)

(local (%enable default
                tactic.crewrite-first-okp
                tactic.crewrite-first-compile))

(%autoprove forcing-logic.appeal-listp-of-tactic.crewrite-first-compile
            (%auto :strategy (cleanup split urewrite))
            (%generalize (car (cdr (tactic.skeleton->extras x))) plan)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%enable default dangerous-decomposition-of-app)
            (%auto))

(%autoprove forcing-logic.strip-conclusions-of-tactic.crewrite-first-compile
            (%auto :strategy (cleanup split urewrite))
            (%generalize (car (cdr (tactic.skeleton->extras x))) plan)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%enable default dangerous-decomposition-of-app)
            (%auto))

(%autoprove forcing-logic.proof-listp-of-tactic.crewrite-first-compile
            (%disable default
                      unusual-memberp-rules
                      memberp-when-not-consp
                      MEMBERP-WHEN-MEMBERP-OF-CDR)
            (%auto)
            (%generalize (car (cdr (tactic.skeleton->extras x))) plan)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto)

            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CDR (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X)))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (RW.CREWRITE-CLAUSE-PLAN->FORCED-GOALS PLAN))))))
            (%auto)

            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS2)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CDR (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X)))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (RW.CREWRITE-CLAUSE-PLAN->FORCED-GOALS PLAN))))))
            (%auto))


(%ensure-exactly-these-rules-are-missing "../../tactics/crewrite-first")
