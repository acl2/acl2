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
(include-book "partition")
(include-book "skeletonp")
(%interactive)



;; BOZO all this stuff belongs somewhere else.

(%autoprove firstn-of-nfix
            (%autoinduct firstn))

(%autoprove restn-of-nfix
            (%autoinduct restn)
            (%restrict default restn (equal n 'n)))

(%autoprove cons-listp-of-list-list-fix
            ;; BOZO this was also autoproved in waterfall-steps.lisp, which caused a problem
            ;; during proof checking which seemed to have to do with one file overwriting
            ;; the other?  Now I'm just including this file in waterfall-steps.lisp to
            ;; avoid this.
            (%cdr-induction x))

(%autoprove true-list-listp-of-list-list-fix
            (%cdr-induction x))

(%autoprove logic.term-list-listp-of-list-list-fix
            (%cdr-induction x))

(%autoprove logic.term-list-list-atblp-of-list-list-fix
            (%cdr-induction x))

(%autoprove logic.strip-conclusions-list-of-partition
            (%autoinduct partition))

(%autoprove nat-listp-of-strip-lens-free)

(%autoprove logic.appeal-list-listp-of-partition
            (%autoinduct partition lens proofs))

(%autoprove true-list-listp-of-cdr-of-clause.split-list
            (%autoinduct clause.split-list))

(%autoprove list-list-fix-when-true-list-listp
            (%cdr-induction x))

(%autoprove clause.clause-list-list-formulas-of-partition
            (%autoinduct partition))

(%autoprove logic.proof-list-listp-of-partition
            (%autoinduct partition))



(%autoadmit tactic.split-all-okp)

(%autoprove booleanp-of-tactic.split-all-okp
            (%enable default tactic.split-all-okp))

(%autoprove forcing-cons-listp-of-simple-flatten
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-listp-of-simple-flatten
            (%cdr-induction x))


(%autoadmit tactic.split-all-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.split-all-tac
            (%enable default tactic.split-all-tac))

(%autoprove forcing-tactic.split-all-okp-of-tactic.split-all-tac
            (%enable default
                     tactic.split-all-tac
                     tactic.split-all-okp))



(encapsulate
 ()
 (%autoadmit tactic.split-all-compile)

 (local (%enable default tactic.split-all-okp tactic.split-all-compile))

 (%autoprove forcing-logic.appeal-listp-of-tactic.split-all-compile
             (%disable default
                       partition-of-simple-flatten
                       [outside]partition-of-simple-flatten)
             (%use (%instance
                    (%thm partition-of-simple-flatten)
                    (x (cdr (clause.split-list (first (tactic.skeleton->extras x))
                                               (second (tactic.skeleton->extras x))
                                               (third (tactic.skeleton->extras x))
                                               (list-list-fix (tactic.skeleton->goals (tactic.skeleton->history x)))))))))

 (%autoprove forcing-logic.strip-conclusions-of-tactic.split-all-compile
             (%disable default
                       partition-of-simple-flatten
                       [outside]partition-of-simple-flatten)
             (%use (%instance
                    (%thm partition-of-simple-flatten)
                    (x (cdr (clause.split-list (first (tactic.skeleton->extras x))
                                               (second (tactic.skeleton->extras x))
                                               (third (tactic.skeleton->extras x))
                                               (list-list-fix (tactic.skeleton->goals (tactic.skeleton->history x)))))))))

 (%autoprove forcing-logic.proof-listp-of-tactic.split-all-compile
             (%disable default
                       partition-of-simple-flatten
                       [outside]partition-of-simple-flatten)
             (%use (%instance
                    (%thm partition-of-simple-flatten)
                    (x (cdr (clause.split-list (first (tactic.skeleton->extras x))
                                               (second (tactic.skeleton->extras x))
                                               (third (tactic.skeleton->extras x))
                                               (list-list-fix (tactic.skeleton->goals (tactic.skeleton->history x)))))))))
 )

(%ensure-exactly-these-rules-are-missing "../../tactics/split-all")