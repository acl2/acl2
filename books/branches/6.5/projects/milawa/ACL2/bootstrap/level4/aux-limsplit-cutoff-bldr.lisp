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
(include-book "clause-basics")
(%interactive)



(%autoadmit clause.aux-limsplit-cutoff-bldr)

(%autoprove clause.aux-limsplit-cutoff-bldr-under-iff
            (%autoinduct clause.aux-limsplit-cutoff-bldr)
            (%restrict default clause.aux-limsplit-cutoff-bldr (equal as 'as)))

(%autoprove forcing-logic.appealp-of-clause.aux-limsplit-cutoff-bldr
            (%autoinduct clause.aux-limsplit-cutoff-bldr)
            (%restrict default clause.aux-limsplit-cutoff-bldr (equal as 'as)))

(%autoprove lemma-for-forcing-logic.conclusion-of-clause.aux-limsplit-cutoff-bldr
            (%cdr-induction a)
            (%forcingp nil))

(%autoprove forcing-logic.conclusion-of-clause.aux-limsplit-cutoff-bldr
            (%autoinduct clause.aux-limsplit-cutoff-bldr)
            (%restrict default clause.aux-limsplit-cutoff-bldr (equal as 'as))
            (%enable default lemma-for-forcing-logic.conclusion-of-clause.aux-limsplit-cutoff-bldr)
            (%disable default ;; these seem to be causing loops
                      forcing-logic.vlhs-of-logic.disjoin-formulas-free
                      forcing-logic.vrhs-of-logic.disjoin-formulas-free)
            (%auto :strategy (cleanup split urewrite crewrite dist)) ;; suppress elim
            (%enable default ;; that's weird.  i seem to need them now.
                     forcing-logic.vlhs-of-logic.disjoin-formulas-free
                     forcing-logic.vrhs-of-logic.disjoin-formulas-free))

(%autoprove forcing-logic.proofp-of-clause.aux-limsplit-cutoff-bldr
            (%autoinduct clause.aux-limsplit-cutoff-bldr)
            (%restrict default clause.aux-limsplit-cutoff-bldr (equal as 'as)))




(%autoadmit clause.limsplit-cutoff-bldr)

(%autoprove forcing-logic.appealp-of-clause.limsplit-cutoff-bldr
            (%enable default
                     clause.limsplit-cutoff-bldr
                     build.rev-disjunction))

(%autoprove forcing-logic.conclusion-of-clause.limsplit-cutoff-bldr
            (%enable default
                     clause.limsplit-cutoff-bldr
                     build.rev-disjunction))

(%autoprove forcing-logic.proofp-of-clause.limsplit-cutoff-bldr
            (%enable default
                     clause.limsplit-cutoff-bldr
                     build.rev-disjunction))




(%autoadmit clause.aux-split-goal)

(%autoprove clause.aux-split-goal-when-not-consp-of-todo
            (%enable default clause.aux-split-goal))



(%autoadmit clause.limsplit-cutoff-bldr-nice)

(%autoprove forcing-logic.appealp-of-clause.limsplit-cutoff-bldr-nice
            (%enable default clause.limsplit-cutoff-bldr-nice))

(%autoprove forcing-logic.conclusion-of-clause.limsplit-cutoff-bldr-nice
            (%enable default
                     clause.limsplit-cutoff-bldr-nice
                     clause.aux-split-goal))

(%autoprove forcing-logic.proofp-of-clause.limsplit-cutoff-bldr-nice
            (%enable default clause.limsplit-cutoff-bldr-nice))






(%autoadmit clause.limsplit-cutoff-bldr-nice-okp)

(%autoadmit clause.limsplit-cutoff-bldr-nice-high)

(encapsulate
 ()
 (local (%enable default
                 clause.limsplit-cutoff-bldr-nice-okp
                 clause.limsplit-cutoff-bldr-nice-high))

 (%autoprove booleanp-of-clause.limsplit-cutoff-bldr-nice-okp)

 (%autoprove clause.limsplit-cutoff-bldr-nice-okp-of-logic.appeal-identity)

 (%autoprove lemma-1-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp)

 (%autoprove lemma-2-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp)

 (%autoprove forcing-soundness-of-clause.limsplit-cutoff-bldr-nice-okp
             (%enable default
                      lemma-1-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp
                      lemma-2-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp)
             (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                              (x (clause.limsplit-cutoff-bldr-nice (first (logic.extras x))
                                                                   (second (logic.extras x))
                                                                   (logic.provable-witness (logic.conclusion (first (logic.subproofs x)))
                                                                                           axioms thms atbl)))))))


