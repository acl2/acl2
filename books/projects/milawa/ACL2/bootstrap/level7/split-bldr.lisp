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
(include-book "split")
(include-book "lift-bldr")
(include-book "limlift-bldr")
(%interactive)


(%autoadmit clause.split-bldr)

(%autoprove forcing-logic.appealp-of-clause.split-bldr
            (%enable default clause.split clause.split-bldr build.rev-disjunction))

(%autoprove forcing-logic.conclusion-of-clause.split-bldr
            (%enable default clause.split clause.split-bldr build.rev-disjunction))

(%autoprove forcing-logic.proofp-of-clause.split-bldr
            (%enable default clause.split clause.split-bldr build.rev-disjunction))


(%deflist logic.appeal-list-listp (x)
          (logic.appeal-listp x))

(%defprojection :list (logic.strip-conclusions-list x)
                :element (logic.strip-conclusions x))

(encapsulate
 ()
 (local (%disable default redefinition-of-clause.clause-list-formulas
                  [OUTSIDE]REDEFINITION-OF-CLAUSE.CLAUSE-LIST-FORMULAS))
 (%defprojection :list (clause.clause-list-list-formulas x)
                 :element (clause.clause-list-formulas x)))

(%deflist logic.proof-list-listp (x axioms thms atbl)
  (logic.proof-listp x axioms thms atbl))


(%autoadmit clause.split-list-bldr)

(%autoprove forcing-logic.appeal-listp-of-clause.split-list-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.split-list (equal x 'x))
            (%restrict default clause.split-list-bldr (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-clause.split-list-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.split-list (equal x 'x))
            (%restrict default clause.split-list-bldr (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-clause.split-list-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.split-list (equal x 'x))
            (%restrict default clause.split-list-bldr (equal x 'x))
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules
                      memberp-when-memberp-of-cdr))



(%autoadmit clause.split-bldr-okp)

(%autoadmit clause.split-bldr-high)

(encapsulate
 ()
 (local (%enable default clause.split-bldr-okp))
 (%autoprove booleanp-of-clause.split-bldr-okp)
 (%autoprove clause.split-bldr-okp-of-logic.appeal-identity)
 (%autoprove lemma-1-for-soundness-of-clause.split-bldr-okp)
 (%autoprove lemma-2-for-soundness-of-clause.split-bldr-okp)
 (%autoprove forcing-soundness-of-clause.split-bldr-okp
             (%enable default
                      lemma-1-for-soundness-of-clause.split-bldr-okp
                      lemma-2-for-soundness-of-clause.split-bldr-okp)
             (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                              (x (clause.split-bldr (first (logic.extras x))
                                                    (second (logic.extras x))
                                                    (third (logic.extras x))
                                                    (fourth (logic.extras x))
                                                    (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                                 axioms thms atbl)))))))
