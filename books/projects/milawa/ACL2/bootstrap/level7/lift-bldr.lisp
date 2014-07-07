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
(include-book "lift")
(include-book "casesplit-bldr")
(%interactive)

(%autoadmit clause.lift-term1-bldr)

(%autoprove lemma-for-forcing-logic.appealp-of-clause.lift-term1-bldr
            (%clause.lift-term1-induction x)
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules
                      logic.termp-when-logic.formulap)
            (%auto)
            (%restrict default clause.lift-term1-bldr (equal x 'x))
            (%restrict default clause.lift-term1 (equal x 'x)))

(%autoprove forcing-logic.appealp-of-clause.lift-term1-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.lift-term1-bldr))))

(%autoprove forcing-logic.conclusion-of-clause.lift-term1-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.lift-term1-bldr))))

(%autoprove forcing-logic.proofp-of-clause.lift-term1-bldr
            (%clause.lift-term1-induction x)
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules
                      logic.termp-when-logic.formulap)
            (%auto)
            (%restrict default clause.lift-term1-bldr (equal x 'x))
            (%restrict default clause.lift-term1 (equal x 'x)))



(%autoadmit clause.lift-term-bldr)

(defthmd clause.lift-term-when-clause.lifted-termp
  (implies (clause.lifted-termp x)
           (equal (clause.lift-term x)
                  x))
  :hints(("Goal" :in-theory (enable clause.lift-term))))

(%autoprove clause.lift-term-when-clause.lifted-termp
            (%restrict default clause.lift-term (equal x 'x)))

(local (%enable default clause.lift-term-when-clause.lifted-termp))

(%autoprove lemma-for-forcing-logic.appealp-of-clause.lift-term-bldr
            (%clause.lift-term-induction x)
            (%auto)
            (%restrict default clause.lift-term-bldr (equal x 'x))
            (%restrict default clause.lift-term (equal x 'x)))

(%autoprove forcing-logic.appealp-of-clause.lift-term-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.lift-term-bldr))))

(%autoprove forcing-logic.conclusion-of-clause.lift-term-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.lift-term-bldr))))

(%autoprove forcing-logic.proofp-of-clause.lift-term-bldr
            (%clause.lift-term-induction x)
            (%auto)
            (%restrict default clause.lift-term-bldr (equal x 'x))
            (%restrict default clause.lift-term (equal x 'x)))


(%defprojection :list (clause.lift-term-list-bldr x)
                :element (clause.lift-term-bldr x))

(%autoprove forcing-logic.appeal-listp-of-clause.lift-term-list-bldr
            (%cdr-induction x))

(%autoprove forcing-logic.strip-conclusions-of-clause.lift-term-list-bldr
            (%cdr-induction x))

(%autoprove forcing-logic.proof-listp-of-clause.lift-term-list-bldr
            (%cdr-induction x))



(%autoadmit clause.lift-clauses-bldr)

(%autoprove forcing-logic.appeal-listp-of-clause.lift-clauses-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.lift-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-clause.lift-clauses-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.lift-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-clause.lift-clauses-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.lift-clauses-bldr (equal x 'x)))
