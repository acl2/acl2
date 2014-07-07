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
(include-book "casesplit")
(%interactive)


(%autoprove cdr-of-logic.smart-negate-formulas)

(%autoprove car-of-logic.smart-negate-formulas
            (%forcingp nil))

(%autoadmit clause.cases-bldr)


(defthm lemma-for-forcing-logic.appealp-of-clause.cases-bldr-alt
  ;; BOZO the real lemma needs :rule-classes nil added
  (implies (and (logic.termp a)
                (logic.term-listp cases)
                (logic.term-listp (domain assignment)))
           (and (logic.appealp (clause.cases-bldr a cases assignment))
                (equal (logic.conclusion (clause.cases-bldr a cases assignment))
                       (if (consp assignment)
                           (logic.por (logic.disjoin-formulas (logic.smart-negate-formulas (assignment-formulas assignment)))
                                      (logic.pequal a (clause.casesplit a cases assignment)))
                         (logic.pequal a (clause.casesplit a cases assignment))))))
  :rule-classes nil)


(%autoprove lemma-for-forcing-logic.appealp-of-clause.cases-bldr-alt
            (%clause.cases-induction cases assignment)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      expensive-term/formula-inference
                      type-set-like-rules
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free)
            (%auto :strategy (cleanup split))
            (%restrict default clause.cases-bldr (equal cases 'cases))
            (%restrict default clause.casesplit (equal cases 'cases)))

(%autoprove forcing-logic.appealp-of-clause.cases-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.cases-bldr-alt))))

(%autoprove forcing-logic.conclusion-of-clause.cases-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.cases-bldr-alt))))



(%autoprove forcing-proofp-of-clause.cases-bldr
            (%clause.cases-induction cases assignment)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      expensive-term/formula-inference
                      type-set-like-rules
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free)
            (%auto :strategy (cleanup split))
            (%restrict default clause.cases-bldr (equal cases 'cases))
            (%restrict default clause.casesplit (equal cases 'cases)))
