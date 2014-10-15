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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(%autoadmit clause.casesplit)

(%autoprove clause.casesplit-when-not-consp
            (%restrict default clause.casesplit (equal cases 'cases)))

(%autoprove clause.casesplit-of-cons
            (%restrict default clause.casesplit (equal cases '(cons a cases))))

(defmacro %clause.cases-induction (cases assignment)
  `(%induct (rank ,cases)
            ((not (consp ,cases))
             nil)
            ((consp ,cases)
             (((,cases (cdr ,cases)) (,assignment (update (car ,cases) t ,assignment)))
              ((,cases (cdr ,cases)) (,assignment (update (car ,cases) nil ,assignment)))))))

(%autoprove forcing-logic.termp-of-clause.casesplit
            (%clause.cases-induction cases assignment))

(%autoprove forcing-logic.term-atblp-of-clause.casesplit
            (%clause.cases-induction cases assignment))



(%autoadmit clause.cases)

(%autoprove clause.cases-when-not-consp
            (%restrict default clause.cases (equal cases 'cases)))

(%autoprove clause.cases-of-cons
            (%restrict default clause.cases (equal cases '(cons a cases))))

(%autoprove consp-of-clause.cases
            (%clause.cases-induction cases assignment))

(%autoprove domain-of-clause.cases
            (%clause.cases-induction cases baseassign))

(%autoprove clause.simple-term-listp-of-domain-of-clause.cases)

(%autoprove disjoint-from-nonep-of-domain-of-clause.cases)


(%ensure-exactly-these-rules-are-missing "../../clauses/if-lifting/casesplit")