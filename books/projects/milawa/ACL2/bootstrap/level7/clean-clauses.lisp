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
(include-book "absurd")
(include-book "normalize-nots")
(%interactive)


(%autoadmit disabled-equal)
(%autoadmit clause.clean-clauses)

(defsection clause.clean-clauses
  (local (%enable default clause.clean-clauses disabled-equal))
  (%autoprove booleanp-of-first-of-clause.clean-clauses)
  (%autoprove booleanp-of-second-of-clause.clean-clauses)
  (%autoprove logic.term-list-listp-of-third-of-clause.clean-clauses)
  (%autoprove logic.cons-listp-of-third-of-clause.clean-clauses)
  (%autoprove true-listp-of-third-of-clause.clean-clauses))

(%autoadmit clause.clean-clauses-bldr)

(%autoprove forcing-logic.appeal-listp-of-clause.clean-clauses-bldr
            (%enable default clause.clean-clauses-bldr clause.clean-clauses disabled-equal)
            (%disable default consp-when-memberp-of-cons-listp))

(%autoprove forcing-logic.strip-conclusions-of-clause.clean-clauses-bldr
            (%enable default clause.clean-clauses-bldr clause.clean-clauses disabled-equal)
            (%disable default consp-when-memberp-of-cons-listp))

(%autoprove forcing-logic.proof-listp-of-clause.clean-clauses-bldr
            (%enable default clause.clean-clauses-bldr clause.clean-clauses disabled-equal)
            (%disable default consp-when-memberp-of-cons-listp))



(%autoadmit clause.fast-clean-part1)

(%autoprove clause.fast-clean-part1-removal
            (%autoinduct clause.fast-clean-part1 x acc)
            (%restrict default clause.fast-clean-part1 (equal x 'x))
            (%enable default
                     clause.normalize-nots-term-list-of-rev
                     [outside]clause.normalize-nots-term-list-of-rev)
            (%disable default
                      rev-of-clause.normalize-nots-term-list
                      [outside]rev-of-clause.normalize-nots-term-list))


(%autoadmit clause.fast-clean-clauses)

(%autoprove clause.fast-clean-clauses-removal
            (%enable default
                     clause.fast-clean-clauses
                     clause.clean-clauses)
            (%enable default
                     clause.normalize-nots-clauses-of-rev
                     clause.remove-obvious-clauses-of-rev
                     clause.remove-complement-clauses-of-rev)
            (%disable default
                      rev-of-clause.normalize-nots-clauses
                      rev-of-clause.remove-obvious-clauses
                      rev-of-clause.remove-complement-clauses
                      [outside]rev-of-clause.normalize-nots-clauses
                      [outside]rev-of-clause.remove-obvious-clauses
                      [outside]rev-of-clause.remove-complement-clauses)
            (%disable default consp-when-memberp-of-cons-listp) ;; wtf?
            )



