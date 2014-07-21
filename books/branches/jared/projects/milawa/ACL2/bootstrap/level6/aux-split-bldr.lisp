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
(include-book "aux-split-double-negate")
(include-book "aux-split-negated-if")
(include-book "aux-split-positive-if")
(include-book "aux-split-negative-default")
(include-book "aux-split-positive-default")
(%interactive)


(local (%disable default
                 type-set-like-rules
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 expensive-term/formula-inference
                 expensive-subsetp-rules
                 unusual-consp-rules))

(%autoadmit clause.aux-split-bldr)

(%autoprove lemma-for-forcing-logic.appealp-of-clause.aux-split-bldr
            (%autoinduct clause.aux-split)
            (%enable default clause.aux-split-goal-when-not-consp-of-todo)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default clause.aux-split-bldr (equal todo 'todo))
            (%restrict default clause.aux-split (equal todo 'todo))
            (%restrict default clause.split-count-list (equal x 'todo))
            (%auto :strategy (cleanup split urewrite crewrite)))

(%autoprove forcing-logic.appealp-of-clause.aux-split-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.aux-split-bldr))))

(%autoprove lemma-for-forcing-logic.proofp-of-clause.aux-split-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.aux-split-bldr))))

(local (%max-proof-size 800000000))

(%autoprove forcing-logic.proofp-of-clause.aux-split-bldr
            (%autoinduct clause.aux-split)
            (%enable default
                     clause.aux-split-goal-when-not-consp-of-todo
                     lemma-for-forcing-logic.proofp-of-clause.aux-split-bldr)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default clause.split-count-list (equal x 'todo))
            (%restrict default clause.aux-split-bldr (equal todo 'todo))
            (%restrict default clause.aux-split (equal todo 'todo))
            (%auto :strategy (cleanup split urewrite crewrite)))

(%autoprove forcing-logic.conclusion-of-clause.aux-split-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-clause.aux-split-bldr)))
            (%enable default clause.aux-split-goal))


