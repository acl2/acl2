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
(%interactive)


(%autoadmit tactic.skeletonp)
(%autoadmit tactic.skeleton->goals)
(%autoadmit tactic.skeleton->tacname)
(%autoadmit tactic.skeleton->extras)
(%autoadmit tactic.skeleton->history)

(%autoprove booleanp-of-tactic.skeletonp
            (%autoinduct tactic.skeletonp)
            (%restrict default tactic.skeletonp (equal x 'x)))

(%autoprove forcing-logic.term-list-listp-of-tactic.skeleton->goals
            (%enable default tactic.skeleton->goals)
            (%restrict default tactic.skeletonp (equal x 'x)))

(%autoprove forcing-cons-listp-of-tactic.skeleton->goals
            (%enable default tactic.skeleton->goals)
            (%restrict default tactic.skeletonp (equal x 'x)))

(%autoprove forcing-true-listp-of-tactic.skeleton->goals
            (%enable default tactic.skeleton->goals)
            (%restrict default tactic.skeletonp (equal x 'x)))

(%autoprove forcing-symbolp-of-tactic.skeleton->tacname
            (%enable default tactic.skeleton->tacname)
            (%restrict default tactic.skeletonp (equal x 'x)))

(%autoprove forcing-tactic.skeletonp-of-tactic.skeleton->history
            (%enable default
                     tactic.skeleton->tacname
                     tactic.skeleton->history)
            (%restrict default tactic.skeletonp (equal x 'x)))

(%autoprove rank-of-tactic.skeleton->history-when-tactic.skeleton->tacname
            (%enable default
                     tactic.skeleton->tacname
                     tactic.skeleton->history)
            (%restrict default tactic.skeletonp (equal x 'x)))


(%autoadmit tactic.initial-skeleton)

(%autoprove tactic.skeleton->goals-of-tactic.initial-skeleton
            (%enable default
                     tactic.initial-skeleton
                     tactic.skeleton->goals))

(%autoprove tactic.skeleton->tacname-of-tactic.initial-skeleton
            (%enable default
                     tactic.initial-skeleton
                     tactic.skeleton->tacname))

(%autoprove forcing-tactic.skeletonp-of-tactic.initial.skeleton
            (%enable default tactic.initial-skeleton)
            (%restrict default tactic.skeletonp (equal x '(cons goals '(nil nil nil)))))

(%autoadmit tactic.extend-skeleton)

(%autoprove tactic.skeleton->goals-of-tactic.extend-skeleton
            (%enable default
                     tactic.extend-skeleton
                     tactic.skeleton->goals))

(%autoprove tactic.skeleton->tacname-of-tactic.extend-skeleton
            (%enable default
                     tactic.extend-skeleton
                     tactic.skeleton->tacname))

(%autoprove tactic.skeleton->extras-of-tactic.extend-skeleton
            (%enable default
                     tactic.extend-skeleton
                     tactic.skeleton->extras))

(%autoprove tactic.skeleton->history-of-tactic.extend-skeleton
            (%enable default
                     tactic.extend-skeleton
                     tactic.skeleton->history))

(%autoprove forcing-tactic.skeletonp-of-tactic.extend.skeleton
            (%enable default tactic.extend-skeleton)
            (%restrict default tactic.skeletonp
                       (equal x '(CONS GOALS
                                  (CONS TACNAME
                                        (CONS EXTRAS (CONS HISTORY 'NIL)))))))



(%autoadmit tactic.original-conclusions)

(%autoprove forcing-logic.term-list-listp-of-tactic.original-conclusion
            (%autoinduct tactic.original-conclusions)
            (%restrict default tactic.original-conclusions (equal x 'x)))

(%autoprove forcing-cons-listp-of-tactic.original-conclusion
            (%autoinduct tactic.original-conclusions)
            (%restrict default tactic.original-conclusions (equal x 'x)))

(%autoprove forcing-true-listp-of-tactic.original-conclusion
            (%autoinduct tactic.original-conclusions)
            (%restrict default tactic.original-conclusions (equal x 'x)))

(%autoprove tactic.original-conclusions-of-tactic.initial-skeleton
            (%restrict default tactic.original-conclusions
                       (equal x '(tactic.initial-skeleton goals))))

(%autoprove forcing-tactic.original-conclusions-of-tactic.extend-skeleton
            (%restrict default tactic.original-conclusions
                       (equal x '(tactic.extend-skeleton goals tacname extras history))))


(%autoadmit tactic.skeleton-atblp)

(%autoprove booleanp-of-tactic.skeleton-atbp
            ;; BOZO bad name
            (%autoinduct tactic.skeleton-atblp)
            (%restrict default tactic.skeleton-atblp (equal x 'x)))

(%autoprove forcing-logic.term-list-list-atblp-of-tactic.skeleton->goals
            (%autoinduct tactic.skeleton-atblp)
            (%restrict default tactic.skeleton-atblp (equal x 'x)))

(%autoprove forcing-tactic.skeleton-atblp-of-tactic.skeleton->history
            (%restrict default tactic.skeleton-atblp (equal x 'x)))

(%autoprove forcing-tactic.skeleton-atblp-of-tactic.initial.skeleton
            (%restrict default tactic.skeleton-atblp (equal x '(tactic.initial-skeleton goals))))

(%autoprove forcing-tactic.skeleton-atblp-of-tactic.extend.skeleton
            (%disable default
                      forcing-logic.term-list-list-atblp-of-tactic.skeleton->goals
                      forcing-tactic.skeleton-atblp-of-tactic.skeleton->history)
            (%restrict default tactic.skeleton-atblp
                       (equal x '(TACTIC.EXTEND-SKELETON GOALS TACNAME EXTRAS HISTORY))))

(%autoprove forcing-logic.term-list-list-atblp-of-tactic.original-conclusion
            (%autoinduct tactic.original-conclusions)
            (%restrict default tactic.original-conclusions
                       (equal x 'x)))



(%autoadmit tactic.skeleton->len)

(%autoprove natp-of-tactic.skeleton->len
            (%autoinduct tactic.skeleton->len)
            (%restrict default tactic.skeleton->len (equal x 'x)))

(%autoprove tactic.skeleton->len-nonzero
            (%autoinduct tactic.skeleton->len)
            (%restrict default tactic.skeleton->len (equal x 'x)))

(%autoprove tactic.skeleton->len-when-not-tacname
            (%autoinduct tactic.skeleton->len)
            (%restrict default tactic.skeleton->len (equal x 'x)))



(%autoadmit logic.slow-term-list-list-arities)
(%autoadmit logic.term-list-list-arities)

(%autoprove true-listp-of-logic.term-list-list-arities
            (%autoinduct logic.term-list-list-arities x acc)
            (%restrict default logic.term-list-list-arities (equal x 'x)))

(%autoprove logic.term-list-list-arities-removal
            (%autoinduct logic.term-list-list-arities x acc)
            (%restrict default logic.term-list-list-arities (equal x 'x))
            (%restrict default logic.slow-term-list-list-arities (equal x 'x)))

(%autoprove logic.slow-term-list-list-arities-correct
            (%cdr-induction x)
            (%restrict default logic.term-list-list-atblp (equal x 'x))
            (%restrict default logic.slow-term-list-list-arities (equal x 'x)))


(%autoadmit tactic.slow-skeleton-arities)
(%autoadmit tactic.skeleton-arities)

(%autoprove true-listp-of-tactic.skeleton-arities
            (%autoinduct tactic.skeleton-arities x acc)
            (%restrict default tactic.skeleton-arities (equal x 'x)))

(%autoprove tactic.skeleton-arities-removal
            (%autoinduct tactic.skeleton-arities x acc)
            (%restrict default tactic.skeleton-arities (equal x 'x))
            (%restrict default tactic.slow-skeleton-arities (equal x 'x)))

(%autoprove logic.slow-skeleton-arities-correct
            (%autoinduct tactic.skeleton-atblp x atbl)
            (%restrict default tactic.slow-skeleton-arities (equal x 'x))
            (%restrict default tactic.skeleton-atblp (equal x 'x))
            (%disable default
                      forcing-tactic.skeleton-atblp-of-tactic.skeleton->history
                      forcing-logic.term-list-list-atblp-of-tactic.skeleton->goals))

(%autoadmit tactic.fast-skeleton-atblp)

(%autoprove tactic.fast-skeleton-atblp-correct
            (%enable default tactic.fast-skeleton-atblp))


(%ensure-exactly-these-rules-are-missing "../../tactics/skeletonp")
(%ensure-exactly-these-rules-are-missing "../../tactics/worldp")
(%ensure-exactly-these-rules-are-missing "../../tactics/urewrite-world")
(%ensure-exactly-these-rules-are-missing "../../tactics/crewrite-world")
(%ensure-exactly-these-rules-are-missing "../../tactics/colors")


