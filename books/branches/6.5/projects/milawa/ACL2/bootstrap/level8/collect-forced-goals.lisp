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
(include-book "trace-okp")
(%interactive)


(defsection revappend-lemmas

  (local (%disable default forcing-revappend-removal))

  (%autoprove revappend-under-iff
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove consp-of-revappend
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove memberp-of-revappend
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove subsetp-of-revappend-one
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove subsetp-of-revappend-two
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove true-listp-of-revappend
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove logic.formula-listp-of-revappend
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove logic.formula-list-atblp-of-revappend
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x))))


(defsection fast-merge

  (%autoadmit fast-merge)

  (local (%enable default fast-merge))
  (local (%disable default forcing-revappend-removal))

  (%autoprove consp-of-fast-merge)
  (%autoprove true-listp-of-fast-merge)
  (%autoprove memberp-of-fast-merge)
  (%autoprove subsetp-of-fast-merge-one)

  (%autoprove subsetp-of-fast-merge-two
              (%disable default
                        subsetp-of-revappend-two
                        [outside]subsetp-of-revappend-two)
              (%use (%instance (%thm subsetp-of-revappend-two)
                               (x x)
                               (acc y)))
              (%restrict default revappend (equal x 'x)))

  (%autoprove logic.formula-listp-of-fast-merge)
  (%autoprove logic.formula-list-atblp-of-fast-merge)
  (%autoprove fast-merge-when-not-consp-left)
  (%autoprove fast-merge-with-nil-left)
  (%autoprove fast-merge-when-not-consp-right)
  (%autoprove fast-merge-with-nil-right))




(%autoadmit rw.flag-collect-forced-goals)

(%autoprove true-listp-of-rw.flag-collect-forced-goals
            (%autoinduct rw.flag-collect-forced-goals)
            (%restrict default rw.flag-collect-forced-goals (equal x 'x)))

(%autoadmit rw.collect-forced-goals)
(%autoadmit rw.collect-forced-goals-list)

(%autoprove definition-of-rw.collect-forced-goals
            (%enable default
                     rw.collect-forced-goals
                     rw.collect-forced-goals-list)
            (%restrict default rw.flag-collect-forced-goals (equal x 'x)))

(%autoprove definition-of-rw.collect-forced-goals-list
            (%enable default
                     rw.collect-forced-goals
                     rw.collect-forced-goals-list)
            (%restrict default rw.flag-collect-forced-goals (equal x 'x)))

(%autoprove rw.flag-collect-forced-goals-of-term
            (%enable default rw.collect-forced-goals))

(%autoprove rw.flag-collect-forced-goals-of-list
            (%enable default rw.collect-forced-goals-list))



(%autoprove rw.collect-forced-goals-list-when-not-consp
            (%restrict default definition-of-rw.collect-forced-goals-list (equal x 'x)))

(%autoprove rw.collect-forced-goals-list-of-cons
            (%restrict default definition-of-rw.collect-forced-goals-list (equal x '(cons a x))))








(%autoprove lemma-for-true-listp-of-rw.collect-forced-goals
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.collect-forced-goals (equal x 'x)))

(%autoprove true-listp-of-rw.collect-forced-goals
            (%use (%instance (%thm lemma-for-true-listp-of-rw.collect-forced-goals)
                             (flag 'term))))

(%autoprove true-listp-of-rw.collect-forced-goals-list
            (%use (%instance (%thm lemma-for-true-listp-of-rw.collect-forced-goals)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.formula-listp-of-rw.collect-forced-goals
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.collect-forced-goals (equal x 'x)))

(%autoprove forcing-logic.formula-listp-of-rw.collect-forced-goals
            (%use (%instance (%thm lemma-for-forcing-logic.formula-listp-of-rw.collect-forced-goals)
                             (flag 'term))))

(%autoprove forcing-logic.formula-listp-of-rw.collect-forced-goals-list
            (%use (%instance (%thm lemma-for-forcing-logic.formula-listp-of-rw.collect-forced-goals)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.formula-list-atblp-of-rw.collect-forced-goals
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.collect-forced-goals (equal x 'x)))

(%autoprove forcing-logic.formula-list-atblp-of-rw.collect-forced-goals
            (%use (%instance (%thm lemma-for-forcing-logic.formula-list-atblp-of-rw.collect-forced-goals)
                             (flag 'term))))

(%autoprove forcing-logic.formula-list-atblp-of-rw.collect-forced-goals-list
            (%use (%instance (%thm lemma-for-forcing-logic.formula-list-atblp-of-rw.collect-forced-goals)
                             (flag 'list))))





(%autoprove memberp-of-rw.trace-conclusion-formula-in-rw.collect-forced-goals
            (%restrict default definition-of-rw.collect-forced-goals (equal x 'x)))

(%autoprove forcing-subsetp-of-rw.collect-forced-goals-list-of-subtraces
            (%restrict default definition-of-rw.collect-forced-goals (equal x 'x))
            (%restrict default definition-of-rw.trace-okp (equal x 'x))
            (%enable default
                     rw.trace-step-okp
                     rw.force-tracep))






(%autoadmit rw.collect-forced-goals-list-list)

(%autoprove rw.collect-forced-goals-list-list-when-not-consp
            (%restrict default rw.collect-forced-goals-list-list (equal x 'x)))

(%autoprove rw.collect-forced-goals-list-list-of-cons
            (%restrict default rw.collect-forced-goals-list-list (equal x '(cons a x))))

(%autoprove true-listp-of-rw.collect-forced-goals-list-list
            (%cdr-induction x))

(%autoprove forcing-rw.formula-listp-of-rw.collect-forced-goals-list-list
            (%cdr-induction x))



(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/collect-forced-goals")