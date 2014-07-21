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
(include-book "skeletonp")
(%interactive)


(defthmd crock1-for-tactic.split-first-compile
  ;; BOZO unlocalize/rename
  (implies (and (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                       (logic.strip-conclusions proofs))
                (equal (firstn n goals) y))
           (equal (logic.strip-conclusions (firstn n proofs))
                  (logic.disjoin-each-formula-list (logic.term-list-list-formulas y))))
  :hints(("Goal"
          :in-theory (disable firstn-of-logic.disjoin-each-formula-list)
          :use ((:instance firstn-of-logic.disjoin-each-formula-list
                           (x (logic.term-list-list-formulas goals))
                           (y n))))))

(defthm crock2-for-tactic.split-first-compile
  ;; BOZO unlocalize/rename
  (implies (and (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                       (logic.strip-conclusions proofs))
                (equal (restn n goals) y))
           (equal (logic.strip-conclusions (restn n proofs))
                  (logic.disjoin-each-formula-list (logic.term-list-list-formulas y))))
  :hints(("Goal"
          :in-theory (disable restn-of-logic.disjoin-each-formula-list)
          :use ((:instance restn-of-logic.disjoin-each-formula-list
                           (x (logic.term-list-list-formulas goals))
                           (y n))))))



(%autoadmit tactic.split-first-okp)

(%autoprove booleanp-of-tactic.split-first-okp
            (%enable default tactic.split-first-okp))


(%autoadmit tactic.split-first-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.split-first-tac
            (%enable default tactic.split-first-tac))

(%autoprove forcing-tactic.split-first-okp-of-tactic.split-first-tac
            (%enable default tactic.split-first-tac tactic.split-first-okp))


(%autoadmit tactic.split-first-compile)

(encapsulate
 ()
 (local (%enable default
                 tactic.split-first-okp
                 tactic.split-first-compile))

 (%autoprove crock1-for-tactic.split-first-compile
             (%disable default
                       firstn-of-logic.disjoin-each-formula-list
                       [outside]firstn-of-logic.disjoin-each-formula-list)
             (%use (%instance (%thm firstn-of-logic.disjoin-each-formula-list)
                              (x (logic.term-list-list-formulas goals))
                              (y n))))

 (%autoprove crock2-for-tactic.split-first-compile
             (%disable default
                       restn-of-logic.disjoin-each-formula-list
                       [outside]restn-of-logic.disjoin-each-formula-list)
             (%use (%instance (%thm restn-of-logic.disjoin-each-formula-list)
                              (x (logic.term-list-list-formulas goals))
                              (y n))))

 (local (%enable default
                 crock1-for-tactic.split-first-compile
                 crock2-for-tactic.split-first-compile))

 (%autoprove forcing-logic.appeal-listp-of-tactic.split-first-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.split-first-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.split-first-compile))

(%ensure-exactly-these-rules-are-missing "../../tactics/split-first")
