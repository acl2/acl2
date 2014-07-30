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


(%autoadmit tactic.use-okp)

(%autoprove booleanp-of-tactic.use-okp
            (%enable default tactic.use-okp))

(%autoadmit tactic.use-env-okp)

(%autoprove booleanp-of-tactic.use-env-okp
            (%enable default tactic.use-env-okp))



(%autoadmit tactic.use-tac)
(%autoprove forcing-tactic.skeletonp-of-tactic.use-tac
            (%enable default tactic.use-tac))
(%autoprove forcing-tactic.use-okp-of-tactic.use-tac
            (%enable default tactic.use-tac tactic.use-okp))
(%autoprove forcing-tactic.use-env-okp-of-tactic.use-tac
            (%enable default tactic.use-tac tactic.use-env-okp))



(defthmd crock-1-for-tactic.use-compile
  ;; BOZO unlocalize/rename
  (implies (and (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (TACTIC.SKELETON->GOALS X)))
                       (LOGIC.STRIP-CONCLUSIONS PROOFS))
                (force (tactic.skeletonp x))
                (force (consp proofs)))
           (equal (logic.conclusion (first proofs))
                  (logic.disjoin-formulas
                   (logic.term-list-formulas (first (tactic.skeleton->goals x)))))))

(%autoprove crock-1-for-tactic.use-compile)
(local (%enable default crock-1-for-tactic.use-compile))

(%autoadmit tactic.use-compile)

(encapsulate
 ()
 (local (%enable default
                 tactic.use-okp
                 tactic.use-env-okp
                 tactic.use-compile
                 logic.term-formula))

 (%autoprove forcing-logic.appeal-listp-of-tactic.use-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.use-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.use-compile))

(%ensure-exactly-these-rules-are-missing "../../tactics/use")