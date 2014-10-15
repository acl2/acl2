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
(include-book "replace-subterm")
(%interactive)

(defthm logic.term-listp-when-tuplep-2-of-logic.termps
  ;; BOZO unlocalize in tactics/fertilize
  (implies (and (tuplep 2 x)
                (logic.termp (first x))
                (logic.termp (second x)))
           (equal (logic.term-listp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(%autoprove logic.term-listp-when-tuplep-2-of-logic.termps)

(%autoadmit tactic.fertilize-okp)
(%autoadmit tactic.fertilize-env-okp)

(%autoprove booleanp-of-tactic.fertilize-okp
            (%enable default tactic.fertilize-okp))

(%autoprove booleanp-of-tactic.fertilize-env-okp
            (%enable default tactic.fertilize-env-okp))


(%autoadmit tactic.fertilize-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.fertilize-tac
            (%enable default tactic.fertilize-tac))

(%autoprove forcing-tactic.fertilize-okp-of-tactic.fertilize-tac
            (%enable default
                     tactic.fertilize-tac
                     tactic.fertilize-okp))

(%autoprove forcing-tactic.fertilize-env-okp-of-tactic.fertilize-tac
            (%enable default
                     tactic.fertilize-tac
                     tactic.fertilize-env-okp))


(%deftheorem tactic.fertilize-lemma1-helper)

(%autoadmit tactic.fertilize-lemma1)

(encapsulate
 ()
 (local (%enable default
                 tactic.fertilize-lemma1-helper
                 tactic.fertilize-lemma1))

 (%autoprove tactic.fertilize-lemma1-under-iff)
 (%autoprove forcing-logic.appealp-of-tactic.fertilize-lemma1)
 (%autoprove forcing-logic.conclusion-of-tactic.fertilize-lemma1)
 (%autoprove forcing-logic.proofp-of-tactic.fertilize-lemma1))




(%autoadmit tactic.fertilize-bldr)

(encapsulate
 ()
 (local (%enable default tactic.fertilize-bldr))
 (%autoprove tactic.fertilize-bldr-under-iff)
 (%autoprove forcing-logic.appealp-of-tactic.fertilize-bldr)
 (%autoprove forcing-logic.conclusion-of-tactic.fertilize-bldr)
 (%autoprove forcing-logic.proofp-of-tactic.fertilize-bldr))



(%autoadmit tactic.fertilize-compile)


(encapsulate
 ()
 (local (%enable default
                 tactic.fertilize-okp
                 tactic.fertilize-env-okp
                 tactic.fertilize-compile
                 logic.term-formula))

 (defthmd crock-for-tactic.fertilize-compile
   (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
            (equal (logic.conclusion (first proofs))
                   (clause.clause-formula (first goals)))))

 (%autoprove crock-for-tactic.fertilize-compile)

 (local (%enable default crock-for-tactic.fertilize-compile))

 (%autoprove forcing-logic.appeal-listp-of-tactic.fertilize-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.fertilize-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.fertilize-compile))

(%ensure-exactly-these-rules-are-missing "../../tactic/fertilize")