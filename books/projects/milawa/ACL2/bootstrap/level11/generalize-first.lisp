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


(%autoadmit tactic.generalize-first-okp)
(%autoadmit tactic.generalize-first-env-okp)

(%autoprove booleanp-of-tactic.generalize-first-okp
            (%enable default tactic.generalize-first-okp))

(%autoprove booleanp-of-tactic.generalize-first-env-okp
            (%enable default tactic.generalize-first-env-okp))


(%autoadmit tactic.generalize-first-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.generalize-first-tac
            (%enable default tactic.generalize-first-tac))

(%autoprove forcing-tactic.generalize-first-okp-of-tactic.generalize-first-tac
            (%enable default
                     tactic.generalize-first-tac
                     tactic.generalize-first-okp))

(%autoprove forcing-tactic.generalize-first-env-okp-of-tactic.generalize-first-tac
            (%enable default
                     tactic.generalize-first-tac
                     tactic.generalize-first-env-okp))


(%autoadmit tactic.generalize-first-compile)

(encapsulate
 ()
 (local (%enable default
                 tactic.generalize-first-okp
                 tactic.generalize-first-env-okp
                 tactic.generalize-first-compile))

 (defthm crock1-for-tactic.generalize-first
   ;; BOZO unlocalize/rename
   (implies (equal x (logic.disjoin-formulas y))
            (equal (logic.substitute-formula x sigma)
                   (logic.disjoin-formulas (logic.substitute-formula-list y sigma)))))

 (defthm crock2-for-tactic.generalize-first
   ;; BOZO unlocalize/rename
   (implies (and (equal terms (logic.replace-subterm-list x old new) )
                 (not (memberp new (logic.term-list-vars x)))
                 (logic.variablep new)
                 (force (logic.term-listp x)))
            (equal (logic.substitute-list terms (list (cons new old)))
                   (list-fix x)))
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (%autoprove crock1-for-tactic.generalize-first)
 (%autoprove crock2-for-tactic.generalize-first)

 (%autoprove forcing-logic.appeal-listp-of-tactic.generalize-first-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.generalize-first-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.generalize-first-compile))

(%ensure-exactly-these-rules-are-missing "../../tactics/generalize-first")