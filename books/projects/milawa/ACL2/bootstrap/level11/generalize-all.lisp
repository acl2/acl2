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


(%autoadmit tactic.generalize-all-okp)
(%autoadmit tactic.generalize-all-env-okp)

(%autoprove booleanp-of-tactic.generalize-all-okp
            (%enable default tactic.generalize-all-okp))

(%autoprove booleanp-of-tactic.generalize-all-env-okp
            (%enable default tactic.generalize-all-env-okp))


(%autoadmit tactic.generalize-all-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.generalize-all-tac
            (%enable default tactic.generalize-all-tac))

(%autoprove forcing-tactic.generalize-all-okp-of-tactic.generalize-all-tac
            (%enable default
                     tactic.generalize-all-tac
                     tactic.generalize-all-okp))

(%autoprove forcing-tactic.generalize-all-env-okp-of-tactic.generalize-all-tac
            (%enable default
                     tactic.generalize-all-tac
                     tactic.generalize-all-env-okp))


(%autoadmit tactic.generalize-all-compile)

(encapsulate
 ()
 (local (%enable default
                 tactic.generalize-all-okp
                 tactic.generalize-all-env-okp
                 tactic.generalize-all-compile))

 (%autoprove forcing-logic.substitute-of-logic.replace-subterm-list-list-with-fresh-variable-free)
 (%autoprove forcing-logic.appeal-listp-of-tactic.generalize-all-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.generalize-all-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.generalize-all-compile))

(%ensure-exactly-these-rules-are-missing "../../tactics/generalize-all")
