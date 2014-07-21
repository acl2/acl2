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


(%autoadmit tactic.urewrite-first-okp)

(%autoprove booleanp-of-tactic.urewrite-first-okp
            (%enable default tactic.urewrite-first-okp))

(%autoadmit tactic.urewrite-first-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.urewrite-first-tac
            (%enable default tactic.urewrite-first-tac))

(%autoprove forcing-tactic.urewrite-first-okp-of-tactic.urewrite-first-tac
            (%forcingp nil)
            (%enable default
                     tactic.urewrite-first-tac
                     tactic.urewrite-first-okp))

(%autoadmit tactic.urewrite-first-compile)

(local (%enable default
                tactic.urewrite-first-okp
                tactic.urewrite-first-compile))

(local (%forcingp nil))

(%autoprove forcing-logic.appeal-listp-of-tactic.urewrite-first-compile)
(%autoprove forcing-logic.strip-conclusions-of-tactic.urewrite-first-compile)
(%autoprove forcing-logic.proof-listp-of-tactic.urewrite-first-compile
            (%disable default
                      MEMBERP-WHEN-MEMBERP-OF-CDR
                      MEMBERP-WHEN-NOT-CONSP
                      CAR-WHEN-MEMBERP-AND-NOT-MEMBERP-OF-CDR-CHEAP
                      CAR-WHEN-MEMBERP-OF-SINGLETON-LIST-CHEAP
                      unusual-memberp-rules))

(%ensure-exactly-these-rules-are-missing "../../tactics/urewrite-first")
