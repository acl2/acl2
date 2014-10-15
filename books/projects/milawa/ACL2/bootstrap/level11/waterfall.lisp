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
(include-book "waterfall-main")
(include-book "waterfall-compiler")
(%interactive)


(%autoadmit tactic.waterfall-okp)

(%autoprove booleanp-of-tactic.waterfall-okp
            (%enable default tactic.waterfall-okp))


(%autoadmit rw.waterfall-list-wrapper)
(%enable default rw.waterfall-list-wrapper)

(%autoadmit tactic.waterfall-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.waterfall-tac
            (%enable default tactic.waterfall-tac))

(%autoprove forcing-tactic.waterfall-okp-of-tactic.waterfall-tac
            (%enable default tactic.waterfall-tac tactic.waterfall-okp)
            (%restrict default nth (logic.constantp n)))


(%autoadmit tactic.waterfall-compile)

(encapsulate
 ()
 (local (%enable default tactic.waterfall-okp tactic.waterfall-compile))

 (%autoprove forcing-logic.appeal-listp-of-tactic.waterfall-compile
             (%auto :strategy (cleanup split urewrite))
             ;; Wow, this is really nice.  I wish I could do this in ACL2.
             (%generalize (NTH '5 (TACTIC.SKELETON->EXTRAS X)) ufastp)
             (%generalize (nth '6 (TACTIC.SKELETON->EXTRAS X)) cfastp)
             (%generalize (car (TACTIC.SKELETON->EXTRAS X)) wsteps)
             (%generalize (car (cdr (TACTIC.SKELETON->EXTRAS X))) theoryname)
             (%generalize (CAR (CDR (CDR (CDR (TACTIC.SKELETON->EXTRAS X))))) maxdepth)
             (%generalize (CAR (CDR (CDR (TACTIC.SKELETON->EXTRAS X)))) strategy))

 (%autoprove forcing-logic.strip-conclusions-of-tactic.waterfall-compile
             (%auto :strategy (cleanup split urewrite))
             ;; Wow, this is really nice.  I wish I could do this in ACL2.
             (%generalize (NTH '5 (TACTIC.SKELETON->EXTRAS X)) ufastp)
             (%generalize (nth '6 (TACTIC.SKELETON->EXTRAS X)) cfastp)
             (%generalize (car (TACTIC.SKELETON->EXTRAS X)) wsteps)
             (%generalize (car (cdr (TACTIC.SKELETON->EXTRAS X))) theoryname)
             (%generalize (CAR (CDR (CDR (CDR (TACTIC.SKELETON->EXTRAS X))))) maxdepth)
             (%generalize (CAR (CDR (CDR (TACTIC.SKELETON->EXTRAS X)))) strategy))

 (%autoprove forcing-logic.proof-listp-of-tactic.waterfall-compile
             (%auto :strategy (cleanup split urewrite))
             ;; Wow, this is really nice.  I wish I could do this in ACL2.
             (%generalize (NTH '5 (TACTIC.SKELETON->EXTRAS X)) ufastp)
             (%generalize (nth '6 (TACTIC.SKELETON->EXTRAS X)) cfastp)
             (%generalize (car (TACTIC.SKELETON->EXTRAS X)) wsteps)
             (%generalize (car (cdr (TACTIC.SKELETON->EXTRAS X))) theoryname)
             (%generalize (CAR (CDR (CDR (CDR (TACTIC.SKELETON->EXTRAS X))))) maxdepth)
             (%generalize (CAR (CDR (CDR (TACTIC.SKELETON->EXTRAS X)))) strategy)))


(%ensure-exactly-these-rules-are-missing "../../tactics/waterfall")