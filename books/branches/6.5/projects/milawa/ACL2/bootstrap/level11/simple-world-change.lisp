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


(%autoadmit tactic.simple-world-change-aux)

(%autoprove tactic.worldp-of-tactic.simple-world-change-aux
            (%autoinduct tactic.simple-world-change-aux)
            (%restrict default tactic.simple-world-change-aux (equal changes 'changes)))

(%autoprove tactic.world-atblp-of-tactic.simple-world-change-aux
            (%autoinduct tactic.simple-world-change-aux)
            (%restrict default tactic.simple-world-change-aux (equal changes 'changes)))

(%autoprove tactic.world-env-okp-of-tactic.simple-world-change-aux
            (%autoinduct tactic.simple-world-change-aux)
            (%restrict default tactic.simple-world-change-aux (equal changes 'changes)))

(%autoprove tactic.world->index-of-tactic.simple-world-change-aux
            (%autoinduct tactic.simple-world-change-aux)
            (%restrict default tactic.simple-world-change-aux (equal changes 'changes)))


(%autoadmit tactic.simple-world-change)

(%autoprove tactic.worldp-of-tactic.simple-world-change
            (%enable default tactic.simple-world-change))

(%autoprove tactic.world-atblp-of-tactic.simple-world-change
            (%enable default tactic.simple-world-change))

(%autoprove tactic.world-env-okp-of-tactic.simple-world-change
            (%enable default tactic.simple-world-change))

(%autoprove tactic.world->index-of-tactic.simple-world-change
            (%enable default tactic.simple-world-change))


(%autoadmit tactic.simple-change-world-okp)

(%autoprove booleanp-of-tactic.simple-change-world-okp
            (%enable default tactic.simple-change-world-okp))

(%autoprove tactic.skeleton->goals-when-tactic.simple-change-world-okp
            (%enable default tactic.simple-change-world-okp))


(%autoadmit tactic.simple-change-world-tac)

(%autoprove tactic.skeletonp-of-tactic.simple-change-world-tac
            (%enable default tactic.simple-change-world-tac))

(%autoprove tactic.simple-change-world-okp-of-tactic.simple-change-world-tac
            (%enable default
                     tactic.simple-change-world-tac
                     tactic.simple-change-world-okp))

(%autoadmit tactic.simple-change-world-compile-world)

(%autoprove tactic.worldp-of-tactic.simple-change-world-compile-world
            (%enable default tactic.simple-change-world-compile-world))

(%autoprove tactic.world-atblp-of-tactic.simple-change-world-compile-world
            (%enable default tactic.simple-change-world-compile-world))

(%autoprove tactic.world-env-okp-of-tactic.simple-change-world-compile-world
            (%enable default tactic.simple-change-world-compile-world))


(%ensure-exactly-these-rules-are-missing "../../tactics/simple-world-change")
