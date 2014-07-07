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
(include-book "worldp")
(include-book "fast-urewrite")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defsection tactic.world->control
  (%autoadmit tactic.world->control)
  (local (%enable default tactic.world->control))
  (%autoprove rw.controlp-of-tactic.world->control)
  (%autoprove rw.control-atblp-of-tactic.world->control)
  (%autoprove rw.control-env-okp-of-tactic.world->control))


(%autoadmit rw.world-urewrite)
(%enable default rw.world-urewrite)

(%autoadmit rw.world-urewrite-list)
(%autoadmit rw.world-urewrite-list-list)

(%autoprove rw.world-urewrite-list-redefinition
            (%cdr-induction x)
            (%restrict default rw.world-urewrite-list (equal x 'x)))

(%autoprove rw.world-urewrite-list-list-redefinition
            (%cdr-induction x)
            (%restrict default rw.world-urewrite-list-list (equal x 'x)))

(%autoadmit rw.fast-urewrite-list-list)

(%autoprove rw.fast-urewrite-list-list-removal
            (%cdr-induction x)
            (%restrict default rw.fast-urewrite-list-list (equal x 'x)))

(%autoadmit rw.fast-world-urewrite)
(%enable default rw.fast-world-urewrite)

(%autoadmit rw.fast-world-urewrite-list)

(%autoprove definition-of-rw.fast-world-urewrite-list
            (%cdr-induction x)
            (%restrict default rw.fast-world-urewrite-list (equal x 'x))
            (%restrict default definition-of-rw.fast-urewrite-list (equal x 'x))
            (%disable default tactic.world->control))

(%autoadmit rw.fast-world-urewrite-list-list)

(%autoprove definition-of-rw.fast-world-urewrite-list-list
            (%cdr-induction x)
            (%restrict default rw.fast-world-urewrite-list-list (equal x 'x))
            (%restrict default rw.fast-urewrite-list-list (equal x 'x))
            (%disable default tactic.world->control))


