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
(include-book "tuple-listp")
(include-book "list-list-fix")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(%autoadmit remove-all-from-ranges)

(%autoprove remove-all-from-ranges-when-not-consp
            (%restrict default remove-all-from-ranges (equal x 'x)))

(%autoprove remove-all-from-ranges-of-cons
            (%restrict default remove-all-from-ranges (equal x '(cons b x))))

(%autoprove true-listp-of-remove-all-from-ranges
            (%cdr-induction x))

(%autoprove true-list-listp-of-remove-all-from-ranges
            (%cdr-induction x))

(%autoprove mapp-of-remove-all-from-ranges
            (%cdr-induction x))

(%autoprove remove-all-from-ranges-of-list-fix
            (%cdr-induction x))

(%autoprove remove-all-from-ranges-of-list-list-fix
            (%cdr-induction x))

(%autoprove remove-all-from-ranges-of-app
            (%cdr-induction x))

(%autoprove remove-all-from-ranges-of-rev
            (%cdr-induction x))

(%autoprove len-of-remove-all-from-ranges
            (%cdr-induction x))
