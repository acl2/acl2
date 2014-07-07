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
(include-book "utilities")
(%interactive)


(%autoadmit sort-symbols-insert)

(%autoprove sort-symbols-insert-when-not-consp
            (%restrict default sort-symbols-insert (equal x 'x)))

(%autoprove sort-symbols-insert-of-cons
            (%restrict default sort-symbols-insert (equal x '(cons b x))))

(%autoprove memberp-of-sort-symbols-insert
            (%cdr-induction x))

(%autoprove len-of-sort-symbols-insert
            (%cdr-induction x))

(%autoprove consp-of-sort-symbols-insert
            (%cdr-induction x))

(%autoprove car-of-sort-symbols-insert)

(%autoprove uniquep-of-sort-symbols-insert
            (%cdr-induction x))


(%autoadmit sort-symbols)

(%autoprove sort-symbols-when-not-consp
            (%restrict default sort-symbols (equal x 'x)))

(%autoprove sort-symbols-of-cons
            (%restrict default sort-symbols (equal x '(cons a x))))

(%autoprove memberp-of-sort-symbols
            (%cdr-induction x))

(%autoprove len-of-sort-symbols
            (%cdr-induction x))

(%autoprove disjointp-of-sort-symbols
            (%cdr-induction x))

(%autoprove uniquep-of-sort-symbols
            (%cdr-induction x))


(%autoadmit symbol-list-orderedp)

(%autoprove symbol-list-orderedp-when-not-consp
            (%restrict default symbol-list-orderedp (equal x 'x)))

(%autoprove symbol-list-orderedp-when-not-consp-of-cdr
            (%restrict default symbol-list-orderedp (equal x 'x)))

(%autoprove symbol-list-orderedp-of-cons
            (%restrict default symbol-list-orderedp (equal x '(cons a x))))

(%autoprove symbol-list-orderedp-of-sort-symbols-insert
            (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../utilities/sort-symbols")