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
(include-book "utilities-3")
(%interactive)


(%autoadmit repeat)

(%autoprove repeat-of-zero
            (%restrict default repeat (equal n ''0)))

(%autoprove repeat-of-one
            (%restrict default repeat (equal n ''1)))

(%autoprove consp-of-repeat
            (%restrict default repeat (equal n 'n)))

(%autoprove repeat-under-iff
            (%restrict default repeat (equal n 'n)))

(%autoprove car-of-repeat
            (%restrict default repeat (equal n 'n)))

(%autoprove cdr-of-repeat
            (%restrict default repeat (equal n 'n)))

(%autoprove repeat-of-nfix
            (%dec-induction n)
            (%restrict default repeat (equal n '(nfix n))))

(%autoprove len-of-repeat
            (%dec-induction n)
            (%restrict default repeat (equal n 'n)))

(%autoprove true-listp-of-repeat
            (%dec-induction n)
            (%restrict default repeat (equal n 'n)))

(%autoprove memberp-of-repeat
            (%dec-induction n)
            (%split)
            ;; Could use (%restrict ...) (%auto) for 187m conses
            ;; Could use (%auto) (%restrict ...) (%auto) for 47m conses
            ;; Or leave these nasty hints for 36m conses
            (%cleanup)
            (%crewrite default)
            (%split)
            (%cleanup)
            (%restrict default repeat (or (equal n 'n) (equal n ''1))))

(%autoprove app-of-repeat
            (%dec-induction n1)
            (%split)
            (%restrict default repeat (or (equal n 'n1) (equal n ''0))))

(%autoprove lemma-for-rev-of-repeat
            (%dec-induction n)
            (%restrict default repeat (equal n 'n)))

(%autoprove rev-of-repeat
            (%dec-induction n)
            (%enable default lemma-for-rev-of-repeat)
            (%restrict default repeat (equal n 'n)))

