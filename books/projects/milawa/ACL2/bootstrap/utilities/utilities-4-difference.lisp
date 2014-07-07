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


(%autoadmit difference)

(%autoprove difference-when-not-consp
            (%restrict default difference (equal x 'x)))

(%autoprove difference-of-cons
            (%restrict default difference (equal x '(cons a x))))

(%autoprove true-listp-of-difference
            (%cdr-induction x))

(%autoprove difference-of-list-fix-one
            (%cdr-induction x))

(%autoprove difference-of-list-fix-two
            (%cdr-induction x))

(%autoprove difference-of-app-one
            (%cdr-induction x))

(%autoprove difference-of-difference
            (%cdr-induction x))

(%autoprove rev-of-difference
            (%cdr-induction x))

(%autoprove difference-of-rev)

(%autoprove difference-of-rev-two
            (%cdr-induction x))

(%autoprove memberp-of-difference
            (%cdr-induction x))

(%autoprove difference-when-subsetp
            (%cdr-induction x))

(%autoprove subsetp-with-app-of-difference-onto-takeaway
            (%cdr-induction x))



(%autoadmit fast-difference$)

(%autoprove fast-difference$-when-not-consp
            (%restrict default fast-difference$ (equal x 'x)))

(%autoprove fast-difference$-of-cons
            (%restrict default fast-difference$ (equal x '(cons a x))))

(%autoprove forcing-fast-difference$-removal
            (%enable default fast-difference$-when-not-consp)
            (%enable default fast-difference$-of-cons)
            (%autoinduct fast-difference$))

