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



(%autoadmit disjointp)


(%autoprove disjointp-when-not-consp-one
            (%restrict default disjointp (equal x 'x)))

(%autoprove disjointp-of-cons-one
            (%restrict default disjointp (equal x '(cons a x))))

(%autoprove booleanp-of-disjointp
            (%cdr-induction x))

(%autoprove disjointp-when-not-consp-two
            (%cdr-induction x))

(%autoprove disjointp-of-cons-two
            (%cdr-induction x))

(%autoprove symmetry-of-disjointp
            (%cdr-induction x))

(%autoprove disjointp-of-list-fix-one
            (%cdr-induction x))

(%autoprove disjointp-of-list-fix-two
            (%disable default symmetry-of-disjointp)
            (%use (%instance (%thm symmetry-of-disjointp) (x x) (y (list-fix y))))
            (%use (%instance (%thm symmetry-of-disjointp) (x y) (y x))))

(%autoprove disjointp-of-singleton-one)
(%autoprove disjointp-of-singleton-two)

(%autoprove disjointp-when-common-member-one
            (%cdr-induction x))

(%autoprove disjointp-when-common-member-two)

(%autoprove disjointp-of-app-two
            (%cdr-induction x))

(%autoprove disjointp-of-app-one)

(%autoprove disjointp-of-rev-two
            (%cdr-induction x))

(%autoprove disjointp-of-rev-one)

(%autoprove disjointp-when-subsetp-of-disjointp-one
            (%cdr-induction x))

(%autoprove disjointp-when-subsetp-of-disjointp-two)

(%autoprove disjointp-when-subsetp-of-disjointp-three
            (%cdr-induction x))

(%autoprove disjointp-when-subsetp-of-disjointp-four)

(%autoprove disjointp-when-subsetp-of-other-one
            (%cdr-induction x))

(%autoprove disjointp-when-subsetp-of-other-two
            (%cdr-induction y))

(%autoprove memberp-when-disjointp-one
            (%cdr-induction x))

(%autoprove memberp-when-disjointp-two)
