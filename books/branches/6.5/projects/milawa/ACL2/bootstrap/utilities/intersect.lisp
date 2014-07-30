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

(%autoadmit intersect)
(%autoprove intersect-when-not-consp-one (%restrict default intersect (equal x 'x)))
(%autoprove intersect-of-cons-one        (%restrict default intersect (equal x '(cons a x))))
(%autoprove intersect-when-not-consp-two (%cdr-induction x))
(%autoprove intersect-under-iff          (%cdr-induction x))
(%autoprove true-listp-of-intersect      (%cdr-induction x))
(%autoprove intersect-of-list-fix-one    (%cdr-induction x))
(%autoprove intersect-of-list-fix-two    (%cdr-induction x))
(%autoprove intersect-of-app-one         (%cdr-induction x))
(%autoprove rev-of-intersect             (%cdr-induction x))
(%autoprove intersect-of-rev-two         (%cdr-induction x))
(%autoprove subsetp-of-intersect-one     (%cdr-induction x))
(%autoprove subsetp-of-intersect-two     (%cdr-induction x))
(%autoprove intersect-when-subsetp       (%cdr-induction x))
(%autoprove intersect-with-self)

(%ensure-exactly-these-rules-are-missing "../../utilities/intersect")