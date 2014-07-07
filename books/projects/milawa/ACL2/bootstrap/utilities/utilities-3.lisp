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
(include-book "utilities-2")
(%interactive)



(%autoadmit rev)

(%autoprove rev-when-not-consp
            (%restrict default rev (equal x 'x)))

(%autoprove rev-of-cons
            (%restrict default rev (equal x '(cons a x))))

(%autoprove rev-of-list-fix
            (%cdr-induction x))

(%autoprove true-listp-of-rev
            (%car-cdr-elim x))

(%autoprove rev-under-iff)

(%autoprove len-of-rev
            (%cdr-induction x))

(%autoprove memberp-of-rev
            (%cdr-induction x))

(%autoprove memberp-of-first-of-rev
            (%cdr-induction x))

(%autoprove subsetp-of-rev-one
            (%use (%instance (%thm subsetp-badguy-membership-property) (x (rev x)) (y x)))
            (%use (%instance (%thm subsetp-badguy-membership-property) (x x) (y (rev x)))))

(%autoprove subsetp-of-rev-two
            (%use (%instance (%thm subsetp-badguy-membership-property) (x y) (y (rev y))))
            (%use (%instance (%thm subsetp-badguy-membership-property) (x (rev y)) (y y))))

(%autoprove lemma-for-rev-of-rev
            (%cdr-induction x))

(%autoprove rev-of-rev
            (%cdr-induction x)
            (%enable default lemma-for-rev-of-rev))

(%autoprove rev-of-app
            (%cdr-induction x)
            (%auto)
            (%fertilize (rev (app x2 y)) (app (rev y) (rev x2))))

(%autoprove subsetp-of-app-of-rev-of-self-one
            (%cdr-induction x))

(%autoprove subsetp-of-app-of-rev-of-self-two
            (%cdr-induction x))



(%autoadmit revappend)

(%autoprove revappend-when-not-consp
            (%restrict default revappend (equal x 'x)))

(%autoprove revappend-of-cons
            (%restrict default revappend (equal x '(cons a x))))

(%autoprove forcing-revappend-removal
            (%autoinduct revappend)
            (%enable default revappend-when-not-consp revappend-of-cons))



(%autoadmit fast-rev)

(%autoprove fast-rev-removal
            (%enable default fast-rev))



(%autoadmit fast-app)

(%autoprove fast-app-removal
            (%enable default fast-app))

