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



(%autoadmit remove-duplicates)

(%autoprove remove-duplicates-when-not-consp
            (%restrict default remove-duplicates (equal x 'x)))

(%autoprove remove-duplicates-of-cons
            (%restrict default remove-duplicates (equal x '(cons a x))))

(%autoprove true-listp-of-remove-duplicates
            (%cdr-induction x))

(%autoprove len-of-remove-duplicates
            (%cdr-induction x))

(%autoprove remove-duplicates-of-list-fix
            (%cdr-induction x))

(%autoprove memberp-of-remove-duplicates
            (%cdr-induction x))

(%autoprove subsetp-of-remove-duplicates-one
            (%use (%instance (%thm subsetp-badguy-membership-property) (x (remove-duplicates x)) (y x)))
            (%use (%instance (%thm subsetp-badguy-membership-property) (x x) (y (remove-duplicates x)))))

(%autoprove subsetp-of-remove-duplicates-two
            (%use (%instance (%thm subsetp-badguy-membership-property) (x (remove-duplicates y)) (y y)))
            (%use (%instance (%thm subsetp-badguy-membership-property) (x y) (y (remove-duplicates y)))))

(%autoprove subsetp-of-cons-onto-remove-duplicates)

;; see also utilities-4.lisp for some additional theorems about remove-duplicates

