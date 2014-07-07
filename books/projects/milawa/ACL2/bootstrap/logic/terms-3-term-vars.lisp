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
(include-book "terms-2")
(%interactive)

(%autoprove logic.term-list-vars-when-not-consp
            (%restrict default definition-of-logic.term-list-vars (equal x 'x)))

(%autoprove logic.term-list-vars-of-cons
            (%restrict default definition-of-logic.term-list-vars (equal x '(cons a x))))

(%autoprove true-listp-of-logic.term-list-vars
            (%cdr-induction x))

(%autoprove true-listp-of-logic.term-vars
            (%restrict default definition-of-logic.term-vars (equal x 'x)))

(%autoprove logic.term-vars-when-variable
            (%restrict default definition-of-logic.term-vars (equal x 'x)))

(%autoprove logic.term-vars-when-constant
            (%restrict default definition-of-logic.term-vars (equal x 'x)))

(%autoprove logic.term-vars-when-bad
            (%restrict default definition-of-logic.term-vars (equal x 'x)))

(%autoprove subsetp-of-logic.term-list-vars-of-cdr-with-logic.term-list-vars)

(%autoprove subsetp-of-logic.term-vars-of-car-with-logic.term-list-vars)

(%autoprove logic.term-list-vars-when-logic.variable-listp
            (%cdr-induction x))

(encapsulate
 ()
 (%autoprove lemma-for-subsetp-of-logic.term-list-vars-and-remove-duplicates
             (%cdr-induction x))

 (%autoprove subsetp-of-logic.term-list-vars-and-remove-duplicates
             (%cdr-induction x)
             (%enable default lemma-for-subsetp-of-logic.term-list-vars-and-remove-duplicates)))

(%autoprove subsetp-of-logic.term-list-vars-and-remove-duplicates-two
            (%cdr-induction x))

