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
(%interactive)


(%autoadmit clause.absurd-termp)

(%autoprove booleanp-of-clause.absurd-termp
            (%enable default clause.absurd-termp))


(%autoadmit clause.remove-absurd-terms-from-list)

(%autoprove clause.remove-absurd-terms-from-list-when-not-consp
            (%restrict default clause.remove-absurd-terms-from-list (equal x 'x)))

(%autoprove clause.remove-absurd-terms-from-list-of-cons
            (%restrict default clause.remove-absurd-terms-from-list (equal x '(cons a x))))

(%autoprove true-listp-of-clause.remove-absurd-terms-from-list
            (%cdr-induction x))

(%autoprove clause.remove-absurd-terms-from-list-of-list-fix
            (%cdr-induction x))

(%autoprove clause.remove-absurd-terms-from-list-of-app
            (%cdr-induction x))

(%autoprove rev-of-clause.remove-absurd-terms-from-list
            (%cdr-induction x))

(%autoprove subsetp-of-clause.remove-absurd-terms-from-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-listp-of-clause.remove-absurd-terms-from-list
            (%cdr-induction x))



(%defprojection :list (clause.remove-absurd-terms-from-clauses x)
                :element (clause.remove-absurd-terms-from-list x))

(%autoprove all-superset-of-somep-of-clause.remove-absurd-terms-from-clauses
            (%cdr-induction x))

(%autoprove all-subset-of-somep-of-clause.remove-absurd-terms-from-clauses
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-listp-of-clause.remove-absurd-terms-from-clauses
            (%cdr-induction x))




(%autoadmit clause.fast-remove-absurd-terms-from-list$)

(%autoprove clause.fast-remove-absurd-terms-from-list$-removal
            (%induct (rank x)
                     ((not (consp x))
                      nil)
                     ((and (consp x)
                           (clause.absurd-termp (car x)))
                      (((x (cdr x)) (acc acc))))
                     ((and (consp x)
                           (not (clause.absurd-termp (car x))))
                      (((x (cdr x)) (acc (cons (car x) acc))))))
            (%restrict default clause.fast-remove-absurd-terms-from-list$ (equal x 'x)))


