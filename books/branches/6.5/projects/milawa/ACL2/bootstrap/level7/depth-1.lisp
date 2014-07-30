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



;; BOZO move these to utilities or wherever max is defined
(defthm max-of-nfix-left
  (equal (max (nfix a) b)
         (max a b)))

(defthm max-of-nfix-right
  (equal (max a (nfix b))
         (max a b)))

(%autoprove max-of-nfix-left)
(%autoprove max-of-nfix-right)


(%autoadmit clause.flag-depth)
(%autoadmit clause.depth)
(%autoadmit clause.depth-list)

(%autoprove definition-of-clause.depth
            (%restrict default clause.flag-depth (equal x 'x))
            (%enable default clause.depth clause.depth-list))

(%autoprove definition-of-clause.depth-list
            (%restrict default clause.flag-depth (equal x 'x))
            (%enable default clause.depth clause.depth-list))

(%autoprove clause.flag-depth-of-term
            (%enable default clause.depth))

(%autoprove clause.flag-depth-of-list
            (%enable default clause.depth-list))



(%autoprove forcing-clause.depth-of-logic.function
            (%restrict default definition-of-clause.depth (memberp x '((logic.function fn args)
                                                                       (logic.function 'if args))))
            (%forcingp nil))

(%autoprove forcing-clause.depth-of-logic.lambda
            (%restrict default definition-of-clause.depth (equal x '(logic.lambda formals body actuals)))
            (%forcingp nil))

(%autoprove clause.depth-list-when-not-consp
            (%restrict default definition-of-clause.depth-list (equal x 'x)))

(%autoprove clause.depth-list-of-cons
            (%restrict default definition-of-clause.depth-list (equal x '(cons a x))))



(%autoprove clause.depth-list-when-length-three
            (%disable default max))


(%autoprove lemma-for-natp-of-clause.depth
            (%clause.simple-term-induction flag x)
            (%restrict default definition-of-clause.depth (equal x 'x)))

(%autoprove natp-of-clause.depth
            (%use (%instance (%thm lemma-for-natp-of-clause.depth) (flag 'term))))

(%autoprove natp-of-clause.depth-list
            (%use (%instance (%thm lemma-for-natp-of-clause.depth) (flag 'list))))


(%autoprove clause.depth-list-of-list-fix
            (%cdr-induction x))

(%autoprove clause.depth-list-of-app
            (%cdr-induction x))

(%autoprove clause.depth-list-of-rev
            (%cdr-induction x))



(%autoprove lemma-for-clause.depth-zero
            (%clause.simple-term-induction flag x)
            (%restrict default definition-of-clause.depth (equal x 'x)))

(%autoprove clause.depth-zero
            (%use (%instance (%thm lemma-for-clause.depth-zero) (flag 'term))))

(%autoprove clause.depth-list-zero
            (%use (%instance (%thm lemma-for-clause.depth-zero) (flag 'list))))



(%autoprove clause.depth-when-clause.simple-termp)

(%autoprove clause.depth-list-when-clause.simple-term-listp)

(%autoprove clause.depth-positive-when-non-clause.simple-termp)

(%autoprove clause.depth-list-positive-when-non-clause.simple-term-listp)




