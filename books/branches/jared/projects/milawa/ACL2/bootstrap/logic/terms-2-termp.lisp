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
(include-book "terms-2-term-vars")
(include-book "terms-2-variable-listp")
(%interactive)


(%autoadmit logic.flag-termp)
(%autoadmit logic.termp)
(%autoadmit logic.term-listp)

(defmacro %logic.term-induction (flag x)
  `(%induct (rank ,x)
            ((and (equal ,flag 'term)
                  (logic.constantp ,x))
             nil)
            ((and (equal flag 'term)
                  (logic.variablep ,x))
             nil)
            ((and (equal ,flag 'term)
                  (logic.functionp ,x))
             (((,flag 'list)
               (,x    (logic.function-args ,x)))))
            ((and (equal ,flag 'term)
                  (logic.lambdap ,x))
             (((,flag 'term)
               (,x    (logic.lambda-body ,x)))
              ((,flag 'list)
               (,x    (logic.lambda-actuals ,x)))))
            ((and (equal ,flag 'term)
                  (not (logic.constantp ,x))
                  (not (logic.variablep ,x))
                  (not (logic.functionp ,x))
                  (not (logic.lambdap ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (consp ,x))
             (((,flag 'term)
               (,x    (car ,x)))
              ((,flag 'list)
               (,x    (cdr ,x)))))))

(%autoprove definition-of-logic.termp
            (%enable default logic.termp logic.term-listp)
            (%restrict default logic.flag-termp (equal x 'x)))

(%autoprove definition-of-logic.term-listp
            (%enable default logic.termp logic.term-listp)
            (%restrict default logic.flag-termp (equal x 'x)))

(%autoprove logic.termp-when-not-consp-cheap
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.termp-when-logic.variablep
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.termp-when-logic.constantp
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.term-listp-when-not-consp
            (%restrict default definition-of-logic.term-listp (equal x 'x)))

(%autoprove logic.term-listp-of-cons
            (%restrict default definition-of-logic.term-listp (equal x '(cons a x))))

(%autoprove booleanp-of-logic.term-listp
            (%cdr-induction x))

(%autoprove booleanp-of-logic.termp
            (%restrict default definition-of-logic.termp (equal x 'x)))


(%deflist logic.term-listp (x)
          (logic.termp x))

(%autoprove first-under-iff-when-logic.term-listp-with-len-free)

(%autoprove second-under-iff-when-logic.term-listp-with-len-free)

(%autoprove third-under-iff-when-logic.term-listp-with-len-free)
