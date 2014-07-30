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
(include-book "terms")
(%interactive)


(%autoadmit logic.flag-count-function-occurrences)
(%autoadmit logic.count-function-occurrences)
(%autoadmit logic.count-function-occurrences-list)
(%autoadmit logic.slow-count-function-occurrences)

(defmacro %logic.flag-count-function-occurrences-induction (flag x acc)
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
               (,x    (logic.function-args ,x))
               (,acc  (+ 1 ,acc)))))
            ((and (equal ,flag 'term)
                  (logic.lambdap ,x))
             (((,flag 'list)
               (,x    (logic.lambda-actuals ,x))
               (,acc  (+ 1 ,acc)))))
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
               (,x (car ,x))
               (acc ,acc))
              ((,flag 'list)
               (,x (cdr ,x))
               (,acc (logic.flag-count-function-occurrences 'term (car ,x) ,acc)))))))

(%autoprove forcing-natp-of-logic.flag-count-function-occurrences
            (%logic.flag-count-function-occurrences-induction flag x acc)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default logic.flag-count-function-occurrences (equal x 'x)))

(%autoprove lemma-forcing-logic.flag-count-function-occurrences-removal
            (%logic.flag-count-function-occurrences-induction flag x acc)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default logic.flag-count-function-occurrences (equal x 'x))
            (%restrict default logic.slow-count-function-occurrences (equal x 'x))
            (%auto)
            (%fertilize (logic.flag-count-function-occurrences 'term x1 acc)
                        (+ acc (logic.slow-count-function-occurrences 'term x1))))

(%autoprove definition-of-logic.count-function-occurrences
            (%restrict default logic.slow-count-function-occurrences (equal x 'x))
            (%enable default
                     logic.count-function-occurrences
                     logic.count-function-occurrences-list
                     lemma-forcing-logic.flag-count-function-occurrences-removal
                     ))

(%autoprove definition-of-logic.count-function-occurrences-list
            (%restrict default logic.slow-count-function-occurrences (equal x 'x))
            (%enable default
                     logic.count-function-occurrences
                     logic.count-function-occurrences-list
                     lemma-forcing-logic.flag-count-function-occurrences-removal
                     ))

(%autoprove logic.flag-count-function-occurrences-removal
            (%restrict default logic.slow-count-function-occurrences (equal x 'x))
            (%enable default
                     lemma-forcing-logic.flag-count-function-occurrences-removal
                     logic.count-function-occurrences
                     logic.count-function-occurrences-list))

(%autoprove logic.count-function-occurrences-list-when-not-consp
            (%restrict default definition-of-logic.count-function-occurrences-list (equal x 'x)))

(%autoprove logic.count-function-occurrences-list-of-cons
            (%restrict default definition-of-logic.count-function-occurrences-list (equal x '(cons a x))))


(%autoprove lemma-for-natp-of-logic.count-function-occurrences
            (%logic.term-induction flag x)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default definition-of-logic.count-function-occurrences (equal x 'x)))

(%autoprove natp-of-logic.count-function-occurrences
            (%use (%instance (%thm lemma-for-natp-of-logic.count-function-occurrences) (flag 'term))))

(%autoprove natp-of-logic.count-function-occurrences-list
            (%use (%instance (%thm lemma-for-natp-of-logic.count-function-occurrences) (flag 'list))))

(%autoprove logic.count-function-occurrences-when-logic.constantp
            (%restrict default definition-of-logic.count-function-occurrences (equal x 'x)))

(%autoprove logic.count-function-occurrences-positive-when-logic.functionp
            (%restrict default definition-of-logic.count-function-occurrences (equal x 'x)))

(%autoprove logic.count-function-occurrences-positive-when-logic.lambdap
            (%restrict default definition-of-logic.count-function-occurrences (equal x 'x)))

