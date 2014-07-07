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
(include-book "terms-1")
(%interactive)



(%autoadmit logic.flag-term-vars)
(%autoadmit logic.slow-term-vars)
(%autoadmit logic.term-vars)
(%autoadmit logic.term-list-vars)

(defmacro %logic.flag-term-vars-induction (flag x acc)
  `(%induct (rank ,x)
            ((and (equal ,flag 'term)
                  (or (logic.constantp ,x)
                      (logic.variablep ,x)
                      (not (consp ,x))))
             nil)
            ((and (equal ,flag 'term)
                  (not (logic.constantp ,x))
                  (not (logic.variablep ,x))
                  (consp ,x))
             (((,flag 'list)
               (,x    (cdr ,x))
               (,acc  ,acc))))
            ((and (not (equal ,flag 'term))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (consp ,x))
             (((,flag 'term)
               (,x    (car ,x))
               (,acc  (logic.flag-term-vars 'list (cdr ,x) ,acc)))
              ((,flag 'list)
               (,x    (cdr ,x))
               (,acc  ,acc))))))



(%autoprove true-listp-of-logic.flag-term-vars
            (%restrict default logic.flag-term-vars (equal x 'x))
            (%logic.flag-term-vars-induction flag x acc)
            ;; big gains by avoiding urewrite for some reason
            (%auto :strategy (cleanup split crewrite elim)))

(encapsulate
 ()
 (%autoprove lemma-for-definition-of-logic.term-vars
             (%logic.flag-term-vars-induction flag x acc)
             (%restrict default logic.flag-term-vars (equal x 'x))
             (%restrict default logic.slow-term-vars (equal x 'x))
             (%auto :strategy (cleanup split crewrite elim)))

 (local (%enable default lemma-for-definition-of-logic.term-vars))

 (%autoprove definition-of-logic.term-vars
             (%enable default logic.term-vars logic.term-list-vars)
             (%restrict default logic.slow-term-vars (equal x 'x)))

 (%autoprove definition-of-logic.term-list-vars
             (%enable default logic.term-vars logic.term-list-vars)
             (%restrict default logic.slow-term-vars (equal x 'x)))

 (%autoprove logic.flag-term-vars-of-term-removal
             (%enable default logic.term-vars)
             (%restrict default logic.slow-term-vars (equal x 'x)))

 (%autoprove logic.flag-term-vars-of-list-removal
             (%enable default logic.term-list-vars)
             (%restrict default logic.slow-term-vars (equal x 'x))))

