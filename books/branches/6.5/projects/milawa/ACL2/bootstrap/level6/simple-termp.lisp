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


(%autoadmit clause.flag-simple-termp)
(%autoadmit clause.simple-termp)
(%autoadmit clause.simple-term-listp)

(%autoprove definition-of-clause.simple-termp
            (%enable default clause.simple-termp clause.simple-term-listp)
            (%restrict default clause.flag-simple-termp (equal x 'x)))

(%autoprove definition-of-clause.simple-term-listp
            (%enable default clause.simple-termp clause.simple-term-listp)
            (%restrict default clause.flag-simple-termp (equal x 'x)))

(%autoprove clause.flag-simple-termp-of-term-removal
            (%enable default clause.simple-termp))

(%autoprove clause.flag-simple-termp-of-list-removal
            (%enable default clause.simple-term-listp))

(%autoprove clause.simple-termp-when-logic.variablep
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-logic.constantp
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-non-if-logic.functionp
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-bad-args-logic.functionp
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-if-logic.functionp
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-logic.lambdap
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-degenerate
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))


(defmacro %clause.simple-term-induction (flag x)
  `(%induct (rank ,x)
            ((and (equal ,flag 'term)
                  (logic.constantp ,x))
             nil)
            ((and (equal ,flag 'term)
                  (logic.variablep ,x))
             nil)
            ((and (equal ,flag 'term)
                  (logic.functionp ,x)
                  (equal (logic.function-name ,x) 'if)
                  (equal (len (logic.function-args ,x)) 3))
             (((,flag 'term) (,x (first (logic.function-args ,x))))
              ((,flag 'term) (,x (second (logic.function-args ,x))))
              ((,flag 'term) (,x (third (logic.function-args ,x))))))
            ((and (equal ,flag 'term)
                  (logic.functionp ,x)
                  (not (and (equal (logic.function-name ,x) 'if)
                            (equal (len (logic.function-args ,x)) 3))))
             (((,flag 'list) (,x (logic.function-args ,x)))))
            ((and (equal ,flag 'term)
                  (logic.lambdap ,x))
             (((,flag 'list) (,x (logic.lambda-actuals ,x)))))
            ((and (equal ,flag 'term)
                  (not (or (logic.constantp ,x)
                           (logic.variablep ,x)
                           (logic.functionp ,x)
                           (logic.lambdap ,x))))
             nil)
            ((and (not (equal ,flag 'term))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (consp ,x))
             (((,flag 'term) (,x (car ,x)))
              ((,flag 'list) (,x (cdr ,x)))))))

(%autoprove clause.simple-term-listp-when-not-consp
            (%restrict default definition-of-clause.simple-term-listp (equal x 'x)))

(%autoprove clause.simple-term-listp-of-cons
            (%restrict default definition-of-clause.simple-term-listp (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-clause.simple-termp
            (%clause.simple-term-induction flag x))

(%autoprove booleanp-of-clause.simple-termp
            (%use (%instance (%thm lemma-for-booleanp-of-clause.simple-termp)
                             (flag 'term))))

(%autoprove booleanp-of-clause.simple-term-listp
            (%use (%instance (%thm lemma-for-booleanp-of-clause.simple-termp)
                             (flag 'list))))

(%deflist clause.simple-term-listp (x)
          (clause.simple-termp x))


(%autoprove clause.simple-term-listp-when-length-three)

(%deflist clause.simple-term-list-listp (x)
          (clause.simple-term-listp x))



(%create-theory clause.simple-termp-openers)
(%enable clause.simple-termp-openers
         clause.simple-termp-when-logic.variablep
         clause.simple-termp-when-logic.constantp
         clause.simple-termp-when-non-if-logic.functionp
         clause.simple-termp-when-bad-args-logic.functionp
         clause.simple-termp-when-if-logic.functionp
         clause.simple-termp-when-logic.lambdap
         clause.simple-termp-when-degenerate)


(%ensure-exactly-these-rules-are-missing "../../clauses/if-lifting/simple-termp")

