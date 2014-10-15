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
(include-book "simple-termp")
(%interactive)

(%autoadmit clause.lifted-termp)

(%autoprove clause.lifted-termp-when-logic.constantp
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-logic.variablep
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-not-if
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-bad-args-logic.functionp
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-if-logic.functionp
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-if-logic.lambdap
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-degenerate
            (%restrict default clause.lifted-termp (equal x 'x)))

(defmacro %clause.lifted-termp-induction (x)
  `(%induct (rank ,x)
            ((logic.constantp ,x) nil)
            ((logic.variablep ,x) nil)
            ((and (logic.functionp ,x)
                  (equal (logic.function-name ,x) 'if)
                  (equal (len (logic.function-args ,x)) 3))
             (((,x (first (logic.function-args ,x))))
              ((,x (second (logic.function-args ,x))))
              ((,x (third (logic.function-args ,x))))))
            ((and (logic.functionp ,x)
                  (not (and (equal (logic.function-name ,x) 'if)
                            (equal (len (logic.function-args ,x)) 3))))
             nil)
            ((logic.lambdap ,x) nil)
            ((not (or (logic.constantp ,x)
                      (logic.variablep ,x)
                      (logic.functionp ,x)
                      (logic.lambdap ,x)))
             nil)))

(%autoprove clause.lifted-termp-when-clause.simple-termp
            (%clause.lifted-termp-induction x))

(%autoprove booleanp-of-clause.lifted-termp
            (%clause.lifted-termp-induction x))

(%deflist clause.lifted-term-listp (x)
          (clause.lifted-termp x))

(%ensure-exactly-these-rules-are-missing "../../clauses/if-lifting/lifted-termp")

(%create-theory clause.lifted-termp-openers)
(%enable clause.lifted-termp-openers
         clause.lifted-termp-when-logic.constantp
         clause.lifted-termp-when-logic.variablep
         clause.lifted-termp-when-not-if
         clause.lifted-termp-when-bad-args-logic.functionp
         clause.lifted-termp-when-if-logic.functionp
         clause.lifted-termp-when-if-logic.lambdap
         clause.lifted-termp-when-degenerate)
