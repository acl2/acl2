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

(%autoadmit clause.unlifted-subterms)

(%autoprove consp-of-clause.unlifted-subterms
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-logic.constantp
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-logic.variablep
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-non-if-logic.functionp
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-bad-args-logic.functionp
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-if-logic.functionp
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-logic.lambdap
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-degenerate
            (%restrict default clause.unlifted-subterms (equal x 'x)))


(defmacro %clause.unlifted-subterms-induction (x)
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
                  (or (not (equal (logic.function-name ,x) 'if))
                      (not (equal (len (logic.function-args ,x)) 3))))
             nil)
            ((logic.lambdap ,x)
             nil)
            ((and (not (logic.constantp ,x))
                  (not (logic.variablep ,x))
                  (not (logic.functionp ,x))
                  (not (logic.lambdap ,x)))
             nil)))

(%autoprove true-listp-of-clause.unlifted-subterms
            (%clause.unlifted-subterms-induction x))

(%autoprove forcing-logic.term-listp-of-clause.unlifted-subterms
            (%clause.unlifted-subterms-induction x))

(%autoprove clause.unlifted-subterms-when-clause.simple-termp
            (%clause.unlifted-subterms-induction x))

(%autoprove clause.simple-termp-when-memberp-of-clause.unlifted-subterms
            (%clause.unlifted-subterms-induction x)
            ;; speed hint
            (%disable default in-superset-when-in-subset-two
                      not-in-subset-when-not-in-superset-one
                      subsetp-transitive-two
                      subsetp-when-prefixp-cheap
                      subsetp-when-ordered-subsetp
                      memberp-when-memberp-of-cdr
                      clause.simple-termp-when-memberp-of-clause.simple-term-listp-alt))

(%autoprove clause.unlifted-subterms-under-iff
            (%clause.unlifted-subterms-induction x)
            ;; speed hint
            (%disable default
                      clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                      clause.unlifted-subterms-when-clause.simple-termp
                      clause.lifted-termp-when-clause.simple-termp))

(%autoprove clause.simple-term-listp-of-clause.unlifted-subterms
            (%clause.unlifted-subterms-induction x)
            (%disable default
                      clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                      clause.unlifted-subterms-when-clause.simple-termp
                      clause.lifted-termp-when-clause.simple-termp))





(%autoadmit clause.unlifted-subterms-list)

(%autoprove clause.unlifted-subterms-list-when-not-consp
            (%restrict default clause.unlifted-subterms-list (equal x 'x)))

(%autoprove clause.unlifted-subterms-list-of-cons
            (%restrict default clause.unlifted-subterms-list (equal x '(cons a x))))

(%autoprove true-listp-of-clause.unlifted-subterms-list
            (%cdr-induction x))

(%autoprove consp-of-clause.unlifted-subterms-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-listp-of-clause.unlifted-subterms-list
            (%cdr-induction x))

(%autoprove clause.unlifted-subterms-list-of-list-fix
            (%cdr-induction x))

(%autoprove clause.unlifted-subterms-list-of-app
            (%cdr-induction x))

(%autoprove clause.simple-termp-when-memberp-of-clause.unlifted-subterms-list
            (%cdr-induction x))

(%autoprove clause.unlifted-subterms-list-under-iff
            (%cdr-induction x))

(%autoprove clause.simple-term-listp-of-clause.unlifted-subterms-list
            (%cdr-induction x))


(%create-theory clause.unlifted-subterms-openers)
(%enable clause.unlifted-subterms-openers
         clause.unlifted-subterms-when-logic.constantp
         clause.unlifted-subterms-when-logic.variablep
         clause.unlifted-subterms-when-non-if-logic.functionp
         clause.unlifted-subterms-when-bad-args-logic.functionp
         clause.unlifted-subterms-when-if-logic.functionp
         clause.unlifted-subterms-when-logic.lambdap
         clause.unlifted-subterms-when-degenerate)
