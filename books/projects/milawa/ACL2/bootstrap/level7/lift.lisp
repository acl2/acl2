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
(include-book "lift-term1")
(%interactive)

(%autoadmit clause.lift-term)

(defmacro %clause.lift-term-induction (x)
  `(%induct (clause.depth-list (clause.unlifted-subterms ,x))
            ((not (logic.termp ,x))
             nil)
            ((clause.lifted-termp ,x)
             nil)
            ((and (logic.termp ,x)
                  (not (clause.lifted-termp ,x)))
             (((x (clause.lift-term1 ,x)))))))

(%autoprove forcing-logic.termp-of-clause.lift-term
            (%clause.lift-term-induction x)
            (%restrict default clause.lift-term (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-clause.lift-term
            (%clause.lift-term-induction x)
            (%restrict default clause.lift-term (equal x 'x)))

(%autoprove forcing-clause.lifted-termp-of-clause.lift-term
            (%clause.lift-term-induction x)
            (%restrict default clause.lift-term (equal x 'x)))

(%autoprove clause.lift-term-when-clause.simple-termp
            (%clause.lift-term-induction x)
            (%restrict default clause.lift-term (equal x 'x)))




(%defprojection :list (clause.lift-term-list x)
                :element (clause.lift-term x))

(%autoprove forcing-logic.term-listp-of-clause.lift-term-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-clause.lift-term-list
            (%cdr-induction x))

(%autoprove clause.lift-term-list-when-clause.simple-term-listp
            (%cdr-induction x))

(%autoprove forcing-clause.lifted-term-listp-of-clause.lift-term-list
            (%cdr-induction x))



(%defprojection :list (clause.lift-term-list-list x)
                :element (clause.lift-term-list x))

(%autoprove forcing-logic.term-listp-of-clause.lift-term-list-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-clause.lift-term-list-list
            (%cdr-induction x))

(%autoprove clause.lift-term-list-list-when-clause.simple-term-list-listp
            (%cdr-induction x))

(%autoprove forcing-cons-listp-of-clause.lift-term-list-list
            (%cdr-induction x))

