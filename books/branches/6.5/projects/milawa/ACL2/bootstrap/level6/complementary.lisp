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
(include-book "simple-negativep")
(%interactive)

(local (%enable default lemma-split-up-list-of-quoted-nil))

(%autoadmit clause.complement-term)

(%autoprove logic.termp-of-clause.complement-term
            (%enable default clause.complement-term))

(%autoprove clause.complement-term-of-clause.complement-term
            (%enable default clause.complement-term))




(%autoadmit clause.find-complementary-literal)

(%autoprove clause.find-complementary-literal-when-not-consp
            (%restrict default clause.find-complementary-literal (equal x 'x)))

(%autoprove clause.find-complementary-literal-of-cons
            (%restrict default clause.find-complementary-literal (equal x '(cons a x))))

(%autoprove forcing-memberp-of-clause.find-complementary-literal
            (%cdr-induction x))

(%autoprove forcing-memberp-of-not-of-clause.find-complementary-literal
            (%cdr-induction x))

(%autoprove clause.find-complementary-literal-of-list-fix
            (%cdr-induction x))

(%autoprove forcing-clause.find-complementary-literal-of-app-one
            (%cdr-induction x))

(%autoprove lemma-for-clause.find-complementary-literal-of-rev
            (%cdr-induction x))

(%autoprove clause.find-complementary-literal-of-rev
            (%cdr-induction x)
            (%enable default lemma-for-clause.find-complementary-literal-of-rev))



(%autoadmit clause.remove-complement-clauses)

(%autoprove clause.remove-complement-clauses-when-not-consp
            (%restrict default clause.remove-complement-clauses (equal x 'x)))

(%autoprove clause.remove-complement-clauses-of-cons
            (%restrict default clause.remove-complement-clauses (equal x '(cons a x))))

(%autoprove forcing-logic.term-list-listp-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove cons-listp-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove true-listp-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove clause.remove-complement-clauses-of-list-fix
            (%cdr-induction x))

(%autoprove clause.remove-complement-clauses-of-app
            (%cdr-induction x))

(%autoprove rev-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove clause.remove-complement-clauses-of-rev)




(defsection clause.complement-clause-bldr
  (%autoadmit clause.complement-clause-bldr)
  (local (%enable default
                  clause.complement-clause-bldr
                  clause.complement-term
                  theorem-not-when-nil))
  (%autoprove forcing-logic.appealp-of-clause.complement-clause-bldr)
  (%autoprove forcing-logic.conclusion-of-clause.complement-clause-bldr)
  (%autoprove forcing-logic.proofp-of-clause.complement-clause-bldr))




(%autoadmit clause.remove-complement-clauses-bldr)

(%autoprove forcing-logic.appeal-listp-of-clause.remove-complement-clauses-bldr
            (%autoinduct clause.remove-complement-clauses-bldr)
            (%restrict default clause.remove-complement-clauses (equal x 'x))
            (%restrict default clause.remove-complement-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-clause.remove-complement-clauses-bldr
            (%autoinduct clause.remove-complement-clauses-bldr)
            (%restrict default clause.remove-complement-clauses (equal x 'x))
            (%restrict default clause.remove-complement-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-clause.remove-complement-clauses-bldr
            (%autoinduct clause.remove-complement-clauses-bldr)
            (%restrict default clause.remove-complement-clauses (equal x 'x))
            (%restrict default clause.remove-complement-clauses-bldr (equal x 'x)))
