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
(include-book "formula-compiler")
(include-book "clause-basics")
(%interactive)


(%autoadmit clause.make-clause-from-arbitrary-formula)

(%autoprove consp-of-clause.make-clause-from-arbitrary-formula
            (%enable default clause.make-clause-from-arbitrary-formula))

(%autoprove forcing-logic.term-listp-of-clause.make-clause-from-arbitrary-formula
            (%enable default clause.make-clause-from-arbitrary-formula))

(%autoprove forcing-logic.term-list-atblp-of-clause.make-clause-from-arbitrary-formula
            (%enable default clause.make-clause-from-arbitrary-formula))

(%autoadmit clause.prove-arbitrary-formula-from-its-clause)

(encapsulate
 ()
 (local (%enable default
                clause.prove-arbitrary-formula-from-its-clause
                clause.make-clause-from-arbitrary-formula
                logic.term-formula))
 (%autoprove forcing-logic.appealp-of-clause.prove-arbitrary-formula-from-its-clause)
 (%autoprove forcing-logic.conclusion-of-clause.prove-arbitrary-formula-from-its-clause)
 (%autoprove forcing-logic.proofp-of-clause.prove-arbitrary-formula-from-its-clause))



(%defprojection :list (clause.make-clauses-from-arbitrary-formulas x)
                :element (clause.make-clause-from-arbitrary-formula x)
                :nil-preservingp nil)

(%autoprove consp-listp-of-clause.make-clauses-from-arbitrary-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-listp-of-clause.make-clauses-from-arbitrary-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-clause.make-clauses-from-arbitrary-formulas
            (%cdr-induction x))


(%autoadmit clause.prove-arbitrary-formulas-from-their-clauses)

(%autoprove forcing-logic.appeal-listp-of-clause.prove-arbitrary-formulas-from-their-clauses
            (%autoinduct clause.prove-arbitrary-formulas-from-their-clauses)
            (%restrict default clause.prove-arbitrary-formulas-from-their-clauses
                       (equal fs 'fs)))

(%autoprove forcing-logic.strip-conclusions-of-clause.prove-arbitrary-formulas-from-their-clauses
            (%autoinduct clause.prove-arbitrary-formulas-from-their-clauses)
            (%restrict default clause.prove-arbitrary-formulas-from-their-clauses
                       (equal fs 'fs)))

(%autoprove forcing-logic.proofp-of-clause.prove-arbitrary-formulas-from-their-clauses
            (%autoinduct clause.prove-arbitrary-formulas-from-their-clauses)
            (%restrict default clause.prove-arbitrary-formulas-from-their-clauses
                       (equal fs 'fs)))




(%autoadmit clause.prove-arbitrary-formula-from-its-clause-okp)

(%autoadmit clause.prove-arbitrary-formula-from-its-clause-high)
(%autoprove clause.prove-arbitrary-formula-from-its-clause-okp-of-clause.prove-arbitrary-formula-from-its-clause-high
            (%enable default clause.prove-arbitrary-formula-from-its-clause-okp
                     clause.prove-arbitrary-formula-from-its-clause-high))


(%autoprove hack-for-compile-formula-okp-1
            (%autoinduct logic.compile-formula f)
            (%restrict default logic.compile-formula (equal x 'f))

            (%disable default
                      FORCING-LOGIC.FORMULA-ATBLP-OF-LOGIC.VRHS
                      FORCING-LOGIC.FORMULA-ATBLP-OF-LOGIC.VLHS
                      FORCING-LOGIC.FORMULA-ATBLP-OF-LOGIC.~ARG
                      FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.=RHS
                      FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.=LHS
                      FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.FUNCTION
                      FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.COMPILE-FORMULA)

            (%restrict default logic.formula-atblp (equal x 'f))

            (%restrict default definition-of-logic.term-atblp
                       (or (equal x '(LOGIC.FUNCTION 'IF
                                                     (CONS (LOGIC.COMPILE-FORMULA (LOGIC.~ARG F))
                                                           '('NIL 'T))))
                           (equal x '(LOGIC.FUNCTION 'EQUAL
                                                     (CONS (LOGIC.=LHS F)
                                                           (CONS (LOGIC.=RHS F) 'nil))))
                           (equal x '(LOGIC.FUNCTION 'IF
                                                     (CONS (LOGIC.COMPILE-FORMULA (LOGIC.VLHS F))
                                                           (CONS ''T
                                                                 (CONS (LOGIC.COMPILE-FORMULA (LOGIC.VRHS F))
                                                                       'NIL)))))))

            (%forcingp nil))

(%autoprove hack-for-compile-formula-okp-2
            (%enable default
                     clause.make-clause-from-arbitrary-formula
                     clause.prove-arbitrary-formula-from-its-clause-okp
                     logic.term-formula)
            (%disable default
                      logic.formula-atblp-when-logic.provablep
                      logic.formula-list-atblp-of-when-logic.provable-listp)
            (%forcingp nil)
            (%use (%instance (%thm logic.formula-atblp-when-logic.provablep)
                             (x (logic.conclusion (car (logic.subproofs x))))))
            (%use (%instance (%thm hack-for-compile-formula-okp-1)
                             (f (logic.conclusion x))))
            (%auto)
            (%fertilize (logic.compile-formula (logic.conclusion x))
                        (logic.=lhs
                         (logic.~arg (logic.conclusion (car (logic.subproofs x)))))))

(encapsulate
 ()
 (local (%enable default clause.prove-arbitrary-formula-from-its-clause-okp))

 (%autoprove booleanp-of-clause.prove-arbitrary-formula-from-its-clause-okp)
 (%autoprove clause.prove-arbitrary-formula-from-its-clause-okp-of-logic.appeal-identity)

 (%autoprove lemma-1-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp)

 (%autoprove lemma-2-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp
             (%enable default hack-for-compile-formula-okp-2))

 (%autoprove forcing-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp
             (%enable default
                      lemma-1-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp
                      lemma-2-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp)
             (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                              (x (clause.prove-arbitrary-formula-from-its-clause
                                  (logic.conclusion x)
                                  (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                                          axioms thms atbl)))))))


(%ensure-exactly-these-rules-are-missing "../../clauses/compiler")