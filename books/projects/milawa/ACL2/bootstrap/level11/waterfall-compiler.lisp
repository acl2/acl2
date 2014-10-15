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
(include-book "waterfall-steps")
(%interactive)


(%autoadmit rw.stop-waterstep-compiler)
(encapsulate
 ()
 (local (%enable default
                 rw.stop-waterstep-compiler
                 rw.stop-waterstep-okp))
 (local (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))
 (%autoprove logic.appealp-of-rw.stop-waterstep-compiler)
 (%autoprove logic.conclusion-of-rw.stop-waterstep-compiler)
 (%autoprove logic.proofp-of-rw.stop-waterstep-compiler))


(%autoadmit rw.urewrite-waterstep-compiler)
(encapsulate
 ()
 (local (%enable default
                 rw.urewrite-waterstep-compiler
                 rw.urewrite-waterstep-okp))
 (local (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))
 (local (%disable default
                  formula-decomposition
                  expensive-term/formula-inference
                  type-set-like-rules
                  unusual-memberp-rules
                  unusual-subsetp-rules
                  expensive-arithmetic-rules
                  expensive-arithmetic-rules-two
                  MEMBERP-WHEN-MEMBERP-OF-CDR
                  MEMBERP-WHEN-NOT-CONSP
                  same-length-prefixes-equal-cheap
                  CAR-WHEN-MEMBERP-OF-SINGLETON-LIST-CHEAP
                  CAR-WHEN-MEMBERP-AND-NOT-MEMBERP-OF-CDR-CHEAP
                  ))
 (%autoprove logic.appealp-of-rw.urewrite-waterstep-compiler)
 (%autoprove logic.conclusion-of-rw.urewrite-waterstep-compiler)
 (%autoprove logic.proofp-of-rw.urewrite-waterstep-compiler))


(%autoadmit rw.crewrite-waterstep-compiler)
(encapsulate
 ()
 (local (%enable default
                 rw.crewrite-waterstep-compiler
                 rw.crewrite-waterstep-okp))
 (local (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))
 (local (%disable default
                  formula-decomposition
                  expensive-term/formula-inference
                  type-set-like-rules
                  unusual-memberp-rules
                  unusual-subsetp-rules
                  expensive-arithmetic-rules
                  expensive-arithmetic-rules-two
                  MEMBERP-WHEN-MEMBERP-OF-CDR
                  MEMBERP-WHEN-NOT-CONSP
                  same-length-prefixes-equal-cheap
                  CAR-WHEN-MEMBERP-OF-SINGLETON-LIST-CHEAP
                  CAR-WHEN-MEMBERP-AND-NOT-MEMBERP-OF-CDR-CHEAP
                  ))
 (%autoprove logic.appealp-of-rw.crewrite-waterstep-compiler)
 (%autoprove logic.conclusion-of-rw.crewrite-waterstep-compiler)
 (%autoprove logic.proofp-of-rw.crewrite-waterstep-compiler))


(%autoadmit rw.split-waterstep-compiler)
(encapsulate
 ()
 (local (%enable default
                 rw.split-waterstep-okp
                 rw.split-waterstep-compiler))
 (local (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))
 (%autoprove logic.appealp-of-rw.split-waterstep-compiler)
 (%autoprove logic.conclusion-of-rw.split-waterstep-compiler)
 (%autoprove logic.proofp-of-rw.split-waterstep-compiler))



(%autoadmit rw.flag-waterstep-compiler)
(%autoadmit rw.waterstep-compiler)
(%autoadmit rw.waterstep-list-compiler)
(%autoprove definition-of-rw.waterstep-compiler
            (%restrict default rw.flag-waterstep-compiler (equal x 'x))
            (%enable default rw.waterstep-list-compiler rw.waterstep-compiler))
(%autoprove definition-of-rw.waterstep-list-compiler
            (%restrict default rw.flag-waterstep-compiler (equal x 'x))
            (%enable default rw.waterstep-list-compiler rw.waterstep-compiler))
(%autoprove rw.flag-waterstep-compiler-of-clause
            (%enable default rw.waterstep-compiler))
(%autoprove rw.flag-waterstep-compiler-of-list
            (%enable default rw.waterstep-list-compiler))

(%autoprove rw.waterstep-compiler-of-nil
            (%restrict default definition-of-rw.waterstep-compiler (equal x ''nil)))

(%autoprove rw.waterstep-list-compiler-when-not-consp
            (%restrict default definition-of-rw.waterstep-list-compiler (equal x 'x)))

(%autoprove rw.waterstep-list-compiler-of-cons
            (%restrict default definition-of-rw.waterstep-list-compiler (equal x '(cons a x))))

(%defprojection
 :list (rw.waterstep-list-compiler x world rproofs)
 :element (rw.waterstep-compiler x world rproofs)
 :nil-preservingp t)

(%autoprove lemma-for-logic.appealp-of-rw.waterstep-compiler
            (%autoinduct rw.waterstep-induction flag x)
            (%disable default
                      formula-decomposition
                      expensive-term/formula-inference
                      type-set-like-rules
                      unusual-memberp-rules
                      unusual-subsetp-rules
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      same-length-prefixes-equal-cheap)
            (%forcingp nil)
            (%waterfall default 40)

            (%restrict default definition-of-rw.waterstep-compiler (equal x 'x))
            (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x))
            (%restrict default definition-of-rw.waterstep-okp (equal x 'x))
            (%waterfall default 40)

            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference
                     type-set-like-rules
                     unusual-memberp-rules
                     unusual-subsetp-rules
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     same-length-prefixes-equal-cheap)

            (%waterfall default 40)
            (%auto))

(%autoprove logic.appealp-of-rw.waterstep-compiler
            (%use (%instance (%thm lemma-for-logic.appealp-of-rw.waterstep-compiler)
                             (flag 'clause))))

(%autoprove logic.conclusion-of-rw.waterstep-compiler
            (%use (%instance (%thm lemma-for-logic.appealp-of-rw.waterstep-compiler)
                             (flag 'clause))))

(%autoprove logic.appeal-listp-of-rw.waterstep-list-compiler
            (%use (%instance (%thm lemma-for-logic.appealp-of-rw.waterstep-compiler)
                             (flag 'list))))

(%autoprove logic.strip-conclusions-of-rw.waterstep-list-compiler
            (%use (%instance (%thm lemma-for-logic.appealp-of-rw.waterstep-compiler)
                             (flag 'list))))

(%autoprove lemma-for-logic.proofp-of-rw.waterstep-compiler
            (%autoinduct rw.waterstep-induction flag x)
            (%disable default
                      formula-decomposition
                      expensive-term/formula-inference
                      type-set-like-rules
                      unusual-memberp-rules
                      unusual-subsetp-rules
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      same-length-prefixes-equal-cheap
                      MEMBERP-WHEN-MEMBERP-OF-CDR
                      MEMBERP-WHEN-NOT-CONSP
                      CAR-WHEN-MEMBERP-AND-NOT-MEMBERP-OF-CDR-CHEAP
                      CAR-WHEN-MEMBERP-OF-SINGLETON-LIST-CHEAP
                      SUBSETP-TRANSITIVE-TWO
                      SUBSETP-OF-REMOVE-DUPLICATES-ONE-INDIRECT
                      SUBSETP-OF-LOGIC.DISJOIN-EACH-FORMULA-LISTS-WHEN-SUBSETP
                      SUBSETP-OF-LOGIC.TERM-LIST-LIST-FORMULASS-WHEN-SUBSETP)
            (%forcingp nil)
            (%liftlimit 2)
            (%splitlimit 5)
            (%waterfall default 40)

            (%restrict default definition-of-rw.waterstep-compiler (equal x 'x))
            (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x))
            (%restrict default definition-of-rw.waterstep-okp (equal x 'x))
            (%waterfall default 40)

            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference
                     type-set-like-rules
                     unusual-memberp-rules
                     unusual-subsetp-rules
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     same-length-prefixes-equal-cheap)

            (%waterfall default 40)
            (%auto))

(%autoprove logic.proofp-of-rw.waterstep-compiler
            (%use (%instance (%thm lemma-for-logic.proofp-of-rw.waterstep-compiler)
                             (flag 'clause))))

(%autoprove logic.proof-listp-of-rw.waterstep-list-compiler
            (%use (%instance (%thm lemma-for-logic.proofp-of-rw.waterstep-compiler)
                             (flag 'list))))
