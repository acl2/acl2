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
(include-book "trace-compiler")
(%interactive)

(defsection rw.ccstepp

  (%autoadmit rw.ccstepp)
  (%autoadmit rw.ccstep->term)
  (%autoadmit rw.ccstep->hypbox)
  (%autoadmit rw.ccstep->contradiction)
  (%autoadmit rw.ccstep->trace)
  (%autoadmit rw.ccstep)

  (local (%enable default
                  rw.ccstepp
                  rw.ccstep
                  rw.ccstep->term
                  rw.ccstep->hypbox
                  rw.ccstep->contradiction
                  rw.ccstep->trace))

  (%autoprove booleanp-of-rw.ccstepp)
  (%autoprove forcing-rw.ccstepp-of-rw.ccstep)
  (%autoprove rw.ccstep->term-of-rw.ccstep)
  (%autoprove rw.ccstep->hypbox-of-rw.ccstep)
  (%autoprove rw.ccstep->contradiction-of-rw.ccstep)
  (%autoprove rw.ccstep->trace-of-rw.ccstep)
  (%autoprove forcing-logic.termp-of-rw.ccstep->term)
  (%autoprove forcing-rw.hypboxp-of-rw.ccstep->hypbox)
  (%autoprove forcing-rw.eqtracep-of-rw.ccstep->contradiction)
  (%autoprove forcing-rw.eqtrace-contradictionp-of-rw.ccstep->contradiction)
  (%autoprove forcing-rw.eqtrace-okp-of-rw.ccstep->contradiction)
  (%autoprove forcing-rw.hypbox->right-of-rw.ccstep->hypbox-when-rw.ccstep->contradiction)
  (%autoprove forcing-rw.tracep-of-rw.ccstep->trace)
  (%autoprove forcing-rw.trace->iffp-of-rw.ccstep->trace)
  (%autoprove forcing-rw.trace->hypbox-of-rw.ccstep->trace)
  (%autoprove forcing-rw.trace->lhs-of-rw.ccstep->trace))


(%deflist rw.ccstep-listp (x)
          (rw.ccstepp x))

(%deflist rw.ccstep-list-listp (x)
          (rw.ccstep-listp x))


(%defprojection :list (rw.ccstep-list-terms x)
                :element (rw.ccstep->term x)
                :nil-preservingp t)

(%defprojection :list (rw.ccstep-list-list-terms x)
                :element (rw.ccstep-list-terms x)
                :nil-preservingp t)

(%defprojection :list (rw.ccstep-list-hypboxes x)
                :element (rw.ccstep->hypbox x)
                :nil-preservingp t)

(%defprojection :list (rw.ccstep-list-list-hypboxes x)
                :element (rw.ccstep-list-hypboxes x)
                :nil-preservingp t)


(defsection rw.ccstep-list-gather-traces
  (%autoadmit rw.ccstep-list-gather-traces)
  (%autoprove rw.ccstep-list-gather-traces-when-not-consp
              (%restrict default rw.ccstep-list-gather-traces (equal x 'x)))
  (%autoprove rw.ccstep-list-gather-traces-of-cons
              (%restrict default rw.ccstep-list-gather-traces (equal x '(cons a x))))
  (%autoprove true-listp-of-rw.ccstep-list-gather-traces
              (%cdr-induction x)))

(defsection rw.ccstep-list-list-gather-traces
  (%autoadmit rw.ccstep-list-list-gather-traces)
  (%autoprove rw.ccstep-list-list-gather-traces-when-not-consp
              (%restrict default rw.ccstep-list-list-gather-traces (equal x 'x)))
  (%autoprove true-listp-of-rw.ccstep-list-list-gather-traces
              (%cdr-induction x)
              (%restrict default rw.ccstep-list-list-gather-traces (equal x 'x)))
  (%autoprove rw.ccstep-list-list-gather-traces-of-cons
              (%restrict default rw.ccstep-list-list-gather-traces (equal x '(cons a x)))))

(defsection rw.ccstep-list-gather-contradictions
  (%autoadmit rw.ccstep-list-gather-contradictions)
  (%autoprove rw.ccstep-list-gather-contradictions-when-not-consp
              (%restrict default rw.ccstep-list-gather-contradictions (equal x 'x)))
  (%autoprove rw.ccstep-list-gather-contradictions-of-cons
              (%restrict default rw.ccstep-list-gather-contradictions (equal x '(cons a x))))
  (%autoprove true-listp-of-rw.ccstep-list-gather-contradictions
              (%cdr-induction x)))

(defsection rw.ccstep-list-list-gather-contradictions
  (%autoadmit rw.ccstep-list-list-gather-contradictions)
  (%autoprove rw.ccstep-list-list-gather-contradictions-when-not-consp
              (%restrict default rw.ccstep-list-list-gather-contradictions (equal x 'x)))
  (%autoprove true-listp-of-rw.ccstep-list-list-gather-contradictions
              (%cdr-induction x)
              (%restrict default rw.ccstep-list-list-gather-contradictions (equal x 'x)))
  (%autoprove rw.ccstep-list-list-gather-contradictions-of-cons
              (%restrict default rw.ccstep-list-list-gather-contradictions (equal x '(cons a x)))))


(%autoadmit rw.ccstep->provedp)
(%autoadmit rw.ccstep->terminalp)

(%autoprove rw.ccstep->terminalp-when-rw.ccstep->provedp
            (%enable default rw.ccstep->terminalp rw.ccstep->provedp))


(%autoadmit rw.ccstep->original-goal)
(%autoadmit rw.ccstep->result-goal)
(%autoadmit rw.ccstep->clause-prime)

(%autoprove booleanp-of-rw.ccsetp->provedp
            ;; BOZO misnamed
            (%enable default rw.ccstep->provedp))

(%autoprove forcing-logic.term-listp-of-rw.ccstep->clause-prime
            (%enable default rw.ccstep->clause-prime))

(%autoprove forcing-true-listp-of-rw.ccstep->clause-prime
            (%enable default rw.ccstep->clause-prime))

(%autoprove forcing-rw.ccstep->result-goal-when-rw.ccstep->terminalp
            (%enable default rw.ccstep->result-goal rw.ccstep->terminalp rw.ccstep->provedp rw.ccstep->clause-prime))


(%autoadmit rw.ccstep->t1prime)

(%autoprove forcing-logic.termp-of-rw.ccstep->t1prime
            (%enable default rw.ccstep->provedp rw.ccstep->t1prime))

(%autoprove forcing-logic.term-atblp-of-rw.ccstep->t1prime
            (%enable default rw.ccstep->provedp rw.ccstep->t1prime))



(defsection rw.ccstep-forced-goals
  (%autoadmit rw.ccstep-forced-goals)
  (local (%enable default rw.ccstep-forced-goals))
  (%autoprove true-listp-of-rw.ccstep-forced-goals)
  (%autoprove rw.ccstep-forced-goals-when-contradiction)
  (%autoprove forcing-logic.formula-listp-of-rw.ccstep-forced-goals)
  (%autoprove forcing-logic.formula-list-atblp-of-rw.ccstep-forced-goals))



(defsection rw.fast-ccstep-list-forced-goals
  ;(%autoadmit rw.fast-ccstep-list-forced-goals)
  (%autoadmit rw.ccstep-list-forced-goals)
  ;(%autoadmit rw.slow-ccstep-list-forced-goals)
  ;(%autoprove lemma-1-for-definition-of-rw.crewrite-clause-step-list-forced-goals
  ;            (%autoinduct rw.fast-ccstep-list-forced-goals)
  ;            (%restrict default rw.fast-ccstep-list-forced-goals (equal x 'x)))
  ;(%autoprove lemma-2-for-definition-of-rw.crewrite-clause-step-list-forced-goals
  ;            (%autoinduct rw.fast-ccstep-list-forced-goals)
  ;            (%restrict default rw.fast-ccstep-list-forced-goals (equal x 'x))
  ;            (%restrict default rw.slow-ccstep-list-forced-goals (equal x 'x))
  ;            (%enable default
  ;                     rw.ccstep-forced-goals
  ;                     lemma-1-for-definition-of-rw.crewrite-clause-step-list-forced-goals))
  ;(%autoprove lemma-3-for-definition-of-rw.crewrite-clause-step-list-forced-goals
  ;            (%autoinduct rw.slow-ccstep-list-forced-goals)
  ;            (%restrict default rw.slow-ccstep-list-forced-goals (equal x 'x)))
  ;(%autoprove definition-of-rw.crewrite-clause-step-list-forced-goals
  ;            (%enable default
  ;                     lemma-1-for-definition-of-rw.crewrite-clause-step-list-forced-goals
  ;                     lemma-2-for-definition-of-rw.crewrite-clause-step-list-forced-goals
  ;                     lemma-3-for-definition-of-rw.crewrite-clause-step-list-forced-goals
  ;                     rw.ccstep-list-forced-goals)
  ;            (%restrict default rw.slow-ccstep-list-forced-goals (equal x 'x)))
  ;(%autoprove rw.fast-ccstep-list-forced-goals-removal
  ;            (%enable default
  ;                     rw.ccstep-list-forced-goals
  ;                     lemma-1-for-definition-of-rw.crewrite-clause-step-list-forced-goals
  ;                     lemma-2-for-definition-of-rw.crewrite-clause-step-list-forced-goals
  ;                     lemma-3-for-definition-of-rw.crewrite-clause-step-list-forced-goals))
  (%autoprove true-listp-of-rw.crewrite-clause-step-list-forced-goals
              (%cdr-induction x)
              (%restrict default rw.ccstep-list-forced-goals (equal x 'x)))
  (%autoprove rw.ccstep-list-forced-goals-when-not-consp
              (%restrict default rw.ccstep-list-forced-goals (equal x 'x)))
  (%autoprove rw.ccstep-list-forced-goals-of-cons
              (%restrict default rw.ccstep-list-forced-goals (equal x '(cons a x))))
  (%autoprove rw.ccstep-list-forced-goals-of-list-fix
              (%cdr-induction x))
  (%autoprove rw.ccstep-list-forced-goals-of-app
              (%cdr-induction x))
  (%autoprove logic.formula-listp-of-rw.ccstep-list-forced-goals
              (%cdr-induction x))
  (%autoprove logic.formula-list-atblp-of-rw.ccstep-list-forced-goals
              (%cdr-induction x)))

(defsection rw.fast-ccstep-list-list-forced-goals
  ;(%autoadmit rw.fast-ccstep-list-list-forced-goals)
  (%autoadmit rw.ccstep-list-list-forced-goals)
  ;(%autoadmit rw.slow-ccstep-list-list-forced-goals)
  ;(%autoprove lemma-1-for-definition-of-rw.crewrite-clause-step-list-list-forced-goals
  ;            (%autoinduct rw.fast-ccstep-list-list-forced-goals)
  ;            (%restrict default rw.fast-ccstep-list-list-forced-goals (equal x 'x)))
  ;(%autoprove lemma-2-for-definition-of-rw.crewrite-clause-step-list-list-forced-goals
  ;            (%autoinduct rw.fast-ccstep-list-list-forced-goals)
  ;            (%enable default lemma-1-for-definition-of-rw.crewrite-clause-step-list-list-forced-goals)
  ;            (%restrict default rw.fast-ccstep-list-list-forced-goals (equal x 'x))
  ;            (%restrict default rw.slow-ccstep-list-list-forced-goals (equal x 'x)))
  ;(%autoprove lemma-3-for-definition-of-rw.crewrite-clause-step-list-list-forced-goals
  ;            (%autoinduct rw.slow-ccstep-list-list-forced-goals)
  ;            (%restrict default rw.slow-ccstep-list-list-forced-goals (equal x 'x)))
  ;(%autoprove definition-of-rw.crewrite-clause-step-list-list-forced-goals
  ;            (%autoinduct rw.slow-ccstep-list-list-forced-goals)
  ;            (%enable default
  ;                     rw.ccstep-list-list-forced-goals
  ;                     lemma-1-for-definition-of-rw.crewrite-clause-step-list-list-forced-goals
  ;                     lemma-2-for-definition-of-rw.crewrite-clause-step-list-list-forced-goals
  ;                     lemma-3-for-definition-of-rw.crewrite-clause-step-list-list-forced-goals)
  ;            (%restrict default rw.slow-ccstep-list-list-forced-goals (equal x 'x)))
  ;(%autoprove rw.fast-ccstep-list-list-forced-goals-removal
  ;            (%enable default
  ;                     rw.ccstep-list-list-forced-goals
  ;                     lemma-1-for-definition-of-rw.crewrite-clause-step-list-list-forced-goals
  ;                     lemma-2-for-definition-of-rw.crewrite-clause-step-list-list-forced-goals
  ;                     lemma-3-for-definition-of-rw.crewrite-clause-step-list-list-forced-goals))
  (%autoprove true-listp-of-rw.ccstep-list-list-forced-goals
              (%cdr-induction x)
              (%restrict default rw.ccstep-list-list-forced-goals (equal x 'x)))
  (%autoprove rw.ccstep-list-list-forced-goals-when-not-consp
              (%restrict default rw.ccstep-list-list-forced-goals (equal x 'x)))
  (%autoprove rw.ccstep-list-list-forced-goals-of-cons
              (%restrict default rw.ccstep-list-list-forced-goals (equal x '(cons a x))))
  (%autoprove logic.formula-listp-of-rw.ccstep-list-list-forced-goals
              (%cdr-induction x))
  (%autoprove logic.formula-list-atblp-of-rw.ccstep-list-list-forced-goals
              (%cdr-induction x)))


(defsection rw.proved-ccstep-bldr
  (%autoadmit rw.proved-ccstep-bldr)

  (local (%enable default
                  rw.proved-ccstep-bldr
                  rw.ccstep->result-goal
                  rw.ccstep->provedp
                  rw.ccstep->original-goal
                  rw.ccstep-forced-goals
                  rw.hypbox-formula
                  logic.term-formula
                  rw.trace-formula
                  rw.trace-conclusion-formula))

  (local (%disable default ;; extra speed hint
                   type-set-like-rules
                   expensive-arithmetic-rules
                   expensive-arithmetic-rules-two
                   same-length-prefixes-equal-cheap
                   expensive-term/formula-inference
                   unusual-consp-rules
                   car-when-not-consp
                   cdr-when-not-consp
                   memberp-when-not-consp
                   memberp-when-not-subset-of-somep-cheap
                   memberp-when-not-superset-of-somep-cheap
                   memberp-when-memberp-of-cdr
                   in-superset-when-in-subset-one
                   not-in-subset-when-not-in-superset-two
                   subset-of-somep-when-obvious-alt
                   superset-of-somep-when-obvious-alt
                   memberp-when-logic.all-terms-larger-cheap))

  (%autoprove rw.proved-ccstep-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.proved-ccstep-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.proved-ccstep-bldr)
  (%autoprove forcing-logic.proofp-of-rw.proved-ccstep-bldr))


(defsection rw.usual-ccstep-bldr
  (%autoadmit rw.usual-ccstep-bldr)

  (local (%enable default
                  rw.usual-ccstep-bldr
                  rw.ccstep->result-goal
                  rw.ccstep->provedp
                  rw.ccstep->original-goal
                  rw.ccstep-forced-goals
                  rw.hypbox-formula
                  logic.term-formula
                  rw.trace-formula
                  rw.trace-conclusion-formula))

  (local (%disable default ;; extra speed hint
                   type-set-like-rules
                   expensive-arithmetic-rules
                   expensive-arithmetic-rules-two
                   same-length-prefixes-equal-cheap
                   expensive-term/formula-inference
                   unusual-consp-rules
                   car-when-not-consp
                   cdr-when-not-consp
                   memberp-when-not-consp
                   memberp-when-not-subset-of-somep-cheap
                   memberp-when-not-superset-of-somep-cheap
                   memberp-when-memberp-of-cdr
                   in-superset-when-in-subset-one
                   not-in-subset-when-not-in-superset-two
                   subset-of-somep-when-obvious-alt
                   superset-of-somep-when-obvious-alt
                   memberp-when-logic.all-terms-larger-cheap))

  (%autoprove rw.usual-ccstep-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.usual-ccstep-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.usual-ccstep-bldr)
  (%autoprove forcing-logic.proofp-of-rw.usual-ccstep-bldr))




(%autoadmit rw.ccstep-list->original-goal)

(defsection rw.ccstep-list->none-provedp
  (%autoadmit rw.ccstep-list->none-provedp)
  (%autoprove rw.ccstep-list->none-provedp-when-not-consp
              (%restrict default rw.ccstep-list->none-provedp (equal x 'x)))
  (%autoprove rw.ccstep-list->none-provedp-of-cons
              (%restrict default rw.ccstep-list->none-provedp (equal x '(cons a x))))
  (%autoprove booleanp-of-rw.ccstep-list->none-provedp
              (%cdr-induction x)))

(defsection rw.ccstep-list->compatiblep
  (%autoadmit rw.ccstep-list->compatiblep)
  (%autoprove booleanp-of-rw.ccstep-list->compatiblep
              (%autoinduct rw.ccstep-list->compatiblep)
              (%restrict default rw.ccstep-list->compatiblep (equal x 'x)))
  (%autoprove rw.ccstep-list->compatiblep-when-not-consp
              (%restrict default rw.ccstep-list->compatiblep (equal x 'x)))
  (%autoprove rw.ccstep-list->compatiblep-when-not-of-cdr
              (%restrict default rw.ccstep-list->compatiblep (equal x 'x))))




(defsection rw.usual-ccstep-list-bldr
  (%autoadmit rw.usual-ccstep-list-bldr)
  (local (%enable default rw.ccstep->provedp))
  (local (%restrict default rw.usual-ccstep-list-bldr (equal x 'x)))
  (local (%restrict default rw.ccstep-list->compatiblep (equal x 'x)))
  (local (%restrict default rw.ccstep-list->original-goal (equal x 'x)))
  (local (%disable default ;; extra speed hint
                   type-set-like-rules
                   expensive-arithmetic-rules
                   expensive-arithmetic-rules-two
                   same-length-prefixes-equal-cheap
                   expensive-term/formula-inference
                   unusual-consp-rules
                   car-when-not-consp
                   cdr-when-not-consp
                   memberp-when-not-consp
                   memberp-when-not-subset-of-somep-cheap
                   memberp-when-not-superset-of-somep-cheap
                   memberp-when-memberp-of-cdr
                   in-superset-when-in-subset-one
                   not-in-subset-when-not-in-superset-two
                   subset-of-somep-when-obvious-alt
                   superset-of-somep-when-obvious-alt
                   memberp-when-logic.all-terms-larger-cheap))
  (%autoprove forcing-logic.appealp-of-rw.usual-ccstep-list-bldr
              (%autoinduct rw.usual-ccstep-list-bldr))
  (%autoprove forcing-logic.conclusion-of-rw.usual-ccstep-list-bldr
              (%autoinduct rw.usual-ccstep-list-bldr))
  (%autoprove forcing-logic.proofp-of-rw.usual-ccstep-list-bldr
              (%autoinduct rw.usual-ccstep-list-bldr)))


(defsection rw.ccstep-list-bldr

  (%autoadmit rw.ccstep-list-bldr)

  (local (%enable default rw.ccstep-list-bldr))

  (%autoprove lemma-1-for-rw.ccstep-list-bldr
              (%autoinduct rw.ccstep-list->compatiblep)
              (%restrict default rw.ccstep-list->compatiblep (equal x 'x)))

  (%autoprove lemma-2-for-rw.ccstep-list-bldr
              (%use (%instance (%thm lemma-1-for-rw.ccstep-list-bldr))))

  (local (%enable default lemma-2-for-rw.ccstep-list-bldr))

  (local (%disable default ;; extra speed hint
                   type-set-like-rules
                   expensive-arithmetic-rules
                   expensive-arithmetic-rules-two
                   same-length-prefixes-equal-cheap
                   expensive-term/formula-inference
                   unusual-consp-rules
                   car-when-not-consp
                   cdr-when-not-consp
                   memberp-when-not-consp
                   memberp-when-not-subset-of-somep-cheap
                   memberp-when-not-superset-of-somep-cheap
                   memberp-when-memberp-of-cdr
                   in-superset-when-in-subset-one
                   not-in-subset-when-not-in-superset-two
                   subset-of-somep-when-obvious-alt
                   superset-of-somep-when-obvious-alt
                   memberp-when-logic.all-terms-larger-cheap))

  (%autoprove forcing-logic.appealp-of-rw.ccstep-list-bldr
              (%restrict default rw.ccstep-list->compatiblep (equal x 'x))
              (%restrict default rw.ccstep-list->original-goal (equal x 'x)))

  (%autoprove forcing-logic.conclusion-of-rw.ccstep-list-bldr
              (%restrict default rw.ccstep-list->compatiblep (equal x 'x))
              (%restrict default rw.ccstep-list->original-goal (equal x 'x)))

  (%autoprove forcing-logic.proofp-of-rw.ccstep-list-bldr
              (%restrict default rw.ccstep-list->compatiblep (equal x 'x))
              (%restrict default rw.ccstep-list->original-goal (equal x 'x))))


(%ensure-exactly-these-rules-are-missing "../../rewrite/ccsteps")

