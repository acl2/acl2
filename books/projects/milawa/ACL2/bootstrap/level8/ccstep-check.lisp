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
(include-book "ccsteps")
(include-book "ccstep-arities")
(%interactive)


(%autoprove forcing-rw.hypbox-listp-of-rw.ccstep-list-hypboxes
            (%cdr-induction x))

(%autoprove forcing-logic.term-listp-of-rw.ccstep-list-terms
            (%cdr-induction x))

(%autoprove forcing-rw.trace-listp-of-rw.ccstep-list-gather-traces
            (%cdr-induction x))

(%autoprove forcing-rw.eqtrace-listp-of-rw.ccstep-list-gather-contradictions
            (%cdr-induction x))

(%autoprove forcing-logic.formulap-of-rw.ccstep-list->original-goal
            (%cdr-induction x)
            (%restrict default rw.ccstep-list->original-goal (equal x 'x))
            (%enable default rw.ccstep->original-goal))

(%autoprove logic.provable-listp-of-remove-duplicates-when-logic.provable-listp-free)



(defsection rw.ccstep-list-bldr-okp

  (%autoadmit rw.ccstep-list-bldr-okp)
  (%autoadmit rw.ccstep-list-bldr-high)

  (local (%enable default
                  rw.ccstep-list-bldr-okp
                  rw.ccstep-list-bldr-high))

  (%autoprove rw.ccstep-list-bldr-okp-of-rw.ccstep-list-bldr-high)

  (local (%disable default
                   expensive-arithmetic-rules
                   expensive-arithmetic-rules-two
                   memberp-when-not-consp
                   memberp-when-not-subset-of-somep-cheap
                   memberp-when-not-superset-of-somep-cheap
                   memberp-when-memberp-of-cdr
                   in-superset-when-in-subset-one
                   not-in-subset-when-not-in-superset-two
                   subset-of-somep-when-obvious-alt
                   superset-of-somep-when-obvious-alt
                   memberp-when-logic.all-terms-larger-cheap))

  (%autoprove booleanp-of-rw.ccstep-list-bldr-okp)
  (%autoprove rw.ccstep-list-bldr-okp-of-logic.appeal-identity)
  (%autoprove lemma-1-for-soundness-of-rw.ccstep-list-bldr-okp)
  (%autoprove lemma-2-for-soundness-of-rw.ccstep-list-bldr-okp)

  (%autoprove forcing-soundness-of-rw.ccstep-list-bldr-okp
              (%use (%instance (%thm lemma-1-for-soundness-of-rw.ccstep-list-bldr-okp)))
              (%use (%instance (%thm lemma-2-for-soundness-of-rw.ccstep-list-bldr-okp)))
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (rw.ccstep-list-bldr (logic.extras x)
                                                       defs
                                                       (if (rw.ccstep->provedp (first (logic.extras x)))
                                                           nil
                                                         (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                                                                 axioms thms atbl))
                                                       (logic.provable-list-witness (RW.CCSTEP-LIST-FORCED-GOALS (LOGIC.EXTRAS X))
                                                                                    axioms thms atbl)))))))


(%ensure-exactly-these-rules-are-missing "../../rewrite/ccstep-check")

