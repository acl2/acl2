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
(include-book "rewrite-world")
(include-book "urewrite-clause")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defsection rw.world-urewrite-list-bldr
  (%autoadmit rw.world-urewrite-list-bldr)
  (local (%enable default rw.world-urewrite-list-bldr))
  (%autoprove logic.appealp-of-rw.world-urewrite-list-bldr)
  (%autoprove logic.conclusion-of-rw.world-urewrite-list-bldr)
  (%autoprove logic.proofp-of-rw.world-urewrite-list-bldr))


(%autoadmit rw.world-urewrite-list-list-bldr)

(local (%disable default rw.world-urewrite-list-bldr))

(local (%disable default
                 formula-decomposition
                 expensive-term/formula-inference
                 type-set-like-rules
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 expensive-subsetp-rules
                 unusual-memberp-rules
                 unusual-consp-rules
                 unusual-subsetp-rules
                 CONSP-WHEN-TRUE-LISTP-CHEAP
                 LOGIC.TERM-LIST-LISTP-OF-SUBSETP-WHEN-LOGIC.TERM-LIST-LISTP
                 MEMBERP-WHEN-MEMBERP-OF-CDR
                 LOGIC.APPEAL-LISTP-OF-SUBSETP-WHEN-LOGIC.APPEAL-LISTP
                 LOGIC.APPEALP-WHEN-MEMBERP-OF-LOGIC.APPEAL-LISTP
                 LOGIC.DISJOIN-EACH-FORMULA-LIST-WHEN-NOT-CONSP
                 RW.TRACE-LIST-LIST-RHSES-WHEN-NOT-CONSP
                 TRUE-LISTP-OF-CDR
                 LOGIC.TERM-LISTP-WHEN-MEMBERP-OF-LOGIC.TERM-LIST-LISTP
                 LOGIC.TERM-LIST-LISTP-OF-CDR-WHEN-LOGIC.TERM-LIST-LISTP
                 SUBSET-OF-SOMEP-WHEN-FIND-SUPERSET
                 FORCING-PREFIXP-WHEN-NOT-PREFIXP-BADGUY
                 LOGIC.DISJOIN-FORMULAS-WHEN-NOT-CONSP
                 LOGIC.DISJOIN-FORMULAS-WHEN-SINGLETON-LIST
                 LOGIC.TERM-LIST-FORMULAS-WHEN-NOT-CONSP
                 MEMBERP-OF-CAR-IN-CDR-WHEN-UNIQUEP
                 RW.TRACE-LIST-RHSES-WHEN-NOT-CONSP
                 RW.UREWRITE-LIST-WHEN-NOT-CONSP
                 CONS-LISTP-WHEN-NOT-CONSP
                 LOGIC.TERM-LIST-LISTP-WHEN-NOT-CONSP
                 SUBSETP-WHEN-NOT-CONSP
                 SUBSETP-WHEN-NOT-CONSP-TWO
                 LOGIC.TERM-LISTP-WHEN-LOGIC.CONSTANT-LISTP-CHEAP
                 LOGIC.TERM-LISTP-OF-SUBSETP-WHEN-LOGIC.TERM-LISTP
                 LOOKUP-WHEN-NOT-CONSP
                 LOGIC.TERM-LIST-ATBLP-OF-CAR-WHEN-LOGIC.TERM-LIST-LIST-ATBLP
                 LOGIC.TERM-LIST-ATBLP-WHEN-LOGIC.VARIABLE-LISTP
                 LOGIC.TERM-LISTP-WHEN-LOGIC.VARIABLE-LISTP-CHEAP
                 LOGIC.TERM-LISTP-WHEN-NOT-CONSP
                 LOGIC.TERM-LIST-LIST-ATBLP-OF-CDR-WHEN-LOGIC.TERM-LIST-LIST-ATBLP
                 LOGIC.TERM-LIST-ATBLP-WHEN-LOGIC.CONSTANT-LISTP
                 ))

(local (%splitlimit 2))
(local (%liftlimit 2))

(%autoprove logic.appeal-listp-of-rw.world-urewrite-list-bldr
            (%autoinduct rw.world-urewrite-list-list-bldr x result fastp theoryname world traces proofs)
            (%restrict default rw.world-urewrite-list-list-bldr (equal x 'x))
            (%waterfall default 40)
            (%car-cdr-elim x)
            (%waterfall default 40)
            (%car-cdr-elim result)
            (%waterfall default 40)
            (%car-cdr-elim proofs)
            (%waterfall default 40)
            (%car-cdr-elim traces)
            (%waterfall default 40))

(%autoprove logic.conclusion-of-rw.world-urewrite-list-list-bldr
            (%autoinduct rw.world-urewrite-list-list-bldr x result fastp theoryname world traces proofs)
            (%restrict default rw.world-urewrite-list-list-bldr (equal x 'x))
            (%waterfall default 40)
            (%car-cdr-elim x)
            (%waterfall default 40)
            (%car-cdr-elim result)
            (%waterfall default 40)
            (%car-cdr-elim proofs)
            (%waterfall default 40)
            (%car-cdr-elim traces)
            (%waterfall default 40))

(%autoprove logic.proofp-of-rw.world-urewrite-list-list-bldr
            (%autoinduct rw.world-urewrite-list-list-bldr x result fastp theoryname world traces proofs)
            (%waterfall default 40)
            (%restrict default rw.world-urewrite-list-list-bldr (equal x 'x))
            (%waterfall default 40)
            (%car-cdr-elim x)
            (%waterfall default 40)
            (%car-cdr-elim result)
            (%waterfall default 40)
            (%car-cdr-elim proofs)
            (%waterfall default 40)
            (%car-cdr-elim traces)
            (%waterfall default 40))

(%autoprove logic.term-listp-of-rw.trace-list-rhses-free)

(local (%disable default
                 formula-decomposition
                 expensive-term/formula-inference
                 type-set-like-rules
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 expensive-subsetp-rules
                 unusual-memberp-rules
                 unusual-consp-rules
                 unusual-subsetp-rules
                 memberp-when-memberp-of-cdr
                 subsetp-when-not-consp
                 subsetp-when-not-consp-two))

(%autoadmit rw.world-urewrite-list-bldr-okp)
(%autoadmit rw.world-urewrite-list-bldr-high)

(encapsulate
 ()
 (local (%enable default
                 rw.world-urewrite-list-bldr-okp
                 rw.world-urewrite-list-bldr-high))
 (%autoprove rw.world-urewrite-list-bldr-okp-of-rw.world-urewrite-list-bldr-high)
 (%autoprove booleanp-of-rw.world-urewrite-list-bldr-okp)
 (%autoprove rw.world-urewrite-list-bldr-okp-of-logic.appeal-identity)
 (%autoprove lemma-1-for-soundness-of-rw.world-urewrite-list-bldr-okp)
 (%autoprove lemma-2-for-soundness-of-rw.world-urewrite-list-bldr-okp)
 (%autoprove forcing-soundness-of-rw.world-urewrite-list-bldr-okp
             (%use (%instance (%thm lemma-1-for-soundness-of-rw.world-urewrite-list-bldr-okp)))
             (%use (%instance (%thm lemma-2-for-soundness-of-rw.world-urewrite-list-bldr-okp)))
             (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                              (x (let ((orig-clause   (first (logic.extras x)))
                                       (result-clause (second (logic.extras x)))
                                       (theoryname    (third (logic.extras x)))
                                       (fastp         t) ;; so no traces are needed
                                       (world         (tactic.find-world (fourth (logic.extras x)) worlds))
                                       (traces        nil) ;; since fastp is set
                                       (proof         (logic.provable-witness (logic.conclusion
                                                                               (first (logic.subproofs x)))
                                                                              axioms thms atbl)))
                                   (rw.world-urewrite-list-bldr orig-clause result-clause fastp theoryname
                                                                world traces proof)))))))

(%ensure-exactly-these-rules-are-missing "../../tactics/rewrite-world")
