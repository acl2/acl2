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
(include-book "eqtrace-okp")
(include-book "primary-eqtrace-bldr")
(include-book "secondary-eqtrace-bldr")
(include-book "trans1-eqtrace-bldr")
(include-book "trans2-eqtrace-bldr")
(include-book "trans3-eqtrace-bldr")
(include-book "weakening-eqtrace-bldr")
(include-book "direct-iff-eqtrace-bldr")
(include-book "negative-iff-eqtrace-bldr")
(include-book "hypbox-arities")
(%interactive)

(defsection rw.eqtrace-step-bldr
  (%autoadmit rw.eqtrace-step-bldr)
  (local (%enable default
                  rw.eqtrace-step-bldr
                  rw.eqtrace-step-okp))
  (local (%restrict default definition-of-rw.eqtrace-okp (equal x 'x)))
  (local (%disable default forcing-rw.eqtrace-list-okp-of-rw.eqtrace-subtraces))
  (%autoprove rw.eqtrace-step-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.eqtrace-step-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.eqtrace-step-bldr)
  (%autoprove forcing-logic.proofp-of-rw.eqtrace-step-bldr))



(%autoadmit rw.flag-eqtrace-bldr)
(%autoadmit rw.eqtrace-bldr)
(%autoadmit rw.eqtrace-list-bldr)

(%autoprove definition-of-rw.eqtrace-bldr
            (%restrict default rw.flag-eqtrace-bldr (equal x 'x))
            (%enable default rw.eqtrace-bldr rw.eqtrace-list-bldr))

(%autoprove definition-of-rw.eqtrace-list-bldr
            (%restrict default rw.flag-eqtrace-bldr (equal x 'x))
            (%enable default rw.eqtrace-bldr rw.eqtrace-list-bldr))

(%autoprove rw.flag-eqtrace-bldr-of-trace
            (%enable default rw.eqtrace-bldr))

(%autoprove rw.flag-eqtrace-bldr-of-list
            (%enable default rw.eqtrace-list-bldr))

(%autoprove rw.eqtrace-list-bldr-when-not-consp
            (%restrict default definition-of-rw.eqtrace-list-bldr (equal x 'x)))

(%autoprove rw.eqtrace-list-bldr-of-cons
            (%restrict default definition-of-rw.eqtrace-list-bldr (equal x '(cons a x))))

(%defprojection :list (rw.eqtrace-list-bldr x box)
                :element (rw.eqtrace-bldr x box))



(defthm lemma-for-forcing-logic.appealp-of-rw.eqtrace-bldr
  ;; BOZO change to defthms-flag
  (if (equal flag 'trace)
      (implies (and (rw.eqtracep x)
                    (rw.hypboxp box)
                    (rw.eqtrace-okp x box))
               (and (logic.appealp (rw.eqtrace-bldr x box))
                    (equal (logic.conclusion (rw.eqtrace-bldr x box))
                           (rw.eqtrace-formula x box))))
    (implies (and (rw.eqtrace-listp x)
                  (rw.hypboxp box)
                  (rw.eqtrace-list-okp x box))
             (and (logic.appeal-listp (rw.eqtrace-list-bldr x box))
                  (equal (logic.strip-conclusions (rw.eqtrace-list-bldr x box))
                         (rw.eqtrace-formula-list x box)))))
  :rule-classes nil
  :hints(("Goal"
          :induct (rw.flag-eqtrace-bldr flag x box)
          :expand (rw.eqtrace-bldr x box))))

(%autoprove lemma-for-forcing-logic.appealp-of-rw.eqtrace-bldr
            (%rw.flag-eqtracep-induction flag x)
            (%restrict default definition-of-rw.eqtrace-bldr (equal x 'x)))

(%autoprove forcing-logic.appealp-of-rw.eqtrace-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-rw.eqtrace-bldr)
                             (flag 'trace))))

(%autoprove forcing-logic.conclusion-of-rw.eqtrace-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-rw.eqtrace-bldr)
                             (flag 'trace))))

(%autoprove forcing-logic.appeal-listp-of-rw.eqtrace-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-rw.eqtrace-bldr)
                             (flag 'list))))

(%autoprove forcing-logic.strip-conclusions-of-rw.eqtrace-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-rw.eqtrace-bldr)
                             (flag 'list))))

(defthm@ lemma-for-forcing-logic.proofp-of-rw.eqtrace-bldr
  (implies (and (rw.hypboxp box)
                (rw.hypbox-atblp box atbl)
                (equal (cdr (lookup 'not atbl)) 1)
                (equal (cdr (lookup 'equal atbl)) 2)
                (equal (cdr (lookup 'iff atbl)) 2)
                (@obligations rw.eqtrace-bldr))
           (if (equal flag 'trace)
               (implies (and (rw.eqtracep x)
                             (rw.eqtrace-okp x box))
                        (equal (logic.proofp (rw.eqtrace-bldr x box) axioms thms atbl)
                               t))
             (implies (and (rw.eqtrace-listp x)
                           (rw.eqtrace-list-okp x box))
                      (equal (logic.proof-listp (rw.eqtrace-list-bldr x box) axioms thms atbl)
                             t))))
  :rule-classes nil
  :hints(("Goal"
          :induct (rw.flag-eqtrace-bldr flag x box)
          :expand (rw.eqtrace-bldr x box))))

(%autoprove lemma-for-forcing-logic.proofp-of-rw.eqtrace-bldr
            (%rw.flag-eqtracep-induction flag x)
            (%restrict default definition-of-rw.eqtrace-bldr (equal x 'x)))

(%autoprove forcing-logic.proofp-of-rw.eqtrace-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-rw.eqtrace-bldr)
                             (flag 'trace))))

(%autoprove forcing-logic.proof-listp-of-rw.eqtrace-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-rw.eqtrace-bldr)
                             (flag 'list))))



(%autoadmit rw.eqtrace-bldr-okp)

(%autoadmit rw.eqtrace-bldr-high)

(defsection rw.eqtrace-bldr-okp
  (local (%enable default rw.eqtrace-bldr-okp))
  (%autoprove booleanp-of-rw.eqtrace-bldr-okp)
  (%autoprove rw.eqtrace-bldr-okp-of-logic.appeal-identity)
  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free
                   forcing-logic.term-list-atblp-of-logic.function-args))
  (%autoprove lemma-1-for-soundness-of-rw.eqtrace-bldr-okp)
  (%autoprove lemma-2-for-soundness-of-rw.eqtrace-bldr-okp)
  (%autoprove forcing-soundness-of-rw.eqtrace-bldr-okp
              (%enable default
                       lemma-1-for-soundness-of-rw.eqtrace-bldr-okp
                       lemma-2-for-soundness-of-rw.eqtrace-bldr-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (rw.eqtrace-bldr (first (logic.extras x))
                                                   (second (logic.extras x))))))))

