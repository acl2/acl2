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
(include-book "hacks")
(%interactive)

;(local (%disable default LOGIC.FUNCTION-OF-CONS-WITH-DEFECTIVELY-MERGED-CONSTANT))


(defsection build.modus-ponens-list
  (encapsulate
   ()
   (%autoadmit build.modus-ponens-list)
   (local (%restrict default build.modus-ponens-list (equal as 'as)))
   (%autoprove forcing-build.modus-ponens-list-under-iff
               (%autoinduct build.modus-ponens-list))
   (%autoprove forcing-logic.appealp-of-build.modus-ponens-list
               (%autoinduct build.modus-ponens-list))
   (%autoprove forcing-logic.conclusion-of-build.modus-ponens-list
               (%autoinduct build.modus-ponens-list))
   (%autoprove forcing-logic.proofp-of-build.modus-ponens-list
               (%autoinduct build.modus-ponens-list)))
   (%autoadmit build.modus-ponens-list-okp)
   (local (%enable default build.modus-ponens-list-okp))
   (%autoprove booleanp-of-build.modus-ponens-list-okp)
   (%autoprove build.modus-ponens-list-okp-of-logic.appeal-identity)
   (local (%enable default backtracking-logic.formula-atblp-rules))
   (local (%disable default
                    forcing-logic.formula-atblp-rules
                    forcing-lookup-of-logic.function-name-free
                    forcing-logic.term-list-atblp-of-logic.function-args))
   (%autoprove lemma-1-for-soundness-of-build.modus-ponens-list-okp)
   (%autoprove lemma-2-for-soundness-of-build.modus-ponens-list-okp)
   (%autoprove forcing-soundness-of-build.modus-ponens-list-okp
               (%enable default
                        lemma-1-for-soundness-of-build.modus-ponens-list-okp
                        lemma-2-for-soundness-of-build.modus-ponens-list-okp)
               (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                                (x (build.modus-ponens-list (logic.conclusion x)
                                                            (logic.provable-list-witness
                                                             (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                             axioms thms atbl)
                                                            (logic.provable-witness
                                                             (logic.conclusion (car (logic.subproofs x)))
                                                             axioms thms atbl)))))
               (%auto :strategy (cleanup split crewrite))))


(defsection build.disjoined-modus-ponens-list
  (%autoadmit build.disjoined-modus-ponens-list)
  (%autoprove forcing-build.disjoined-modus-ponens-list-under-iff
              (%restrict default build.disjoined-modus-ponens-list (equal as 'as))
              (%autoinduct build.disjoined-modus-ponens-list))
  (%autoprove lemma-for-forcing-logic.appealp-of-build.disjoined-modus-ponens-list
              (%autoinduct build.disjoined-modus-ponens-list)
              (%restrict default build.disjoined-modus-ponens-list (equal as 'as))
              ;; This disable prevents an rlimit loop.  It wasn't clear to me how to syntactically
              ;; limit the rule appropriately.
              (%disable default forcing-logic.vrhs-of-logic.disjoin-formulas-free))
  (%autoprove forcing-logic.appealp-of-build.disjoined-modus-ponens-list
              (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.disjoined-modus-ponens-list))))
  (%autoprove forcing-logic.conclusion-of-build.disjoined-modus-ponens-list
              (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.disjoined-modus-ponens-list))))
  (%autoprove forcing-logic.proofp-of-build.disjoined-modus-ponens-list
              (%restrict default build.disjoined-modus-ponens-list (equal as 'as))
              (%autoinduct build.disjoined-modus-ponens-list))

  (%autoadmit build.disjoined-modus-ponens-list-okp)
  (local (%enable default build.disjoined-modus-ponens-list-okp))
  (%autoprove booleanp-of-build.disjoined-modus-ponens-list-okp)
  (%autoprove build.disjoined-modus-ponens-list-okp-of-logic.appeal-identity)
  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free
                   forcing-logic.term-list-atblp-of-logic.function-args))
  (%autoprove lemma-1-for-soundness-of-build.disjoined-modus-ponens-list-okp)
  (%autoprove lemma-2-for-soundness-of-build.disjoined-modus-ponens-list-okp)
  (%autoprove forcing-soundness-of-build.disjoined-modus-ponens-list-okp
              (%enable default
                       lemma-1-for-soundness-of-build.disjoined-modus-ponens-list-okp
                       lemma-2-for-soundness-of-build.disjoined-modus-ponens-list-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (build.disjoined-modus-ponens-list (logic.vrhs (logic.conclusion x))
                                                                     (logic.provable-list-witness
                                                                      (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                      axioms thms atbl)
                                                                     (logic.provable-witness
                                                                      (logic.conclusion (car (logic.subproofs x)))
                                                                      axioms thms atbl)))))
              (%auto :strategy (cleanup split crewrite))))

(defsection build.multi-expansion
  ;; No okp --- we use generic-subset instead
  (%autoadmit build.multi-expansion)
  (local (%restrict default build.multi-expansion (equal as 'as)))
  (%autoprove build.multi-expansion-under-iff)
  (local (%disable default
                   car-when-memberp-and-not-memberp-of-cdr-cheap
                   car-when-memberp-of-singleton-list-cheap))
  (%autoprove forcing-logic.appealp-of-build.multi-expansion
              (%cdr-induction as)
              (%auto)
              (%enable default
                       car-when-memberp-and-not-memberp-of-cdr-cheap
                       car-when-memberp-of-singleton-list-cheap))
  (%autoprove forcing-logic.conclusion-of-build.multi-expansion
              (%cdr-induction as)
              (%auto)
              (%enable default
                       car-when-memberp-and-not-memberp-of-cdr-cheap
                       car-when-memberp-of-singleton-list-cheap))
  (%autoprove forcing-logic.proofp-of-build.multi-expansion
              (%cdr-induction as)
              (%auto)
              (%enable default
                       car-when-memberp-and-not-memberp-of-cdr-cheap
                       car-when-memberp-of-singleton-list-cheap)))

(defsection build.multi-or-expansion-step
  ;; No okp --- we use generic subset instead
  (%autoadmit build.multi-or-expansion-step)
  (%autoprove build.multi-or-expansion-step-under-iff
              (%restrict default build.multi-or-expansion-step (equal as 'as)))
  (local (%disable default
                   car-when-memberp-of-singleton-list-cheap
                   car-when-memberp-and-not-memberp-of-cdr-cheap))
  (%autoprove lemma-for-forcing-logic.appealp-of-build.multi-or-expansion-step
              (%cdr-induction as)
              (%restrict default build.multi-or-expansion-step (equal as 'as))
              (%auto)
              (%enable default
                       car-when-memberp-of-singleton-list-cheap
                       car-when-memberp-and-not-memberp-of-cdr-cheap))
  (%autoprove forcing-logic.appealp-of-build.multi-or-expansion-step
              (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.multi-or-expansion-step))))
  (%autoprove forcing-logic.conclusion-of-build.multi-or-expansion-step
              (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.multi-or-expansion-step))))
  (%autoprove forcing-logic.proofp-of-build.multi-or-expansion-step
              (%cdr-induction as)
              (%restrict default build.multi-or-expansion-step (equal as 'as))
              (%auto)
              (%enable default
                       car-when-memberp-of-singleton-list-cheap
                       car-when-memberp-and-not-memberp-of-cdr-cheap)))


(defsection build.multi-or-expansion
  ;; No okp --- we use generic subset instead
  (%autoadmit build.multi-or-expansion)
  (local (%restrict default build.multi-or-expansion (equal as 'as)))
  (%autoprove build.multi-or-expansion-under-iff)

  ;; loops with new rewriting changes
  (local (%disable default car-when-memberp-and-not-memberp-of-cdr-cheap))
  (%autoprove forcing-logic.appealp-of-build.multi-or-expansion
              (%cdr-induction as))

  (%autoprove forcing-logic.conclusion-of-build.multi-or-expansion
              (%cdr-induction as))

  (%autoprove forcing-logic.proofp-of-build.multi-or-expansion
              (%cdr-induction as)))

(%defderiv build.generic-subset-step-lemma-1 :omit-okp t)


(defsection build.generic-subset-step
  ;; No okp --- we use generic subset instead
  (%autoadmit build.generic-subset-step)
  (local (%enable default build.generic-subset-step))
  (%autoprove build.generic-subset-step-under-iff)
  (%autoprove forcing-logic.appealp-of-build.generic-subset-step)
  (%autoprove forcing-logic.conclusion-of-build.generic-subset-step)
  (%autoprove forcing-logic.proofp-of-build.generic-subset-step))


(defsection build.generic-subset
  (%autoadmit build.generic-subset)
  (%autoprove build.generic-subset-under-iff
              (%restrict default build.generic-subset (equal as 'as)))
  (%autoprove lemma-for-forcing-logic.appealp-of-build.generic-subset
              (%autoinduct build.generic-subset)
              (%auto :strategy (cleanup split urewrite crewrite))
              (%restrict default build.generic-subset (equal as 'as)))
  (%autoprove forcing-logic.appealp-of-build.generic-subset
              (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.generic-subset))))
  (%autoprove forcing-logic.conclusion-of-build.generic-subset
              (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.generic-subset))))
  (%autoprove forcing-logic.proofp-of-build.generic-subset
              (%autoinduct build.generic-subset)
              (%auto :strategy (cleanup split urewrite crewrite))
              (%restrict default build.generic-subset (equal as 'as)))
  (%autoadmit build.generic-subset-okp)
  (local (%enable default build.generic-subset-okp))
  (%autoprove booleanp-of-build.generic-subset-okp)
  (%autoprove build.generic-subset-okp-of-logic.appeal-identity)
  (%autoprove forcing-soundness-of-build.generic-subset-okp
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (build.generic-subset (first (logic.extras x))
                                                        (second (logic.extras x))
                                                        (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                                                                axioms thms atbl)))))))


(defsection build.multi-assoc-expansion
  (%autoadmit build.multi-assoc-expansion)
  (%autoprove build.multi-assoc-expansion-under-iff
              (%restrict default build.multi-assoc-expansion (equal as 'as)))
  (%autoprove lemma-for-forcing-logic.appealp-of-build.multi-assoc-expansion
              (%autoinduct build.multi-assoc-expansion)
              (%restrict default build.multi-assoc-expansion (equal as 'as))
              (%forcingp nil))
  (%autoprove forcing-logic.appealp-of-build.multi-assoc-expansion
              (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.multi-assoc-expansion))))
  (%autoprove forcing-logic.conclusion-of-build.multi-assoc-expansion
              (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.multi-assoc-expansion))))
  (%autoprove forcing-logic.proofp-of-build.multi-assoc-expansion
              (%autoinduct build.multi-assoc-expansion)
              (%restrict default build.multi-assoc-expansion (equal as 'as)))
  (%autoadmit build.multi-assoc-expansion-okp)
  (local (%enable default build.multi-assoc-expansion-okp))
  (%autoprove booleanp-of-build.multi-assoc-expansion-okp)
  (%autoprove build.multi-assoc-expansion-okp-of-logic.appeal-identity)
  (%autoprove lemma-1-for-soundness-of-build.multi-assoc-expansion-okp)
  (%autoprove lemma-2-for-soundness-of-build.multi-assoc-expansion-okp)
  (%autoprove forcing-soundness-of-build.multi-assoc-expansion-okp
              (%enable default
                       lemma-1-for-soundness-of-build.multi-assoc-expansion-okp
                       lemma-2-for-soundness-of-build.multi-assoc-expansion-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (build.multi-assoc-expansion (logic.provable-witness
                                                                (logic.conclusion (car (logic.subproofs x)))
                                                                axioms thms atbl)
                                                               (logic.extras x)))))))


(%autoadmit build.rev-disjunction)
(%autoadmit build.disjoined-rev-disjunction)
(%autoadmit build.disjoined-subset)
(%autoadmit build.all-superset-of-some)

(%autoprove forcing-logic.appeal-listp-of-build.all-superset-of-some
            (%cdr-induction x)
            (%restrict default build.all-superset-of-some (equal x 'x))
            (%enable default build.disjoined-subset))

(%autoprove forcing-logic.strip-conclusions-of-build.all-superset-of-some
            (%cdr-induction x)
            (%restrict default build.all-superset-of-some (equal x 'x))
            (%enable default build.disjoined-subset))

(%autoprove forcing-logic.proof-listp-of-build.all-superset-of-some
            (%cdr-induction x)
            (%restrict default build.all-superset-of-some (equal x 'x))
            (%enable default build.disjoined-subset))

