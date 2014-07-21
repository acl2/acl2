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
(include-book "cleanup")
(include-book "conditional-eqsubst")
(include-book "conditional-eqsubst-all")
(include-book "crewrite-all")
(include-book "crewrite-first")
(include-book "elim")
(include-book "distribute-all")
(include-book "fertilize")
(include-book "generalize-all")
(include-book "generalize-first")
(include-book "induct")
(include-book "split-all")
(include-book "split-first")
(include-book "urewrite-all")
(include-book "urewrite-first")
(include-book "use")
(include-book "waterfall")
(include-book "simple-world-change")
(include-book "theory-change")
(%interactive)



(%autoprove |(< b d) when (= (+ a (+ b c)) d)|)
(%autoprove |(< a c) when (= (+ a b) c)|)
(%autoprove |(< b c) when (= (+ a b) c)|)



(%autoadmit tactic.world-stepp)

(%autoprove booleanp-of-tactic.world-stepp
            (%enable default tactic.world-stepp))


(%autoadmit tactic.world-step-okp)

(%autoprove booleanp-of-tactic.world-step-okp
            (%enable default tactic.world-step-okp))

(%autoadmit tactic.worlds-okp)


(%autoadmit tactic.compile-worlds-step)

(%autoprove tactic.worldp-of-tactic.compile-worlds-step
            (%enable default
                     tactic.compile-worlds-step
                     tactic.world-step-okp))

(%autoprove tactic.world-atblp-of-tactic.compile-worlds-step
            (%enable default
                     tactic.compile-worlds-step
                     tactic.world-step-okp))

(%autoprove tactic.world-env-okp-of-tactic.compile-worlds-step
            (%enable default
                     tactic.compile-worlds-step
                     tactic.world-step-okp))

(%autoprove tactic.world->index-of-tactic.compile-worlds-step
            (%enable default
                     tactic.world-stepp
                     tactic.compile-worlds-step
                     tactic.simple-change-world-compile-world
                     tactic.update-noexec-compile-world
                     tactic.create-theory-compile-world
                     tactic.e/d-compile-world
                     tactic.restrict-compile-world
                     tactic.cheapen-compile-world))


(%autoadmit tactic.compile-worlds)

(%autoprove consp-of-tactic.compile-worlds
            (%autoinduct tactic.compile-worlds x world)
            (%restrict default tactic.compile-worlds (equal x 'x)))

(%autoprove tactic.world-listp-of-tactic.compile-worlds
            (%autoinduct tactic.compile-worlds x world)
            (%restrict default tactic.compile-worlds (equal x 'x))
            (%restrict default tactic.worlds-okp (equal x 'x)))

(%autoprove tactic.world-list-atblp-of-tactic.compile-worlds
            (%autoinduct tactic.compile-worlds x world)
            (%restrict default tactic.compile-worlds (equal x 'x))
            (%restrict default tactic.worlds-okp (equal x 'x)))

(%autoprove tactic.world-list-env-okp-of-tactic.compile-worlds
            (%autoinduct tactic.compile-worlds x world)
            (%restrict default tactic.compile-worlds (equal x 'x))
            (%restrict default tactic.worlds-okp (equal x 'x)))


(%autoadmit tactic.skeleton-step-okp)

(%autoadmit tactic.skeleton-step-env-okp)

(%autoprove booleanp-of-tactic.skeleton-step-okp
            (%enable default tactic.skeleton-step-okp))

(%autoprove booleanp-of-tactic.skeleton-step-env-okp
            (%enable default tactic.skeleton-step-env-okp))



(%autoadmit tactic.skeleton-length)

(%autoprove natp-of-tactic.skeleton-length
            (%autoinduct tactic.skeleton-length)
            (%restrict default tactic.skeleton-length (equal x 'x)))

(%autoprove tactic.skeleton-length-zero
            (%autoinduct tactic.skeleton-length)
            (%restrict default tactic.skeleton-length (equal x 'x)))

(%autoprove tactic.skeleton-length-one
            (%autoinduct tactic.skeleton-length)
            (%restrict default tactic.skeleton-length (equal x 'x)))

(%autoprove tactic.skeleton-length-of-tactic.skeleton->history
            (%autoinduct tactic.skeleton-length)
            (%restrict default tactic.skeleton-length (equal x 'x)))

(%autoadmit tactic.compile-skeleton-step)

(encapsulate
 ()
 (local (%enable default
                 tactic.skeleton-step-okp
                 tactic.skeleton-step-env-okp
                 tactic.compile-skeleton-step
                 tactic.world-stepp
                 tactic.world-step-okp))
 (local (%disable default
                  expensive-arithmetic-rules
                  type-set-like-rules
                  unusual-memberp-rules
                  unusual-subsetp-rules
                  memberp-when-not-consp
                  same-length-prefixes-equal-cheap
                  expensive-term/formula-inference
                  formula-decomposition))
 (%autoprove forcing-logic.appeal-listp-of-tactic.compile-skeleton-step)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.compile-skeleton-step)
 (%autoprove forcing-logic.proof-listp-of-tactic.compile-skeleton-step))


(%autoadmit tactic.skeleton-okp)

(%autoprove booleanp-of-tactic.skeleton-okp
            (%autoinduct tactic.skeleton-okp)
            (%restrict default tactic.skeleton-okp (equal x 'x)))


(%autoadmit tactic.skeleton-env-okp)

(%autoprove booleanp-of-tactic.skeleton-env-okp
            (%autoinduct tactic.skeleton-env-okp)
            (%restrict default tactic.skeleton-env-okp (equal x 'x)))


(%autoadmit tactic.compile-skeleton)

(%autoprove forcing-logic.appeal-listp-of-tactic.compile-skeleton
            (%autoinduct tactic.compile-skeleton)
            (%restrict default tactic.skeleton-okp (equal x 'x))
            (%restrict default tactic.compile-skeleton (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-tactic.compile-skeleton
            (%autoinduct tactic.compile-skeleton)
            (%restrict default tactic.skeleton-okp (equal x 'x))
            (%restrict default tactic.compile-skeleton (equal x 'x))
            (%restrict default tactic.original-conclusions (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-tactic.compile-skeleton
            (%autoinduct tactic.compile-skeleton)
            (%restrict default tactic.skeleton-okp (equal x 'x))
            (%restrict default tactic.skeleton-env-okp (equal x 'x))
            (%restrict default tactic.compile-skeleton (equal x 'x))
            (%disable default
                      unusual-memberp-rules
                      memberp-when-not-consp))




(%autoadmit tactic.compile-skeleton-okp)

(%autoprove booleanp-of-tactic.compile-skeleton-okp
            (%enable default tactic.compile-skeleton-okp))

(%defprojection
 :list (logic.appeal-list method x subproofs extras)
 :element (logic.appeal method x subproofs extras))

(%autoadmit tactic.compile-skeleton-high)

(%deflist tactic.compile-skeleton-list-okp (x worlds axioms thms atbl)
  (tactic.compile-skeleton-okp x worlds axioms thms atbl))

(%autoprove tactic.compile-skeleton-list-okp-of-logic.appeal-list
            (%cdr-induction conclusions)
            (%enable default tactic.compile-skeleton-okp))

(%autoprove tactic.compile-skeleton-list-okp-of-tactic.compile-skeleton-high
            (%enable default tactic.compile-skeleton-high))

(encapsulate
 ()
 (local (%enable default tactic.compile-skeleton-okp))
 (%autoprove tactic.compile-skeleton-okp-of-logic.appeal-identity)
 (%autoprove lemma-1-for-soundness-of-tactic.compile-skeleton-okp)
 (%autoprove lemma-2-for-soundness-of-tactic.compile-skeleton-okp)
 (%autoprove forcing-soundness-of-tactic.compile-skeleton-okp
             (%use (%instance (%thm lemma-1-for-soundness-of-tactic.compile-skeleton-okp)))
             (%use (%instance (%thm lemma-2-for-soundness-of-tactic.compile-skeleton-okp)))
             (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                              (x (let* ((skelly     (logic.extras x))
                                        (in-proofs  (logic.provable-list-witness
                                                     (logic.strip-conclusions (logic.subproofs x))
                                                     axioms thms atbl))
                                        (out-proofs (tactic.compile-skeleton skelly worlds in-proofs)))
                                   (logic.find-proof (logic.conclusion x) out-proofs)))))))


(%ensure-exactly-these-rules-are-missing "../../tactics/compiler")

