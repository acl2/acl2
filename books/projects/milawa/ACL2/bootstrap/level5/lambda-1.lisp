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
(include-book "fuse")
(%interactive)



(defthm equal-of-first-index-and-n-when-len-alt
  ;; BOZO put this somewhere better.
  (implies (equal (len x) n)
           (equal (equal n (first-index a x))
                  (not (memberp a x)))))

(%autoprove equal-of-first-index-and-n-when-len-alt
            (%use (%instance (%thm equal-of-first-index-and-n-when-len))))

(%defderiv build.dual-substitution-lemma-1)
(%autoadmit build.flag-dual-substitution)
(%autoadmit build.dual-substitution)
(%autoadmit build.dual-substitution-list)

(%autoprove definition-of-build.dual-substitution
            (%restrict default build.flag-dual-substitution (equal x 'x))
            (%enable default
                     build.dual-substitution
                     build.dual-substitution-list))

(%autoprove definition-of-build.dual-substitution-list
            (%restrict default build.flag-dual-substitution (equal x 'x))
            (%enable default
                     build.dual-substitution
                     build.dual-substitution-list))

(%autoprove build.flag-dual-substitution-of-term-removal
            (%enable default build.dual-substitution))

(%autoprove build.flag-dual-substitution-of-list-removal
            (%enable default build.dual-substitution-list))

(%autoprove build.dual-substitution-under-iff
            (%restrict default definition-of-build.dual-substitution (equal x 'x)))

(%autoprove build.dual-substitution-list-when-not-consp
            (%restrict default definition-of-build.dual-substitution-list (equal x 'x)))

(%autoprove build.dual-substitution-list-of-cons
            (%restrict default definition-of-build.dual-substitution-list (equal x '(cons a x))))

(%autoprove len-of-build.dual-substitution-list
            (%cdr-induction x))



(defmacro %build.flag-dual-substitution-induction (flag x vars proofs)
  `(%induct (rank ,x)

            ((and (equal ,flag 'term)
                  (logic.constantp ,x))
             nil)

            ((and (equal ,flag 'term)
                  (logic.variablep ,x))
             nil)

            ((and (equal ,flag 'term)
                  (logic.functionp ,x))
             (((,flag 'list)
               (,x (logic.function-args ,x))
               (,vars ,vars)
               (,proofs ,proofs))))

            ((and (equal ,flag 'term)
                  (logic.lambdap ,x))

             (((,flag 'list)
               (,x (logic.lambda-actuals ,x))
               (,vars ,vars)
               (,proofs ,proofs))
              ((,flag 'term)
               (,x (logic.lambda-body ,x))
               (,vars (logic.lambda-formals ,x))
               (,proofs (build.dual-substitution-list (logic.lambda-actuals ,x) ,vars ,proofs)))))

            ((and (equal ,flag 'term)
                  (not (logic.constantp ,x))
                  (not (logic.variablep ,x))
                  (not (logic.functionp ,x))
                  (not (logic.lambdap ,x)))
             nil)

            ((and (not (equal ,flag 'term))
                  (consp ,x))
             (((,flag 'term) (,x (car ,x)) (,vars ,vars) (,proofs ,proofs))
              ((,flag 'list) (,x (cdr ,x)) (,vars ,vars) (,proofs ,proofs))))

            ((and (not (equal ,flag 'term))
                  (not (consp ,x)))
             nil)))



(%autoprove lemma-for-forcing-logic.appealp-of-build.dual-substitution
            ;; with manual induction -- 100m; with autoinduction -- 176m
            (%build.flag-dual-substitution-induction flag x vars proofs)
            (%auto :strategy (cleanup urewrite split))
            (%restrict default definition-of-build.dual-substitution (equal x 'x))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove forcing-logic.appealp-of-build.dual-substitution
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.dual-substitution)
                             (flag 'term))))

(%autoprove forcing-logic.appealp-listp-of-build.dual-substitution-list
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.dual-substitution)
                             (flag 'list))))

(%autoprove forcing-logic.conclusion-of-build.dual-substitution
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.dual-substitution)
                             (flag 'term))))

(%autoprove forcing-logic.strip-conclusions-of-build.dual-substitution-list
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.dual-substitution)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.proofp-of-build.dual-substitution
            ;; (%build.flag-dual-substitution-induction flag x vars proofs)
            (%autoinduct build.flag-dual-substitution)
            (%auto :strategy (cleanup urewrite split))
            (%restrict default definition-of-build.dual-substitution (equal x 'x))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove forcing-logic.proofp-of-build.dual-substitution
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-build.dual-substitution)
                             (flag 'term)))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove forcing-logic.proof-listp-of-build.dual-substitution-list
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-build.dual-substitution)
                             (flag 'list)))
            (%auto :strategy (cleanup urewrite split)))



(defsection build.lambda-pequal-by-args
  (%autoadmit build.lambda-pequal-by-args)
  (local (%enable default build.lambda-pequal-by-args))
  (%autoprove build.lambda-pequal-by-args-under-iff)
  (%autoprove forcing-logic.appealp-of-build.lambda-pequal-by-args)
  (%autoprove forcing-logic.conclusion-of-build.lambda-pequal-by-args)
  (%autoprove forcing-logic.proofp-of-build.lambda-pequal-by-args))



(defsection build.lambda-pequal-by-args-okp

  (%autoadmit build.lambda-pequal-by-args-okp)

  (%autoprove booleanp-of-build.lambda-pequal-by-args-okp
              (%enable default build.lambda-pequal-by-args-okp))

  (%autoprove build.lambda-pequal-by-args-okp-of-logic.appeal-identity
              (%enable default build.lambda-pequal-by-args-okp))

  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free))

  (%autoprove lemma-1-for-soundness-of-build.lambda-pequal-by-args-okp
              (%enable default build.lambda-pequal-by-args-okp))

  (%autoprove lemma-2-for-soundness-of-build.lambda-pequal-by-args-okp
              (%enable default build.lambda-pequal-by-args-okp))

  (%autoprove forcing-soundness-of-build.lambda-pequal-by-args-okp
              (%enable default
                       lemma-1-for-soundness-of-build.lambda-pequal-by-args-okp
                       lemma-2-for-soundness-of-build.lambda-pequal-by-args-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (build.lambda-pequal-by-args
                                   (first (logic.extras x))
                                   (second (logic.extras x))
                                   (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                axioms thms atbl)))))
              (%auto :strategy (cleanup split crewrite))
              (%enable default build.lambda-pequal-by-args-okp)
              (%auto :strategy (cleanup split crewrite))))


