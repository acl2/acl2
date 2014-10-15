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
(include-book "lambda-1")
(%interactive)


(%defderiv build.disjoined-dual-substitution-lemma-1 :omit-okp t)

(%autoadmit build.flag-disjoined-dual-substitution)
(%autoadmit build.disjoined-dual-substitution)
(%autoadmit build.disjoined-dual-substitution-list)

(%autoprove definition-of-build.disjoined-dual-substitution
            (%restrict default build.flag-disjoined-dual-substitution (equal x 'x))
            (%enable default
                     build.disjoined-dual-substitution
                     build.disjoined-dual-substitution-list))

(%autoprove definition-of-build.disjoined-dual-substitution-list
            (%restrict default build.flag-disjoined-dual-substitution (equal x 'x))
            (%enable default
                     build.disjoined-dual-substitution
                     build.disjoined-dual-substitution-list))

(%autoprove build.flag-disjoined-dual-substitution-of-term-removal
            (%enable default build.disjoined-dual-substitution))

(%autoprove build.flag-disjoined-dual-substitution-of-list-removal
            (%enable default build.disjoined-dual-substitution-list))

(%autoprove forcing-build.disjoined-dual-substitution-under-iff
            (%restrict default definition-of-build.disjoined-dual-substitution (equal x 'x)))

(%autoprove build.disjoined-dual-substitution-list-when-not-consp
            (%restrict default definition-of-build.disjoined-dual-substitution-list (equal x 'x)))

(%autoprove build.disjoined-dual-substitution-list-of-cons
            (%restrict default definition-of-build.disjoined-dual-substitution-list (equal x '(cons a x))))

(%autoprove len-of-build.disjoined-dual-substitution-list
            (%cdr-induction x))


(defmacro %build.flag-disjoined-dual-substitution-induction (flag x vars p proofs)
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
               (,p ,p)
               (,proofs ,proofs))
              ((,flag 'term)
               (,x    (logic.lambda-body ,x))
               (,vars (logic.lambda-formals ,x))
               (,p ,p)
               (,proofs (build.disjoined-dual-substitution-list (logic.lambda-actuals ,x) ,vars ,p ,proofs)))))

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

(%autoprove lemma-for-forcing-logic.appealp-of-build.disjoined-dual-substitution
            (%build.flag-disjoined-dual-substitution-induction flag x vars p proofs)
            (%auto :strategy (cleanup urewrite split))
            (%restrict default definition-of-build.disjoined-dual-substitution (equal x 'x))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove forcing-logic.appealp-of-build.disjoined-dual-substitution
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.disjoined-dual-substitution)
                             (flag 'term)))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove forcing-logic.conclusion-of-build.disjoined-dual-substitution
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.disjoined-dual-substitution)
                             (flag 'term)))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove forcing-logic.appeal-listp-of-build.disjoined-dual-substitution
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.disjoined-dual-substitution)
                             (flag 'list)))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove forcing-logic.strip-conclusions-of-build.disjoined-dual-substitution
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.disjoined-dual-substitution)
                             (flag 'list)))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove lemma-for-forcing-logic.proofp-of-build.disjoined-dual-substitution
            (%build.flag-disjoined-dual-substitution-induction flag x vars p proofs)
            (%auto :strategy (cleanup urewrite split))
            (%restrict default definition-of-build.disjoined-dual-substitution (equal x 'x))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove forcing-logic.proofp-of-build.disjoined-dual-substitution
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-build.disjoined-dual-substitution)
                             (flag 'term)))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove forcing-logic.proof-listp-of-build.disjoined-dual-substitution
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-build.disjoined-dual-substitution)
                             (flag 'list)))
            (%auto :strategy (cleanup urewrite split)))



(defsection build.disjoined-lambda-pequal-by-args
  (%autoadmit build.disjoined-lambda-pequal-by-args)
  (local (%enable default build.disjoined-lambda-pequal-by-args))
  (%autoprove forcing-build.disjoined-lambda-pequal-by-args-under-iff)
  (%autoprove forcing-logic.appealp-of-build.disjoined-lambda-pequal-by-args)
  (%autoprove forcing-logic.conclusion-of-build.disjoined-lambda-pequal-by-args)
  (%autoprove forcing-logic.proofp-of-build.disjoined-lambda-pequal-by-args))




(defsection build.disjoined-lambda-pequal-by-args-okp

  (%autoadmit build.disjoined-lambda-pequal-by-args-okp)

  (%autoprove booleanp-of-build.disjoined-lambda-pequal-by-args-okp
              (%enable default build.disjoined-lambda-pequal-by-args-okp))

  (%autoprove build.disjoined-lambda-pequal-by-args-okp-of-logic.appeal-identity
              (%enable default build.disjoined-lambda-pequal-by-args-okp))

  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free))

  (%autoprove lemma-1-for-soundness-of-build.disjoined-lambda-pequal-by-args-okp
              (%enable default build.disjoined-lambda-pequal-by-args-okp))

  (%autoprove lemma-2-for-soundness-of-build.disjoined-lambda-pequal-by-args-okp
              (%enable default build.disjoined-lambda-pequal-by-args-okp))

  (%autoprove forcing-soundness-of-build.disjoined-lambda-pequal-by-args-okp
              (%enable default
                       lemma-1-for-soundness-of-build.disjoined-lambda-pequal-by-args-okp
                       lemma-2-for-soundness-of-build.disjoined-lambda-pequal-by-args-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (build.disjoined-lambda-pequal-by-args
                                   (first (logic.extras x))
                                   (second (logic.extras x))
                                   (logic.vlhs (logic.conclusion x))
                                   (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                axioms thms atbl)))))
              (%auto :strategy (cleanup split crewrite))
              (%enable default build.disjoined-lambda-pequal-by-args-okp)
              (%auto :strategy (cleanup split crewrite))))

