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
(include-book "skeletonp")
(include-book "replace-subterm")
(%interactive)

(%autoadmit tactic.conditional-eqsubst-okp)
(%autoadmit tactic.conditional-eqsubst-env-okp)

(%autoprove booleanp-of-tactic.conditional-eqsubst-okp
            (%enable default tactic.conditional-eqsubst-okp))

(%autoprove booleanp-of-tactic.conditional-eqsubst-env-okp
            (%enable default tactic.conditional-eqsubst-env-okp))



(%autoadmit tactic.conditional-eqsubst-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.conditional-eqsubst-tac
            (%enable default tactic.conditional-eqsubst-tac))

(%autoprove forcing-tactic.conditional-eqsubst-okp-of-tactic.conditional-eqsubst-tac
            (%enable default
                     tactic.conditional-eqsubst-tac
                     tactic.conditional-eqsubst-okp))

(%autoprove forcing-tactic.conditional-eqsubst-env-okp-of-tactic.conditional-eqsubst-tac
            (%enable default
                     tactic.conditional-eqsubst-tac
                     tactic.conditional-eqsubst-env-okp))


;; BOZO consider moving to level4 or something?
(%defderiv tactic.conditional-eqsubst-lemma1)




(%autoadmit tactic.conditional-eqsubst-bldr)

(encapsulate
 ()
 (local (%enable default tactic.conditional-eqsubst-bldr))
 (%autoprove tactic.conditional-eqsubst-bldr-under-iff)
 (%autoprove forcing-logic.appealp-of-tactic.conditional-eqsubst-bldr)
 (%autoprove forcing-logic.conclusion-of-tactic.conditional-eqsubst-bldr)
 (%autoprove forcing-logic.proofp-of-tactic.conditional-eqsubst-bldr))






;; BOZO unlocalize/rename these in tactics/conditional-eqsubst.lisp

(defthmd crock1-for-tactic.conditional-eqsubst-compile
  (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
           (equal (logic.conclusion (first proofs))
                  (clause.clause-formula (first goals)))))

(defthmd crock2-for-tactic.conditional-eqsubst-compile
  (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
           (equal (logic.conclusion (second proofs))
                  (clause.clause-formula (second goals)))))

(defthmd crock3-for-tactic.conditional-eqsubst-compile
  (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
           (equal (logic.conclusion (third proofs))
                  (clause.clause-formula (third goals)))))

(defthmd crock4-for-tactic.conditional-eqsubst-compile
  ;; NOTE reordered equality to match term order
  (implies (not (cdr x))
           (equal (equal 1 (len x))
                  (consp x)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(%autoprove crock1-for-tactic.conditional-eqsubst-compile)
(%autoprove crock2-for-tactic.conditional-eqsubst-compile)
(%autoprove crock3-for-tactic.conditional-eqsubst-compile)
(%autoprove crock4-for-tactic.conditional-eqsubst-compile)


(%autoadmit tactic.conditional-eqsubst-compile)

(local (%enable default
                tactic.conditional-eqsubst-okp
                tactic.conditional-eqsubst-env-okp
                tactic.conditional-eqsubst-compile
                logic.term-formula))

(local (%enable default
                crock1-for-tactic.conditional-eqsubst-compile
                crock2-for-tactic.conditional-eqsubst-compile
                crock3-for-tactic.conditional-eqsubst-compile
                crock4-for-tactic.conditional-eqsubst-compile))

(%autoprove forcing-logic.appeal-listp-of-tactic.conditional-eqsubst-compile

            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      unusual-memberp-rules
                      unusual-consp-rules
                      unusual-subsetp-rules
                      expensive-term/formula-inference
                      formula-decomposition
                      same-length-prefixes-equal-cheap)

            (%waterfall default 40)

            (%restrict default logic.strip-conclusions
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%restrict default definition-of-logic.appeal-listp
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%waterfall default 40)

            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference
                     unusual-consp-rules)
            (%auto :strategy (cleanup split urewrite crewrite)))


(%autoprove forcing-logic.strip-conclusions-of-tactic.conditional-eqsubst-compile

            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      unusual-memberp-rules
                      unusual-consp-rules
                      unusual-subsetp-rules
                      expensive-term/formula-inference
                      formula-decomposition
                      same-length-prefixes-equal-cheap)

            (%waterfall default 40)

            (%restrict default logic.strip-conclusions
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%restrict default definition-of-logic.appeal-listp
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%waterfall default 40)

            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference
                     unusual-consp-rules)
            (%auto :strategy (cleanup split urewrite crewrite)))



(%autoprove forcing-logic.proof-listp-of-tactic.conditional-eqsubst-compile

            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      unusual-memberp-rules
                      unusual-consp-rules
                      unusual-subsetp-rules
                      expensive-term/formula-inference
                      formula-decomposition
                      same-length-prefixes-equal-cheap)

            (%waterfall default 40)

            (%restrict default logic.strip-conclusions
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%restrict default definition-of-logic.appeal-listp
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%restrict default definition-of-logic.proof-listp
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%waterfall default 40)

            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference
                     unusual-consp-rules)
            (%auto :strategy (cleanup split urewrite crewrite)))

(%ensure-exactly-these-rules-are-missing "../../tactics/conditional-eqsubst")

