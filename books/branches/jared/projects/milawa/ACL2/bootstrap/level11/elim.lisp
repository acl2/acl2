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
(include-book "conditional-eqsubst")
(%interactive)


(defthm logic.strip-conclusions-of-restn
  ;; BOZO this seems to address some of the firstn/restn issues.  Move it where it
  ;; belongs and try using it globally.
  (equal (logic.strip-conclusions (restn n x))
         (restn n (logic.strip-conclusions x))))

(in-theory (disable restn-of-logic.strip-conclusions))

(ACL2::theory-invariant (ACL2::incompatible (:rewrite logic.strip-conclusions-of-restn)
                                            (:rewrite restn-of-logic.strip-conclusions)))

(%autoprove logic.strip-conclusions-of-restn)
(%disable default
          restn-of-logic.strip-conclusions
          [outside]restn-of-logic.strip-conclusions)


(defthm logic.strip-conclusions-of-firstn
  ;; BOZO this seems to address some of the firstn/restn issues.  Move it where it
  ;; belongs and try using it globally.
  (equal (logic.strip-conclusions (firstn n x))
         (firstn n (logic.strip-conclusions x))))

(in-theory (disable firstn-of-logic.strip-conclusions))

(ACL2::theory-invariant (ACL2::incompatible (:rewrite logic.strip-conclusions-of-firstn)
                                            (:rewrite firstn-of-logic.strip-conclusions)))

(%autoprove logic.strip-conclusions-of-firstn)
(%disable default
          firstn-of-logic.strip-conclusions
          [outside]firstn-of-logic.strip-conclusions)


(%autoprove logic.substitute-formula-of-logic.disjoin-formulas-free)

(%autoprove lemma-for-aggressive-forcing-logic.substitute-of-logic.replace-subterm
            (%logic.term-induction flag x)
            (%restrict default definition-of-logic.replace-subterm (equal x 'x)))

(%autoprove aggressive-forcing-logic.substitute-of-logic.replace-subterm
            (%use (%instance (%thm lemma-for-aggressive-forcing-logic.substitute-of-logic.replace-subterm)
                             (flag 'term))))

(%autoprove aggressive-forcing-logic.substitute-list-of-logic.replace-subterm-list
            (%use (%instance (%thm lemma-for-aggressive-forcing-logic.substitute-of-logic.replace-subterm)
                             (flag 'list))))

(%autoprove lemma-for-equal-of-logic.replace-subterm-and-logic.replace-subterm-when-same-term-and-old
            (%logic.term-induction flag x)
            (%restrict default definition-of-logic.replace-subterm (equal x 'x))
            (%restrict default definition-of-logic.subtermp (equal y 'x)))

(%autoprove equal-of-logic.replace-subterm-and-logic.replace-subterm-when-same-term-and-old
            (%use (%instance (%thm lemma-for-equal-of-logic.replace-subterm-and-logic.replace-subterm-when-same-term-and-old)
                             (flag 'term))))

(%autoprove equal-of-logic.replace-subterm-list-and-logic.replace-subterm-list-when-same-term-and-old
            (%use (%instance (%thm lemma-for-equal-of-logic.replace-subterm-and-logic.replace-subterm-when-same-term-and-old)
                             (flag 'list))))

(%autoprove forcing-logic.substitute-of-var-when-first-in-sigma
            (%restrict default definition-of-logic.substitute (equal x 'var)))

(%autoprove forcing-logic.substitute-of-var-when-second-in-sigma
            (%restrict default definition-of-logic.substitute (equal x 'var)))

(%autoprove equal-of-first-and-second-when-uniquep)
(%autoprove equal-of-second-and-first-when-uniquep) ;; probably unnecessary via term order??

(%autoprove memberp-of-first-of-difference-in-removed
            (%disable default
                      memberp-of-car
                      [outside]memberp-of-car)
            (%use (%instance (%thm memberp-of-car)
                             (x (difference x y)))))

(%autoprove memberp-of-second-of-difference-in-removed
            (%disable default memberp-of-second)
            (%use (%instance (%thm memberp-of-second)
                             (x (difference x y)))))


(%autoadmit elim.flag-collect-destructed-variables)
(%autoadmit elim.flag-slow-collect-destructed-variables)
(%autoadmit elim.collect-destructed-variables)
(%autoadmit elim.collect-destructed-variables-list)

(%autoprove true-listp-of-elim.flag-collect-destructed-variables
            (%autoinduct elim.flag-collect-destructed-variables flag x acc)
            (%restrict default elim.flag-collect-destructed-variables (equal x 'x)))

(%autoprove elim.flag-slow-collect-destructed-variables-equiv
            (%autoinduct elim.flag-collect-destructed-variables flag x acc)
            (%restrict default elim.flag-collect-destructed-variables (equal x 'x))
            (%restrict default elim.flag-slow-collect-destructed-variables (equal x 'x)))

(%autoprove definition-of-elim.collect-destructed-variables
            (%forcingp nil)
            (%restrict default elim.flag-slow-collect-destructed-variables (equal x 'x))
            (%enable default
                     elim.collect-destructed-variables
                     elim.collect-destructed-variables-list))

(%autoprove definition-of-elim.collect-destructed-variables-list
            (%restrict default elim.flag-slow-collect-destructed-variables (equal x 'x))
            (%enable default
                     elim.collect-destructed-variables
                     elim.collect-destructed-variables-list))

(%autoprove lemma-for-logic.variable-listp-of-elim.collect-destructed-variables
            (%logic.term-induction flag x)
            (%restrict default definition-of-elim.collect-destructed-variables (equal x 'x))
            (%restrict default definition-of-elim.collect-destructed-variables-list (equal x 'x)))

(%autoprove logic.variable-listp-of-elim.collect-destructed-variables
            (%use (%instance (%thm lemma-for-logic.variable-listp-of-elim.collect-destructed-variables)
                             (flag 'term))))

(%autoprove logic.variable-listp-of-elim.collect-destructed-variables-list
            (%use (%instance (%thm lemma-for-logic.variable-listp-of-elim.collect-destructed-variables)
                             (flag 'list))))




;; BOZO stupid name, should be called duplicity
(%autoadmit fast-count)
(%autoadmit slow-count)
(%autoadmit count)

(%autoprove fast-count-as-slow-count
            (%autoinduct fast-count a x acc)
            (%restrict default fast-count (equal x 'x))
            (%restrict default slow-count (equal x 'x)))

(%autoprove definition-of-count
            (%enable default count)
            (%restrict default slow-count (equal x 'x))
            (%enable default fast-count-as-slow-count))

(%autoprove count-when-not-consp
            (%restrict default definition-of-count (equal x 'x)))

(%autoprove count-of-cons
            (%restrict default definition-of-count (equal x '(cons b x))))

(%autoprove natp-of-count
            (%cdr-induction x))

(%autoprove count-of-zero
            (%cdr-induction x))

(%autoprove count-of-list-fix
            (%cdr-induction x))

(%autoprove count-of-app
            (%cdr-induction x))

(%autoprove count-of-rev
            (%cdr-induction x))

(%autoprove count-when-not-memberp
            (%cdr-induction x))


(%autoadmit aux-maximal-count)

(%autoprove memberp-of-aux-maximal-count
            (%autoinduct aux-maximal-count best best-count domain x)
            (%restrict default aux-maximal-count (equal domain 'domain)))

(%autoprove aux-maximal-count-when-not-consp-of-x
            (%autoinduct aux-maximal-count best best-count domain x)
            (%restrict default aux-maximal-count (equal domain 'domain)))


(%autoadmit maximal-count)

(%autoprove maximal-count-when-not-consp
            (%enable default maximal-count))

(%autoprove memberp-of-maximal-count
            (%enable default maximal-count))



(%autoadmit elim.find-backup-var)

(%autoprove logic.variablep-of-elim.find-backup-var
            (%autoinduct elim.find-backup-var)
            (%restrict default elim.find-backup-var (equal x 'x)))

(%autoadmit elim.choose-var-to-eliminate)

(%autoprove lemma-for-logic.variablep-of-elim.choose-var-to-eliminate
            (%disable default logic.variablep-when-memberp-of-logic.variable-listp)
            (%use (%instance (%thm logic.variablep-when-memberp-of-logic.variable-listp)
                             (a (maximal-count x))
                             (x x))))

(%autoprove logic.variablep-of-elim.choose-var-to-eliminate
            (%enable default
                     elim.choose-var-to-eliminate
                     lemma-for-logic.variablep-of-elim.choose-var-to-eliminate))

(%deflist logic.variable-list-listp (x)
          (logic.variable-listp x))

(%defmap :map (elim.namesp x)
         :key (logic.variablep x)
         :val (logic.variable-listp x)
         :key-list (logic.variable-listp x)
         :val-list (logic.variable-list-listp x)
         :val-of-nil t)

(%autoadmit elim.pick-fresh-vars)

(encapsulate
 ()
 (local (%disable default
                  unusual-consp-rules
                  unusual-memberp-rules
                  unusual-subsetp-rules
                  expensive-term/formula-inference
                  type-set-like-rules
                  list-of-first-and-second-when-len-2
                  ))
 (local (%enable default elim.pick-fresh-vars))
 (%autoprove forcing-logic.variablep-of-first-of-elim.pick-fresh-vars)
 (%autoprove forcing-logic.variablep-of-second-of-elim.pick-fresh-vars)
 (%autoprove forcing-logic.memberp-of-first-of-elim.pick-fresh-vars)
 (%autoprove forcing-logic.memberp-of-second-of-elim.pick-fresh-vars)
 (%autoprove forcing-equal-of-first-and-second-of-elim.pick-fresh-vars)
 (%autoprove forcing-equal-of-second-and-first-of-elim.pick-fresh-vars))


(%autoadmit elim.elim-clause)
(encapsulate
 ()
 (local (%enable default elim.elim-clause))
 (%autoprove forcing-logic.term-list-listp-of-elim.elim-clause)
 (%autoprove forcing-cons-listp-of-elim.elim-clause)
 (%autoprove forcing-logic.term-list-list-atblp-of-elim.elim-clause))



(%autoadmit elim.elim-clause-bldr)
(encapsulate
 ()
 (local (%enable default
                 axiom-cons-of-car-and-cdr
                 elim.elim-clause
                 logic.term-formula
                 redefinition-of-logic.term-list-formulas
                 elim.elim-clause-bldr))
 (%autoprove forcing-logic.appealp-of-elim.elim-clause-bldr)
 (%autoprove forcing-logic.conclusion-of-elim.elim-clause-bldr)
 (%autoprove forcing-logic.proofp-of-elim.elim-clause-bldr))


(%autoadmit elim.elim-clause-list)
(%autoprove true-listp-of-elim.elim-clause-list
            (%cdr-induction x)
            (%restrict default elim.elim-clause-list (equal x 'x)))
(%autoprove forcing-logic.term-list-listp-of-elim.elim-clause-list
            (%cdr-induction x)
            (%restrict default elim.elim-clause-list (equal x 'x)))
(%autoprove forcing-logic.term-list-list-atblp-of-elim.elim-clause-list
            (%cdr-induction x)
            (%restrict default elim.elim-clause-list (equal x 'x)))
(%autoprove forcing-cons-listp-of-elim.elim-clause-list
            (%cdr-induction x)
            (%restrict default elim.elim-clause-list (equal x 'x)))



(%autoadmit elim.elim-clause-list-bldr)

(encapsulate
 ()

 (%autoprove dangerous-decomposition-of-app
             (%cdr-cdr-induction x a)
             (%restrict default firstn (equal n '(len a)))
             (%restrict default restn (equal n '(len a))))

 (local (%enable default dangerous-decomposition-of-app))

 (%autoprove forcing-logic.appeal-listp-of-elim.elim-clause-list-bldr
             (%autoinduct elim.elim-clause-list-bldr)
             (%restrict default elim.elim-clause-list-bldr (equal x 'x))
             (%restrict default elim.elim-clause-list (equal x 'x)))

 (%autoprove forcing-logic.strip-conclusions-of-elim.elim-clause-list-bldr
             (%autoinduct elim.elim-clause-list-bldr)
             (%restrict default elim.elim-clause-list-bldr (equal x 'x))
             (%restrict default elim.elim-clause-list (equal x 'x)))

 (%autoprove forcing-logic.proof-listp-of-elim.elim-clause-list-bldr
             (%autoinduct elim.elim-clause-list-bldr)
             (%restrict default elim.elim-clause-list-bldr (equal x 'x))
             (%restrict default elim.elim-clause-list (equal x 'x))))




(%autoadmit tactic.elim-first-okp)

(%autoprove booleanp-of-tactic.elim-first-okp
            (%enable default tactic.elim-first-okp))


(%autoadmit tactic.elim-first-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.elim-first-tac
            (%enable default tactic.elim-first-tac))

(%autoprove forcing-tactic.elim-first-okp-of-tactic.elim-first-tac
            (%enable default tactic.elim-first-tac tactic.elim-first-okp))



(%autoadmit tactic.elim-first-compile)

(encapsulate
 ()
 (local (%enable default
                 tactic.elim-first-okp
                 tactic.elim-first-compile))

 (local (%enable default dangerous-decomposition-of-app))

 (%autoprove forcing-logic.appeal-listp-of-tactic.elim-first-compile
             (%auto :strategy (cleanup split urewrite crewrite))
             (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS (TACTIC.SKELETON->GOALS X)))))

 (%autoprove forcing-logic.strip-conclusions-of-tactic.elim-first-compile
             (%auto :strategy (cleanup split urewrite crewrite))
             (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS (TACTIC.SKELETON->GOALS X))))
             (%auto :strategy (cleanup split urewrite crewrite))
             (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS (TACTIC.SKELETON->GOALS X)))))

 (%autoprove forcing-logic.proof-listp-of-tactic.elim-first-compile
             (%auto :strategy (cleanup split urewrite crewrite))
             (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS (TACTIC.SKELETON->GOALS X))))))



(%autoadmit tactic.elim-all-okp)

(%autoprove booleanp-of-tactic.elim-all-okp
            (%enable default tactic.elim-all-okp))


(%autoadmit tactic.elim-all-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.elim-all-tac
            (%enable default tactic.elim-all-tac))

(%autoprove forcing-tactic.elim-all-okp-of-tactic.elim-all-tac
            (%enable default tactic.elim-all-tac tactic.elim-all-okp))



(%autoadmit tactic.elim-all-compile)

(encapsulate
 ()
 (local (%enable default tactic.elim-all-okp tactic.elim-all-compile))
 (%autoprove forcing-logic.appeal-listp-of-tactic.elim-all-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.elim-all-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.elim-all-compile))


(%ensure-exactly-these-rules-are-missing "../../tactics/elim")