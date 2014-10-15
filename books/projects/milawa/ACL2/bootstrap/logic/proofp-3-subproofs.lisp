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
(include-book "proofp-2")
(%interactive)



;; BOZO add all these to autoprove
(%autoprove lemma-axiom-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.axiom-okp))

(%autoprove lemma-theorem-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.theorem-okp))

(%autoprove lemma-propositional-schema-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.propositional-schema-okp))

(%autoprove lemma-functional-equality-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.functional-equality-okp))

(%autoprove lemma-beta-reduction-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.beta-reduction-okp))

(%autoprove lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%disable default len-of-logic.strip-conclusions [outside]len-of-logic.strip-conclusions)
            (%use (%instance (%thm len-of-logic.strip-conclusions) (x a)))
            (%use (%instance (%thm len-of-logic.strip-conclusions) (x b))))

(%autoprove lemma-expansion-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.expansion-okp)
            (%use (%instance (%thm lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable)
                             (a (logic.subproofs x))
                             (b new-subproofs))))

(%autoprove lemma-contraction-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.contraction-okp)
            (%use (%instance (%thm lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable)
                             (a (logic.subproofs x))
                             (b new-subproofs)))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%car-cdr-elim new-subproofs)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove lemma-associativity-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.associativity-okp)
            (%use (%instance (%thm lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable)
                             (a (logic.subproofs x))
                             (b new-subproofs)))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%car-cdr-elim new-subproofs)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove lemma-cut-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.cut-okp)
            (%betamode nil)
            (%use (%instance (%thm lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable)
                             (a (logic.subproofs x))
                             (b new-subproofs)))
            (%auto :strategy (cleanup split crewrite))
            (%car-cdr-elim new-subproofs)
            (%auto :strategy (cleanup split crewrite))
            (%car-cdr-elim (cdr new-subproofs))
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove lemma-instantiation-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.instantiation-okp)
            (%use (%instance (%thm lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable)
                             (a (logic.subproofs x))
                             (b new-subproofs)))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%car-cdr-elim new-subproofs)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove lemma-induction-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.induction-okp)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove lemma-base-eval-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.base-eval-okp)
            (%forcingp nil)
            (%auto :strategy (cleanup split crewrite)))






;; Bah. We have a problem now.  Our rules above target
;;
;;   (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x))
;;
;; But we never see this.  Instead, we see things like:
;;
;;   (logic.appealp 'base-eval (logic.conclusion x) new-subproofs (logic.extras x))
;;
;; And even though we know that (logic.method x) is equal to 'base-eval, we don't match the
;; rule because we don't consider the canonical forms when doing pattern matching.  Maybe
;; we should try to change that.  That is, suppose we are trying to match (foo x y), but we
;; know (via our assms structure) that x = x', where x' is the canonical form of x.  Then,
;; really maybe we should be trying to match (foo x' y) instead.  This would require some
;; work to change.
;;
;; Instead of doing this, I add the following hack theorems which suck but do the job.
;;
;; How does ACL2 handle this?  It might be interesting to ask Matt.

(defsection lemma-axiom-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-axiom-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'axiom)))
                 :lhs (logic.axiom-okp (logic.appeal 'axiom (logic.conclusion x) new-subproofs (logic.extras x)) axioms atbl)
                 :rhs (logic.axiom-okp x axioms atbl)))
  (%use (%instance (%thm lemma-axiom-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(defsection lemma-theorem-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-theorem-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'theorem)))
                 :lhs (logic.theorem-okp (logic.appeal 'theorem (logic.conclusion x) new-subproofs (logic.extras x)) thms atbl)
                 :rhs (logic.theorem-okp x thms atbl)))
  (%use (%instance (%thm lemma-theorem-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(defsection lemma-propositional-schema-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-propositional-schema-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'propositional-schema)))
                 :lhs (logic.propositional-schema-okp (logic.appeal 'propositional-schema (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                 :rhs (logic.propositional-schema-okp x atbl)))
  (%use (%instance (%thm lemma-propositional-schema-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(defsection lemma-functional-equality-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-functional-equality-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'functional-equality)))
                 :lhs (logic.functional-equality-okp (logic.appeal 'functional-equality (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                 :rhs (logic.functional-equality-okp x atbl)))
  (%use (%instance (%thm lemma-functional-equality-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(defsection lemma-beta-reduction-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-beta-reduction-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'beta-reduction)))
                 :lhs (logic.beta-reduction-okp (logic.appeal 'beta-reduction (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                 :rhs (logic.beta-reduction-okp x atbl)))
  (%use (%instance (%thm lemma-beta-reduction-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(defsection lemma-expansion-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-expansion-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'expansion)))
                 :lhs (logic.expansion-okp (logic.appeal 'expansion (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                 :rhs (logic.expansion-okp x atbl)))
  (%use (%instance (%thm lemma-expansion-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(defsection lemma-contraction-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-contraction-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'contraction)))
                 :lhs (logic.contraction-okp (logic.appeal 'contraction (logic.conclusion x) new-subproofs (logic.extras x)))
                 :rhs (logic.contraction-okp x)))
  (%use (%instance (%thm lemma-contraction-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(defsection lemma-associativity-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-associativity-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'associativity)))
                 :lhs (logic.associativity-okp (logic.appeal 'associativity (logic.conclusion x) new-subproofs (logic.extras x)))
                 :rhs (logic.associativity-okp x)))
  (%use (%instance (%thm lemma-associativity-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(defsection lemma-cut-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-cut-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'cut)))
                 :lhs (logic.cut-okp (logic.appeal 'cut (logic.conclusion x) new-subproofs (logic.extras x)))
                 :rhs (logic.cut-okp x)))
  (%use (%instance (%thm lemma-cut-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(defsection lemma-instantiation-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-instantiation-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'instantiation)))
                 :lhs (logic.instantiation-okp (logic.appeal 'instantiation (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                 :rhs (logic.instantiation-okp x atbl)))
  (%use (%instance (%thm lemma-instantiation-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(defsection lemma-induction-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-induction-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'induction)))
                 :lhs (logic.induction-okp (logic.appeal 'induction (logic.conclusion x) new-subproofs (logic.extras x)))
                 :rhs (logic.induction-okp x)))
  (%use (%instance (%thm lemma-induction-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(defsection lemma-base-eval-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
  (%prove (%rule lemma-base-eval-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                 :hyps (list (%hyp (logic.appealp x))
                             (%hyp (logic.appeal-listp new-subproofs))
                             (%hyp (true-listp new-subproofs))
                             (%hyp (equal (logic.strip-conclusions (logic.subproofs x))
                                          (logic.strip-conclusions new-subproofs)))
                             (%hyp (equal (logic.method x) 'base-eval)))
                 :lhs (logic.base-eval-okp (logic.appeal 'base-eval (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                 :rhs (logic.base-eval-okp x atbl)))
  (%use (%instance (%thm lemma-base-eval-for-forcing-logic.provablep-when-logic.subproofs-provable)))
  (%auto)
  (%qed))

(%autoprove lemma-appeal-step-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%enable default logic.appeal-step-okp)
            (%enable default
                     lemma-axiom-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                     lemma-theorem-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                     lemma-propositional-schema-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                     lemma-functional-equality-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                     lemma-beta-reduction-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                     lemma-expansion-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                     lemma-contraction-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                     lemma-associativity-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                     lemma-cut-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                     lemma-instantiation-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                     lemma-induction-for-forcing-logic.provablep-when-logic.subproofs-provable-hack
                     lemma-base-eval-for-forcing-logic.provablep-when-logic.subproofs-provable-hack))

