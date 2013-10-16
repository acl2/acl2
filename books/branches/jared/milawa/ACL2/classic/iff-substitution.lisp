;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "../build/prop")
(include-book "../build/conjunctions")
(include-book "../logic/find-proof")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; In this file, we extend our proof checker with an equivalence checking
;; extension.  This extension is based on the equivalence theorem, below:
;;
;;   The Equivalence Theorem.
;;   (From Shoenfield's Mathematical Logic; Page 34)
;;
;;   Let G be obtained from F by replacing some occurrences of A1,...,An by
;;   A1',...,An', respectively.  If
;;    |- A1 <-> A1', |- A2 <-> A2', ..., |- An <-> An',
;;   then
;;    |- F <-> G.
;;
;; Our work is again very similar to Shankar's work in formalizing Godel's
;; incompleteness theorem in NQTHM.



;; We begin formalizing the equivalence theorem using the function
;; equivalent-underp below, which takes as inputs:
;;
;;   - two formulas, f and g
;;   - a list of equivalences, [A1 <-> A1', A2 <-> A2', ..., An <-> An']
;;
;; The equivalent-underp function returns true if g can be obtained by
;; replacing some occurrences of A1, ..., An with A1', ..., An'.
;;
;; Note: This is like Shankar's function, "eqn-form"

(defund iff-substitutiblep (f g as)
  (declare (xargs :guard (and (logic.formulap f)
                              (logic.formulap g)
                              (logic.formula-listp as))))
  (cond ((equal f g) t)
        ((memberp (logic.pnot (logic.por (logic.pnot (logic.por (logic.pnot f) g))
                             (logic.pnot (logic.por (logic.pnot g) f))))
                  as)
         t)
        ((equal (logic.fmtype f) 'pnot*)
         (if (equal (logic.fmtype g) 'pnot*)
             (iff-substitutiblep (logic.~arg f) (logic.~arg g) as)
           nil))
        ((equal (logic.fmtype f) 'por*)
         (if (equal (logic.fmtype g) 'por*)
             (and (iff-substitutiblep (logic.vlhs f) (logic.vlhs g) as)
                  (iff-substitutiblep (logic.vrhs f) (logic.vrhs g) as))
           nil))
        (t nil)))

(defthm booleanp-of-iff-substitutiblep
  (equal (booleanp (iff-substitutiblep f g as))
         t)
  :hints(("Goal" :in-theory (e/d (iff-substitutiblep)
                                 (logic.fmtype-normalizer-cheap
                                  aggressive-equal-of-logic.pnots
                                  aggressive-equal-of-logic.pors)))))





;; Historical Performance Notes
;;
;; Each of the branches below, except for the one where we just use find-proof,
;; are tautologies or tautological consequences of the recursively proven
;; formulas.  And, originally, I used the tautology builder directly in order
;; to construct the proofs, just as Shankar had done in his function.
;;
;; This is fine for proving that iff substitution is sound.  But in the
;; bootstrapping process, we actually care about proof size, and the tautology
;; builder builds remarkably long proofs.  So, now I use several "by hand"
;; derivations below, instead of calling upon the tautology builder.  This
;; results in a massive improvement.
;;
;; We did some test cases below.
;;
;; (defconst *F* (logic.pequal 'A1 'A1))
;; (defconst *G* (logic.pequal 'A2 'A2))
;; (defconst *H* (logic.pequal 'B1 'B1))
;; (defconst *I* (logic.pequal 'B2 'B2))
;;
;; Test1: (iff-substitutible-bldr *F* *F* nil)
;; Test2: (iff-substitutible-bldr
;;         (logic.pnot *F*)
;;         (logic.pnot *G*)
;;         (list (build.axiom (logic.piff *F* *G*))))
;;
;; Test3: (iff-substitutible-bldr
;;         (logic.por *F* *G*)
;;         (logic.por *H* *I*)
;;         (list (build.axiom (logic.piff *F* *H*))
;;               (build.axiom (logic.piff *G* *I*))))
;;
;; Here are the size results:
;;
;; Test    Rank w/Tautologies     Rank by Hand     Savings
;; Test1   1,780                  1,106            37.9%
;; Test2   60,291                 2,511            95.8%
;; Test3   1,122,354              5,294            99.5%
;;
;; BOZO we can probably do even better by building the proofs separately with
;; some kind of aux builder, then conjoining them in the end.

(defund iff-substitutible-bldr (f g as)
  (declare (xargs :guard (and (logic.formulap f)
                              (logic.formulap g)
                              (logic.appeal-listp as)
                              (iff-substitutiblep f g (logic.strip-conclusions as)))
                  :verify-guards nil))
  (cond ((equal f g)
         ;; Here F = G, so F <-> F is a tautology.  Originally, I used the
         ;; tautology builder here, but now I prefer this shorter derivation:
         ;;
         ;; Derivation.  (Cost: 18)
         ;;
         ;;   1. F -> F      Propositional Schema
         ;;   2. F <-> F     Conjoin; 1,1
         ;;
         ;; Q.E.D.
         (let ((lemma (build.propositional-schema f)))
           (build.conjoin lemma lemma)))
        ((memberp (logic.pnot (logic.por (logic.pnot (logic.por (logic.pnot f) g))
                                         (logic.pnot (logic.por (logic.pnot g) f))))
                  (logic.strip-conclusions as))
         ;; Here F <-> G happens to be a proof given to us in the list of
         ;; proofs.  Just find that proof and return it.
         (logic.find-proof (logic.pnot (logic.por (logic.pnot (logic.por (logic.pnot f) g))
                                                  (logic.pnot (logic.por (logic.pnot g) f))))
                           as))
        ((equal (logic.fmtype f) 'pnot*)
         ;; Here we have F = ~A1 and G = ~A2.  Originally, I proved A1 <-> A2
         ;; recursively, and then as a tautological consequence concluded that
         ;; F <-> G.  Now, I use the derivation below, which creates much
         ;; shorter proofs:
         ;;
         ;; Derivation.  (Cost: 35 + 2x)
         ;;
         ;;  1. A1 <-> A2         (Given; constructed recursively)
         ;;  2. ~A2 v A1          Second Conjunct; 1
         ;;  3. A1 v ~A2          Commute Or
         ;;  4. ~~A1 v ~A2        LHS Insert ~~
         ;;  5. ~A1 v A2          First Conjunct; 1
         ;;  6. A2 v ~A1          Commute Or
         ;;  7. ~~A2 v ~A1        LHS Insert ~~
         ;;  8. F <-> G           Conjoin; 4,7
         ;;
         ;; Q.E.D.
         (let ((lemma (iff-substitutible-bldr (logic.~arg f) (logic.~arg g) as)))
           (build.conjoin
            (build.lhs-insert-neg-neg (build.commute-or (build.second-conjunct lemma)))
            (build.lhs-insert-neg-neg (build.commute-or (build.first-conjunct lemma))))))
        ((equal (logic.fmtype f) 'por*)
         ;; Here we have F = A1 v B1 and G = A2 v B2.  Originally, I proved
         ;; A1 <-> A2 and B1 <-> B2, recursively, and then as a tautological
         ;; consequence concluded that F <-> G.  Now, I use the derivation
         ;; below, which creates much shorter proofs:
         ;;
         ;; Derivation.  (Cost: 119 + 2x + 2y)
         ;;
         ;;   1. A1 <-> A2               (Given; constructed recursively)
         ;;   2. B1 <-> B2               (Given; constructed recursively)
         ;;
         ;;   3. ~A1 v A2                1st Conjunct; 1
         ;;   4. ~A1 v (A2 v B2)         DJ Right Expansion
         ;;   5. ~B1 v B2                1st Conjunct; 2
         ;;   6. ~B1 v (A2 v B2)         DJ Left Expansion
         ;;   7. ~(A1 v B1) v (A2 v B2)  Merge Implications; 4,6
         ;;
         ;;   8. ~A2 v A1                2nd Conjunct; 1
         ;;   9. ~A2 v (A1 v B1)         DJ Right Expansion
         ;;  10. ~B2 v B1                2nd Conjunct; 2
         ;;  11. ~B2 v (A1 v B1)         DJ Left Expansion
         ;;  12. ~(A2 v B2) v (A1 v B1)  Merge Implications; 9,11
         ;;  13. F <-> G                 Conjoin; 7,12
         ;;
         ;; Q.E.D.
         (let ((lemma1 (iff-substitutible-bldr (logic.vlhs f) (logic.vlhs g) as))
               (lemma2 (iff-substitutible-bldr (logic.vrhs f) (logic.vrhs g) as)))
           (build.conjoin
            (build.merge-implications
             (build.disjoined-right-expansion (build.first-conjunct lemma1) (logic.vrhs g))
             (build.disjoined-left-expansion (build.first-conjunct lemma2) (logic.vlhs g)))
            (build.merge-implications
             (build.disjoined-right-expansion (build.second-conjunct lemma1) (logic.vrhs f))
             (build.disjoined-left-expansion (build.second-conjunct lemma2) (logic.vlhs f))))))
        (t nil)))


(defthm logic.fmtype-of-g-when-iff-substitutible-for-logic.pnot
  (implies (and (iff-substitutiblep f g as)
                (not (memberp (logic.pnot (logic.por (logic.pnot (logic.por (logic.pnot f) g))
                                                     (logic.pnot (logic.por (logic.pnot g) f))))
                              as))
                (equal (logic.fmtype f) 'pnot*))
           (equal (logic.fmtype g) 'pnot*))
  :hints(("Goal" :in-theory (enable iff-substitutiblep))))

(defthm logic.fmtype-of-g-when-iff-substitutible-for-logic.por
  (implies (and (iff-substitutiblep f g as)
                (not (memberp (logic.pnot (logic.por (logic.pnot (logic.por (logic.pnot f) g))
                                                     (logic.pnot (logic.por (logic.pnot g) f))))
                              as))
                (force (equal (logic.fmtype f) 'por*)))
           (equal (logic.fmtype g) 'por*))
  :hints(("Goal" :in-theory (enable iff-substitutiblep))))

(defthm forcing-iff-substitutiblep-of-logic.vlhs
  (implies (and (iff-substitutiblep f g as)
                (not (memberp (logic.pnot (logic.por (logic.pnot (logic.por (logic.pnot f) g))
                                                     (logic.pnot (logic.por (logic.pnot g) f))))
                              as))
                (force (equal (logic.fmtype f) 'por*)))
           (iff-substitutiblep (logic.vlhs f) (logic.vlhs g) as))
  :hints(("Goal" :in-theory (enable iff-substitutiblep))))

(defthm forcing-iff-substitutiblep-of-logic.vrhs
  (implies (and (iff-substitutiblep f g as)
                (not (memberp (logic.pnot (logic.por (logic.pnot (logic.por (logic.pnot f) g))
                                                     (logic.pnot (logic.por (logic.pnot g) f))))
                              as))
                (force (equal (logic.fmtype f) 'por*)))
           (iff-substitutiblep (logic.vrhs f) (logic.vrhs g) as))
  :hints(("Goal" :in-theory (enable iff-substitutiblep))))

(defthm forcing-iff-substitutiblep-of-logic.~arg
  (implies (and (iff-substitutiblep f g as)
                (not (memberp (logic.pnot (logic.por (logic.pnot (logic.por (logic.pnot f) g))
                                                     (logic.pnot (logic.por (logic.pnot g) f))))
                              as))
                (force (equal (logic.fmtype f) 'pnot*)))
           (iff-substitutiblep (logic.~arg f) (logic.~arg g) as))
  :hints(("Goal" :in-theory (enable iff-substitutiblep))))

(encapsulate
 ()
 (local (defthm main-lemma
          (implies (and (logic.formulap f)
                        (logic.formulap g)
                        (logic.appeal-listp as)
                        (iff-substitutiblep f g (logic.strip-conclusions as)))
                   (and (logic.appealp (iff-substitutible-bldr f g as))
                        (equal (logic.conclusion (iff-substitutible-bldr f g as))
                               (logic.pnot (logic.por (logic.pnot (logic.por (logic.pnot f) g))
                                          (logic.pnot (logic.por (logic.pnot g) f)))))))
          :hints(("Goal" :in-theory (enable iff-substitutible-bldr iff-substitutiblep)))))

(defthm forcing-logic.appealp-of-iff-substitutible-bldr
   (implies (and (force (logic.formulap f))
                 (force (logic.formulap g))
                 (force (logic.appeal-listp as))
                 (force (iff-substitutiblep f g (logic.strip-conclusions as))))
            (equal (logic.appealp (iff-substitutible-bldr f g as))
                   t)))

(defthm forcing-logic.conclusion-of-iff-substitutible-bldr
   (implies (and (force (logic.formulap f))
                 (force (logic.formulap g))
                 (force (logic.appeal-listp as))
                 (force (iff-substitutiblep f g (logic.strip-conclusions as))))
            (equal (logic.conclusion (iff-substitutible-bldr f g as))
                   (logic.pnot (logic.por (logic.pnot (logic.por (logic.pnot f) g))
                              (logic.pnot (logic.por (logic.pnot g) f))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(defthm forcing-logic.proofp-of-iff-substitutible-bldr
  (implies (and (force (logic.formulap f))
                (force (logic.formulap g))
                (force (logic.appeal-listp as))
                (force (iff-substitutiblep f g (logic.strip-conclusions as)))
                ;; ---
                (force (logic.formula-atblp f atbl))
                (force (logic.formula-atblp g atbl))
                (force (logic.proof-listp as axioms thms atbl)))
           (logic.proofp (iff-substitutible-bldr f g as)
                   axioms thms atbl))
  :hints(("Goal" :in-theory (enable iff-substitutible-bldr
                                    iff-substitutiblep))))

(verify-guards iff-substitutible-bldr)



;; Iff Consequences
;; Derive G from proofs of F and A1 <-> A1', ..., An <-> An'
;;   where G is iff-substitutible for F.
;;
;; Derivation.
;;
;;   1. F <-> G     Iff Substitution
;;   2. F -> G      First Conjunct
;;   3. F           Given
;;   4. G           Modus Ponens; 3,2
;;
;; Q.E.D.

(defun iff-consequence-bldr (g f as)
  (declare (xargs :guard (and (logic.formulap g)
                              (logic.appealp f)
                              (logic.appeal-listp as)
                              (iff-substitutiblep (logic.conclusion f) g (logic.strip-conclusions as)))))
  (build.modus-ponens f (build.first-conjunct (iff-substitutible-bldr (logic.conclusion f) g as))))

(defthm forcing-logic.appealp-of-iff-consequence-bldr
  (implies (and (force (logic.formulap g))
                (force (logic.appealp f))
                (force (logic.appeal-listp as))
                (force (iff-substitutiblep (logic.conclusion f) g (logic.strip-conclusions as))))
           (equal (logic.appealp (iff-consequence-bldr g f as))
                  t))
  :hints(("Goal" :in-theory (enable iff-consequence-bldr))))

(defthm forcing-logic.conclusion-of-iff-consequence-bldr
  (implies (and (force (logic.formulap g))
                (force (logic.appealp f))
                (force (logic.appeal-listp as))
                (force (iff-substitutiblep (logic.conclusion f) g (logic.strip-conclusions as))))
           (equal (logic.conclusion (iff-consequence-bldr g f as))
                  g))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable iff-consequence-bldr))))

(defthm forcing-logic.proofp-of-iff-consequence-bldr
  (implies (and (force (logic.formulap g))
                (force (logic.appealp f))
                (force (logic.appeal-listp as))
                (force (iff-substitutiblep (logic.conclusion f) g (logic.strip-conclusions as)))
                ;; ---
                (force (logic.formula-atblp g atbl))
                (force (logic.proofp f axioms thms atbl))
                (force (logic.proof-listp as axioms thms atbl)))
           (equal (logic.proofp (iff-consequence-bldr g f as) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable iff-consequence-bldr))))


