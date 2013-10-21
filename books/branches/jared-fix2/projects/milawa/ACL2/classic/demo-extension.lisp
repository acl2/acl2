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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; We prove that a new proof checker, demo.proofp, is sound with respect to the
;; core proof checker, logic.proofp.  Our new proof checker understands all of
;; the primitive rules, and also commute-or.  This isn't a practically useful
;; thing to do, but perhaps this serves as the simplest example of extending
;; the core prover.

(defund@ demo.commute-or$ (x)
  ;; This builds a "commute or" appeal.  Such appeals are not accepted by
  ;; logic.proofp, but they will be accepted by demo.proofp.
  (declare (xargs :guard (and (logic.appealp x)
                              (@match (proof x (v A B))))))
  (logic.appeal 'commute-or
                (@formula (v B A))
                (list x)
                nil))

(encapsulate
 ()
 (local (in-theory (enable demo.commute-or$)))

 (defthm demo.commute-or$-under-iff
   (iff (demo.commute-or$ x)
        t))

 (defthm logic.method-of-demo.commute-or$
   (equal (logic.method (demo.commute-or$ x))
          'commute-or))

 (defthm@ logic.conclusion-of-demo.commute-or$
   (@extend ((proof x (v A B)))
            (equal (logic.conclusion (demo.commute-or$ x))
                   (@formula (v B A)))))

 (defthm logic.subproofs-of-demo.commute-or$
   (equal (logic.subproofs (demo.commute-or$ x))
          (list x)))

 (defthm logic.extras-of-demo.commute-or$
   (equal (logic.extras (demo.commute-or$ x))
          nil))

 (defthm@ forcing-logic.appealp-of-demo.commute-or$
   (implies (force (and (logic.appealp x)
                        (@match (proof x (v A B)))))
            (equal (logic.appealp (demo.commute-or$ x))
                   t))))



(defund@ demo.commute-or-okp (x)
  ;; This checks that a commute or appeal is valid.  It's the same idea as in
  ;; the primitive checkers for expansion, associativity, etc.
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'commute-or)
         (equal extras nil)
         (equal (len subproofs) 1)
         (@match (formula conclusion (v A B))
                 (proof (first subproofs) (v B A))))))

(encapsulate
 ()
 (local (in-theory (enable demo.commute-or-okp)))

 (defthm booleanp-of-demo.commute-or-okp
   (equal (booleanp (demo.commute-or-okp x))
          t))

 (defthm@ forcing-demo.commute-or-okp-of-demo.commute-or$
   (implies (force (and (logic.appealp x)
                        (@match (proof x (v A B)))))
            (equal (demo.commute-or-okp (demo.commute-or$ x))
                   t)))

 (defthm demo.commute-or-okp-of-logic.appeal-identity
   (equal (demo.commute-or-okp (logic.appeal-identity x))
          (demo.commute-or-okp x)))

 ;; Now we'll show that demo.commute-or-okp is sound w.r.t. the core proof
 ;; checker: if demo.commute-or-okp accepts a step whose subproofs are all
 ;; provable, then the step's conclusion is also provable.

 (local (defthm lemma1
          (implies (and (demo.commute-or-okp x)
                        (logic.appealp x)
                        (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
                   (equal (logic.conclusion (build.commute-or (logic.provable-witness (logic.conclusion (first (logic.subproofs x))) axioms thms atbl)))
                          (logic.conclusion x)))))

 (local (defthm lemma2
          (implies (and (demo.commute-or-okp x)
                        (logic.appealp x)
                        (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
                   (equal (logic.proofp (build.commute-or (logic.provable-witness (logic.conclusion (first (logic.subproofs x))) axioms thms atbl)) axioms thms atbl)
                          t))))

 (defthm soundness-of-demo.commute-or-okp
   (implies (and (demo.commute-or-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints(("Goal"
           :use (:instance forcing-logic.provablep-when-logic.proofp
                           (x (build.commute-or (logic.provable-witness (logic.conclusion (first (logic.subproofs x))) axioms thms atbl))))))))




(defund demo.appeal-step-okp (x axioms thms atbl)
  ;; This is our extended version of logic.appeal-step-okp.  We accept commute
  ;; or appeals, and also all the primitive appeals.  I sometimes think of this
  ;; function as "extending of the virtual table" to include a new "subclass"
  ;; of the appeal class.
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (cond ((equal (logic.method x) 'commute-or)
         (demo.commute-or-okp x))
        (t
         (logic.appeal-step-okp x axioms thms atbl))))



(encapsulate
 ()
 (local (in-theory (enable demo.appeal-step-okp)))

 (defthm soundness-of-demo.appeal-step-okp
   (implies (and (logic.appealp x)
                 (demo.appeal-step-okp x axioms thms atbl)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t)))

 (defthm demo.appeal-step-okp-when-logic.appeal-step-okp
   ;; This shows that our new step checker is "complete" in the sense that all
   ;; previously acceptable appeals are still acceptable.
   (implies (logic.appeal-step-okp x axioms thms atbl)
            (demo.appeal-step-okp x axioms thms atbl))
   :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

 (defthm demo.appeal-step-okp-when-not-consp
   (implies (not (consp x))
            (equal (demo.appeal-step-okp x axioms thms atbl)
                   nil))
   :hints(("Goal" :in-theory (enable logic.method)))))



(defund demo.flag-proofp (flag x axioms thms atbl)
  (declare (xargs :guard (and (if (equal flag 'proof)
                                  (logic.appealp x)
                                (and (equal flag 'list)
                                     (logic.appeal-listp x)))
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
                  :measure (two-nats-measure (rank x)
                                             (if (equal flag 'proof) 1 0))))
  (if (equal flag 'proof)
      (and (demo.appeal-step-okp x axioms thms atbl)
           (demo.flag-proofp 'list (logic.subproofs x) axioms thms atbl))
    (if (consp x)
        (and (demo.flag-proofp 'proof (car x) axioms thms atbl)
             (demo.flag-proofp 'list (cdr x) axioms thms atbl))
     t)))

(definlined demo.proofp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (demo.flag-proofp 'proof x axioms thms atbl))

(definlined demo.proof-listp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (demo.flag-proofp 'list x axioms thms atbl))

(defthmd definition-of-demo.proofp
  (equal (demo.proofp x axioms thms atbl)
         (and (demo.appeal-step-okp x axioms thms atbl)
              (demo.proof-listp (logic.subproofs x) axioms thms atbl)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable demo.proofp demo.proof-listp demo.flag-proofp))))

(defthmd definition-of-demo.proof-listp
  (equal (demo.proof-listp x axioms thms atbl)
         (if (consp x)
             (and (demo.proofp (car x) axioms thms atbl)
                  (demo.proof-listp (cdr x) axioms thms atbl))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable demo.proofp demo.proof-listp demo.flag-proofp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition demo.proofp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition demo.proof-list))))



(defthm demo.proofp-when-not-consp
  (implies (not (consp x))
           (equal (demo.proofp x axioms thms atbl)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-demo.proofp))))

(defthm demo.proof-listp-when-not-consp
  (implies (not (consp x))
           (equal (demo.proof-listp x axioms thms atbl)
                  t))
  :hints (("Goal" :in-theory (enable definition-of-demo.proof-listp))))

(defthm demo.proof-listp-of-cons
  (equal (demo.proof-listp (cons a x) axioms thms atbl)
         (and (demo.proofp a axioms thms atbl)
              (demo.proof-listp x axioms thms atbl)))
  :hints (("Goal" :in-theory (enable definition-of-demo.proof-listp))))

(defthms-flag
  :thms ((proof booleanp-of-demo.proofp
                (equal (booleanp (demo.proofp x axioms thms atbl))
                       t))
         (t booleanp-of-demo.proof-listp
            (equal (booleanp (demo.proof-listp x axioms thms atbl))
                   t)))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-demo.proofp))))

(deflist demo.proof-listp (x axioms thms atbl)
  (demo.proofp x axioms thms atbl)
  :already-definedp t)


(defthms-flag
  :thms ((proof logic.provablep-when-demo.proofp
                (implies (and (logic.appealp x)
                              (demo.proofp x axioms thms atbl))
                         (logic.provablep (logic.conclusion x) axioms thms atbl)))
         (t logic.provable-listp-when-demo.proof-listp
            (implies (and (logic.appeal-listp x)
                          (demo.proof-listp x axioms thms atbl))
                     (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl))))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-demo.proofp))))


(defthms-flag
  ;; WARNING: THESE THEOREMS MUST BE LEFT DISABLED!
  ;;
  ;; Suppose this rule is enabled, and we are trying to prove (demo.proofp X
  ;; ...)  Using this rule, we backchain and try to show (logic.proofp X ...),
  ;; which causes our forcing rules to kick in and assert that the subproofs of
  ;; X are acceptable using logic.proofp.
  ;;
  ;; But this is horrible; if any of the subproofs are derived rules that only
  ;; demo.proofp understands, we end up stuck in forcing rounds that we cannot
  ;; relieve.  So, we should always be reasoning about some single layer and
  ;; never about previous layers.
  :thms ((proof demo.proofp-when-logic.proofp
                (implies (logic.proofp x axioms thms atbl)
                         (demo.proofp x axioms thms atbl)))
         (t demo.proof-listp-when-logic.proof-listp
            (implies (logic.proof-listp x axioms thms atbl)
                     (demo.proof-listp x axioms thms atbl))))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-demo.proofp
                              definition-of-logic.proofp))))

(in-theory (disable demo.proofp-when-logic.proofp demo.proof-listp-when-logic.proof-listp))

(defthm forcing-demo.proofp-of-logic.provable-witness
  ;; Corollary: Suppose F is any provable formula.  Then, the witnessing
  ;; proof of F is acceptable by demo.proofp.
  (implies (force (logic.provablep formula axioms thms atbl))
           (equal (demo.proofp (logic.provable-witness formula axioms thms atbl) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable demo.proofp-when-logic.proofp))))

