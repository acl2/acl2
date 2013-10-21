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
(local (include-book "proof-alteration"))
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


#| Doh, I broke it.


;; The deduction rule is basically the following:
;;
;;      |-_{T \Cup F} G
;;   ---------------------
;;       |-_{T} F -> G
;;
;; In other words, if you can prove some formula G by first assuming F is true,
;; then you can conclude F -> G.
;;
;; NOTE: This is actually only true when the input proof "admits deduction".
;; Loosely, a proof admits deduction with respect to F as long as (1) the proof
;; makes only modest use of induction, and (2) the proof never tries to
;; instantiate any of the variables of F.




;; Definition: Tainted Formulas.
;;
;; Suppose that T is a theory, F is a formula, and G is another formula.
;; Suppose that X is a proof of G from {T \Cup {F}}.  Recall that our goal is to
;; produce a proof of F -> G from T.  In other words, we want to "remove" uses
;; of the "assumption" F, and make the dependence on F explicit.
;;
;; Each step in the proof X is either an axiom, or a rule of inference applied
;; to previously proven formulas.  We are going to distinguish between those
;; portions of X which are "tainted" versus "untainted" by the assumption F.
;;
;;   - An axiomatic appeal is tainted by F exactly when it is an appeal to F
;;     itself.  For example, if our assumption, F, is the formula x = 'nil,
;;     then the only axiomatic appeals which are tainted by F are those appeals
;;     of the form ('axiom ('pequal* x 'nil)).  No other axiomatic appeals are
;;     tainted by F.
;;
;;   - A non-axiomatic appeal (i.e., an appeal with subproofs) is tainted by F
;;     exactly when one of its subproofs is tainted by F.  So for example, if as
;;     before our assumption x = 'nil, then the following appeal is tainted for
;;     any formula G, because one of its children is tainted by F:
;;
;;        ('expansion ('por* <G> ('pequal* x 'nil))
;;                    (('axiom ('pequal* x 'nil))))
;;
;; I could have tried to define "taintedp" to recognize the tainted proofs, but
;; instead I have defined "untaintedp" to recognize untainted proofs.  I think
;; that untaintedp is a nicer function, because in the list case it acts just
;; like a standard list recognizer like integerp, i.e., it operates via "and".
;; In contrast, "tainted-listp" would have to operate through "or", which I
;; think makes the rules about it less nice.

(mutual-recursion
 (defund untaintedp (x f)
   (declare (xargs :guard (and (logic.appealp x)
                               (logic.formulap f))))
   (if (mbt (logic.appealp x))
       (if (or (equal (logic.method x) 'axiom)
               (equal (logic.method x) 'theorem))
           (not (equal (logic.conclusion x) f))
         (untainted-listp (logic.subproofs x) f))
     nil))
 (defund untainted-listp (x f)
   (declare (xargs :guard (and (logic.appeal-listp x)
                               (logic.formulap f))))
   (if (consp x)
       (and (untaintedp (car x) f)
            (untainted-listp (cdr x) f))
     t)))

(defthm untainted-listp-when-not-consp
  (implies (not (consp x))
           (equal (untainted-listp x f)
                  t))
  :hints(("Goal" :in-theory (enable untainted-listp))))

(defthm untainted-listp-of-cons
  (equal (untainted-listp (cons a x) f)
         (and (untaintedp a f)
              (untainted-listp x f)))
  :hints(("Goal" :in-theory (enable untainted-listp))))

(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'proof)
              (booleanp (untaintedp x f))
            (booleanp (untainted-listp x f)))
          :rule-classes nil
          :hints(("Goal"
                  :in-theory (enable untaintedp untainted-listp)
                  :induct (logic.appeal-induction flag x)))))

 (defthm booleanp-of-untaintedp
   (booleanp (untaintedp x f))
   :hints(("Goal" :use ((:instance lemma (flag 'proof))))))

 (defthm booleanp-of-untainted-listp
   (booleanp (untaintedp x f))
   :hints(("Goal" :use ((:instance lemma (flag 'proof)))))))

(defthm untaintedp-of-car-when-untainted-listp
  (implies (untainted-listp x f)
           (equal (untaintedp (car x) f)
                  (consp x)))
  :hints(("Goal" :in-theory (enable untaintedp))))

(defthm untaintedp-of-cdr-when-untainted-listp
  (implies (untainted-listp x f)
           (untainted-listp (cdr x) f)))

(defthm forcing-untaintedp-when-axiom
  (implies (and (force (logic.appealp x))
                (equal (logic.method x) 'axiom))
           (equal (untaintedp x f)
                  (not (equal (logic.conclusion x) f))))
  :hints(("Goal" :in-theory (enable untaintedp))))

(defthm forcing-untaintedp-when-theorem
  (implies (and (force (logic.appealp x))
                (equal (logic.method x) 'theorem))
           (equal (untaintedp x f)
                  (not (equal (logic.conclusion x) f))))
  :hints(("Goal" :in-theory (enable untaintedp))))

(defthm forcing-untaintedp-when-non-axiom/theorem
  (implies (and (force (logic.appealp x))
                (not (equal (logic.method x) 'axiom))
                (not (equal (logic.method x) 'theorem)))
           (equal (untaintedp x f)
                  (untainted-listp (logic.subproofs x) f)))
  :hints(("Goal" :in-theory (enable untaintedp))))

(defthm untainted-listp-of-logic.subproofs-when-untainted-and-logic.appeal-step-okp
  (implies (and (logic.appeal-step-okp x axioms thms)
                (untaintedp x f)
                (logic.appealp x))
           (untainted-listp (logic.subproofs x) f))
  :hints(("Goal" :in-theory (enable untaintedp
                                    logic.appeal-step-okp
                                    logic.axiom-okp
                                    logic.theorem-okp))))

(defthm logic.axiom-okp-of-remove-all-when-untaintedp
  (implies (and (logic.appealp x)
                (untaintedp x f))
           (equal (logic.axiom-okp x (remove-all f axioms))
                  (logic.axiom-okp x axioms)))
  :hints(("Goal" :in-theory (enable logic.axiom-okp))))

(defthm logic.appeal-step-okp-of-remove-all-from-axioms-when-untaintedp
  (implies (and (logic.appealp x)
                (untaintedp x f))
           (equal (logic.appeal-step-okp x (remove-all f axioms) thms)
                  (logic.appeal-step-okp x axioms thms)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.theorem-okp-of-remove-all-when-untaintedp
  (implies (and (logic.appealp x)
                (untaintedp x f))
           (equal (logic.theorem-okp x (remove-all f thms))
                  (logic.theorem-okp x thms)))
  :hints(("Goal" :in-theory (enable logic.theorem-okp))))

(defthm logic.appeal-step-okp-of-remove-all-from-thms-when-untaintedp
  (implies (and (logic.appealp x)
                (untaintedp x f))
           (equal (logic.appeal-step-okp x axioms (remove-all f thms))
                  (logic.appeal-step-okp x axioms thms)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'proof)
              (implies (and (logic.appealp x)
                            (untaintedp x f))
                       (equal (logic.proofp x (remove-all f axioms) thms atbl)
                              (logic.proofp x axioms thms atbl)))
            (implies (and (logic.appeal-listp x)
                          (untainted-listp x f))
                     (equal (logic.proof-listp x (remove-all f axioms) thms atbl)
                            (logic.proof-listp x axioms thms atbl))))
          :rule-classes nil
          :hints(("Goal"
                  :induct (logic.appeal-induction flag x)
                  :in-theory (enable logic.proofp)))))

 (defthm logic.proofp-of-remove-all-from-axioms-when-untaintedp
   (implies (and (logic.appealp x)
                 (untaintedp x f))
            (equal (logic.proofp x (remove-all f axioms) thms atbl)
                   (logic.proofp x axioms thms atbl)))
   :hints(("Goal" :use ((:instance lemma (flag 'proof))))))

 (defthm logic.proof-listp-of-remove-all-from-axioms-when-untainted-listp
   (implies (and (logic.appeal-listp x)
                 (untainted-listp x f))
            (equal (logic.proof-listp x (remove-all f axioms) thms atbl)
                   (logic.proof-listp x axioms thms atbl)))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))


(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'proof)
              (implies (and (logic.appealp x)
                            (untaintedp x f))
                       (equal (logic.proofp x axioms (remove-all f thms) atbl)
                              (logic.proofp x axioms thms atbl)))
            (implies (and (logic.appeal-listp x)
                          (untainted-listp x f))
                     (equal (logic.proof-listp x axioms (remove-all f thms) atbl)
                            (logic.proof-listp x axioms thms atbl))))
          :rule-classes nil
          :hints(("Goal"
                  :induct (logic.appeal-induction flag x)
                  :in-theory (enable logic.proofp)))))

 (defthm logic.proofp-of-remove-all-from-thms-when-untaintedp
   (implies (and (logic.appealp x)
                 (untaintedp x f))
            (equal (logic.proofp x axioms (remove-all f thms) atbl)
                   (logic.proofp x axioms thms atbl)))
   :hints(("Goal" :use ((:instance lemma (flag 'proof))))))

 (defthm logic.proof-listp-of-remove-all-from-thms-when-untainted-listp
   (implies (and (logic.appeal-listp x)
                 (untainted-listp x f))
            (equal (logic.proof-listp x axioms (remove-all f thms) atbl)
                   (logic.proof-listp x axioms thms atbl)))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))




;; Definition: Admits Deduction.
;;
;; We say that X "admits deduction with respect to F" if the following hold:
;;
;;   (1) Whenever sigma is a substitution list used in a tainted appeal to
;;       instantiation, F/sigma = F.
;;
;;   (2) There are no tainted appeals to induction.
;;
;; For example, if as before F is the formula x = 'nil, then the following
;; proof admits deduction, because its substitution list [x <- x] does not
;; change F.
;;
;;   ('instantiation ('pequal* x 'nil)
;;                   (('axiom ('pequal* x 'nil)))
;;                   ((x . x)))
;;
;; However, the following proof does not admit deduction, because its
;; substitution list [x <- a] changes F.
;;
;;   ('instantiation ('pequal* a 'nil)
;;                   (('axiom ('pequal* x 'nil)))
;;                   ((x . a)))
;;
;; We will show that whenever a proof of G from {T \Cup F} admits deduction,
;; then we can transform it into a proof of F -> G from T.


;; BOZO this will also prohibit tainted appeals to reflection.  I don't know if
;; we care about that or how to handle that yet.

(encapsulate
 ()
 (local (defthm termination-lemma-1
          (implies (or (equal (logic.method x) 'expansion)
                       (equal (logic.method x) 'contraction)
                       (equal (logic.method x) 'associativity)
                       (equal (logic.method x) 'cut)
                       (equal (logic.method x) 'instantiation))
                   (equal (< (rank (first (logic.subproofs x)))
                             (rank x))
                          t))
          :hints(("Goal" :in-theory (enable logic.method logic.subproofs)))))

 (local (defthm termination-lemma-2
          (implies (equal (logic.method x) 'cut)
                   (equal (< (rank (second (logic.subproofs x)))
                             (rank x))
                          t))
          :hints(("Goal" :in-theory (enable logic.method logic.subproofs)))))

 (defund admits-deductionp (x f)
   (declare (xargs :guard (and (logic.appealp x)
                               (logic.formulap f))
                   :verify-guards nil))
   (let ((method (logic.method x))
         (subproofs (logic.subproofs x)))
     (cond ((untaintedp x f)
            ;; All untainted proofs admit deduction.  Note that this implicitly
            ;; covers the cases where x is an appeal to any non-f axiom, including
            ;; base-evaluation, propositional axioms, and functional equality
            ;; axioms.
            t)

           ((or (equal method 'axiom)
                (equal method 'theorem))
            ;; The only tainted axiom/theorem is F itself, and it is permissible.
            t)

           ((or (equal method 'expansion)
                (equal method 'contraction)
                (equal method 'associativity))
            ;; Tainted appeals to expansion, contraction, and associativity
            ;; are permissible as long as the subgoal admits deduction.
            (admits-deductionp (first subproofs) f))

           ((equal method 'cut)
            ;; Tainted appeals to cut are permissible as long as both subproofs
            ;; admit deduction.
            (and (admits-deductionp (first subproofs) f)
                 (admits-deductionp (second subproofs) f)))


           ((equal method 'instantiation)
            ;; Tainted appeals to instantiation are permissible as long as the
            ;; substitution list used does not change F, and the subgoal admits
            ;; deduction.
            (and (equal (logic.substitute-formula f (logic.extras x)) f)
                 (admits-deductionp (first subproofs) f)))

           (t
            ;; Other tainted appeals are not acceptable.  In particular,
            ;; tainted appeals to induction are not tolerated.
            nil)))))

(verify-guards admits-deductionp
  :hints(("Goal" :in-theory (enable logic.proofp))))

(defthm forcing-admits-deduction-when-untainted
  (implies (and (untaintedp x f)
                (force (logic.appealp x)))
           (admits-deductionp x f axioms thms atbl))
  :hints(("Goal" :in-theory (enable admits-deductionp))))

(defthm admits-deductionp-when-logic.axiom-okp
  (implies (and (logic.axiom-okp x axioms)
                (force (logic.appealp x)))
           (admits-deductionp x f axioms thms atbl))
  :hints(("Goal" :in-theory (enable admits-deductionp logic.axiom-okp))))

(defthm admits-deductionp-when-logic.theorem-okp
  (implies (and (logic.theorem-okp x thms)
                (force (logic.appealp x)))
           (admits-deductionp x f axioms thms atbl))
  :hints(("Goal" :in-theory (enable admits-deductionp logic.theorem-okp))))

(defthm admits-deductionp-when-logic.expansion-okp
  (implies (and (logic.expansion-okp x)
                (force (logic.appealp x)))
           (equal (admits-deductionp x f axioms thms atbl)
                  (if (untaintedp x f)
                      t
                    (admits-deductionp (first (logic.subproofs x)) f axioms thms atbl))))
  :hints(("Goal" :in-theory (enable admits-deductionp logic.expansion-okp))))

(defthm admits-deductionp-when-logic.contraction-okp
  (implies (and (logic.contraction-okp x)
                (force (logic.appealp x)))
           (equal (admits-deductionp x f axioms thms atbl)
                  (if (untaintedp x f)
                      t
                    (admits-deductionp (first (logic.subproofs x)) f axioms thms atbl))))
  :hints(("Goal" :in-theory (enable admits-deductionp logic.contraction-okp))))

(defthm admits-deductionp-when-logic.associativity-okp
  (implies (and (logic.associativity-okp x)
                (force (logic.appealp x)))
           (equal (admits-deductionp x f axioms thms atbl)
                  (if (untaintedp x f)
                      t
                    (admits-deductionp (first (logic.subproofs x)) f axioms thms atbl))))
  :hints(("Goal" :in-theory (enable admits-deductionp logic.associativity-okp))))

(defthm admits-deductionp-when-logic.cut-okp
  (implies (and (logic.cut-okp x)
                (force (logic.appealp x)))
           (equal (admits-deductionp x f axioms thms atbl)
                  (if (untaintedp x f)
                      t
                    (and (admits-deductionp (first (logic.subproofs x)) f axioms thms atbl)
                         (admits-deductionp (second (logic.subproofs x)) f axioms thms atbl)))))
  :hints(("Goal" :in-theory (enable admits-deductionp logic.cut-okp))))

(defthm admits-deductionp-when-logic.instantiation-okp
  (implies (and (logic.instantiation-okp x)
                (force (logic.appealp x)))
           (equal (admits-deductionp x f axioms thms atbl)
                  (if (untaintedp x f)
                      t
                    (and (equal (logic.substitute-formula f (logic.extras x)) f)
                         (admits-deductionp (first (logic.subproofs x)) f axioms thms atbl)))))
  :hints(("Goal" :in-theory (enable admits-deductionp logic.instantiation-okp))))



;; Suppose X is a proof of A from some database which admits deduction
;; w.r.t. F.  Then, the following builder should construct a proof of F -> A
;; from (remove-all f axioms).

(defund deduction-law-bldr (x f axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formulap f)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl)
                              (logic.proofp x axioms thms atbl)
                              (admits-deductionp x f axioms thms atbl))
                  :verify-guards nil))
  (if (not (mbt (logic.appealp x)))
      ;; stupid hack for termination
      nil
    (let ((method (logic.method x))
          (subproofs (logic.subproofs x)))
      (cond
       ((untaintedp x f)
        ;; If X is not tainted by F, then we can prove A without ever referring
        ;; to F.  We can then just expand this proof with ~F.  Note that this
        ;; case entirely subsumes any uses of 'propositional-schema,
        ;; 'functional-equality, 'base-eval, and any axioms other than F.
        (build.expansion (logic.pnot f) x))

       ((or (equal method 'axiom)
            (equal method 'theorem))
        ;; X is an axiom/theorem but it is tainted.  The only possibility is
        ;; that X is an axiomatic appeal to F itself.  We need to prove ~F v F,
        ;; which is really easy since that's a propositional axiom.
        (build.propositional-schema f))

       ((equal method 'expansion)
        ;; X is a tainted appeal to expansion.  Then, it has the form
        ;; ('expansion ('por* P Q) ([proof of Q])).  We will recursively
        ;; construct a proof of ~F v Q, then by Disjoined Left Expansion we
        ;; obtain ~F v (P v Q).
        (build.disjoined-left-expansion
         (deduction-law-bldr (first subproofs) f axioms thms atbl)
         (logic.vlhs (logic.conclusion x))))

       ((equal method 'contraction)
        ;; X is a tainted appeal to contraction.  Then, it has the form
        ;; ('contraction P ([proof of P v P])).  We recursively construct a
        ;; proof of ~F v (P v P).  We can then use disjoined contraction to
        ;; produce a proof of ~F v P.
        (build.disjoined-contraction
         (deduction-law-bldr (first subproofs) f axioms thms atbl)))

       ((equal method 'associativity)
        ;; X is a tainted appeal to associativity.  Then, it has the form
        ;; ('associativity ('por* ('por* P Q) R) ([proof of ('por* P ('por* Q
        ;; R))]).  We will recursively construct a proof of ~F v (P v (Q v R))
        ;; and then use disjoined left associativity to produce a proof of
        ;; ~F v ((P v Q) v R)
        (build.disjoined-associativity
         (deduction-law-bldr (first subproofs) f axioms thms atbl)))

       ((equal method 'cut)
        ;; X is a tainted appeal to cut.  Then, it has the form ('cut
        ;; ('por* Q R) [(proof of P v Q), (proof of ~P v R)])).  We will
        ;; recursively construct proofs of ~F v (P v Q) and ~F v (~P v R),
        ;; then use disjoined cut to produce a proof of ~F v (Q v R).
        (build.disjoined-cut
         (deduction-law-bldr (first subproofs) f axioms thms atbl)
         (deduction-law-bldr (second subproofs) f axioms thms atbl)))

       ((equal method 'instantiation)
        ;; X is a tainted appeal to instantiation.  Then, it has the form
        ;; ('instantiation P/sigma P sigma).  We will recursively construct a
        ;; proof of ~F v P.  Then, since X admits deduction, we know that sigma
        ;; mentions none of the variables in F, so by instantiation with sigma
        ;; we conclude (~F v P)/sigma = ~F/sigma v P/sigma, which is ~F v
        ;; P/sigma.
        (build.instantiation
         (deduction-law-bldr (first subproofs) f axioms thms atbl)
         (logic.extras x)))

       (t
        ;; This case should never occur
        nil)))))

(local (defthm equal-when-dual-logic.pnots
         (implies (and (equal (logic.fmtype a) 'pnot*)
                       (equal (logic.fmtype b) 'pnot*)
                       (force (logic.formulap a))
                       (force (logic.formulap b)))
                  (equal (equal a b)
                         (equal (logic.~arg a) (logic.~arg b))))
         :rule-classes ((:rewrite :backchain-limit-lst 0))
         :hints(("Goal" :in-theory (enable logic.formulap logic.~arg logic.fmtype)))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (logic.appealp x)
                        (logic.formulap f)
                        (logic.formula-listp axioms)
                        (logic.formula-listp thms)
                        (logic.arity-tablep atbl)
                        (logic.proofp x axioms thms atbl)
                        (admits-deductionp x f axioms thms atbl))
                   (and (logic.appealp (deduction-law-bldr x f axioms thms atbl))
                        (equal (logic.conclusion (deduction-law-bldr x f axioms thms atbl))
                               (logic.por (logic.pnot f) (logic.conclusion x)))))
          :hints(("Goal"
                  :in-theory (enable deduction-law-bldr
                                     admits-deductionp
                                     logic.proofp)
                  :induct (deduction-law-bldr x f axioms thms atbl)))))

 (defthm forcing-logic.appealp-of-deduction-law-bldr
   (implies (force (and (logic.appealp x)
                        (logic.formulap f)
                        (logic.formula-listp axioms)
                        (logic.formula-listp thms)
                        (logic.arity-tablep atbl)
                        (logic.proofp x axioms thms atbl)
                        (admits-deductionp x f axioms thms atbl)))
            (logic.appealp (deduction-law-bldr x f axioms thms atbl))))

 (defthm forcing-logic.conclusion-of-deduction-law-bldr
   (implies (force (and (logic.appealp x)
                        (logic.formulap f)
                        (logic.formula-listp axioms)
                        (logic.formula-listp thms)
                        (logic.arity-tablep atbl)
                        (logic.proofp x axioms thms atbl)
                        (admits-deductionp x f axioms thms atbl)))
            (equal (logic.conclusion (deduction-law-bldr x f axioms thms atbl))
                   (logic.por (logic.pnot f) (logic.conclusion x))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(verify-guards deduction-law-bldr
 :hints(("Goal" :in-theory (enable logic.proofp admits-deductionp))))


(defthm forcing-logic.proofp-of-deduction-law-bldr
  (implies (force (and (logic.appealp x)
                       (logic.formulap f)
                       (logic.formula-listp axioms)
                       (logic.formula-listp thms)
                       (logic.arity-tablep atbl)
                       (logic.proofp x axioms thms atbl)
                       (admits-deductionp x f axioms thms atbl)))
           (logic.proofp (deduction-law-bldr x f axioms thms atbl)
                         (remove-all f axioms)
                         (remove-all f thms)
                         atbl))
  :hints(("Goal" :in-theory (enable deduction-law-bldr
                                    admits-deductionp
                                    logic.proofp))))


|#