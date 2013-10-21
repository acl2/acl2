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
(include-book "prop-list")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(dd.open "disjoined-subset.tex")


;; We introduce builders to prove B1 v ... v Bm from A1 v ... v An, where
;; [A1,...,An] is a subset of [B1,...,Bm].
;;
;; We actually introduce several such builders.  The first of these is called
;; build.generic-subset, and can construct the proof in the general case.  But
;; it is not very efficient.  To address this, we introduce some variants for
;; the special purposes of proving list reversals, ordered subsets, and the
;; like.  In the end, we create an "adaptive" builder which tries to
;; semi-intelligently choose an efficient proof method.


(defund@ build.multi-or-expansion-step (base as)
  ;; Derive P v A1 v ... v An from P v Ai
  ;; Note: this is basically like Shankar's function M2-Proof-Step
  (declare (xargs :guard (and (logic.appealp base)
                              (logic.formula-listp as)
                              (@match (proof base (v P Ai)))
                              (memberp (@formula Ai) as))
                  :verify-guards nil))
  (@extend ((formula (car as) A1))
           (if (and (consp as)
                    (consp (cdr as)))
               (cond ((equal (@formula A1) (@formula Ai))
                      (@derive ((v P A1)                         (@given base))
                               ((v P (v A1 (v A2 (v dots An))))  (build.disjoined-right-expansion @- (logic.disjoin-formulas (cdr as))))))
                     (t
                      (@derive ((v P (v A2 (v dots An)))         (build.multi-or-expansion-step base (cdr as)))
                               ((v P (v A1 (v A2 (v dots An))))  (build.disjoined-left-expansion @- (@formula A1))))))
             ;; Else there is only one A, so it must be Ai
             (@derive ((v P Ai) (logic.appeal-identity base))))))

(encapsulate
 ()
 (local (in-theory (enable build.multi-or-expansion-step)))

 (defthm build.multi-or-expansion-step-under-iff
   (iff (build.multi-or-expansion-step base as)
        t))

 (defthm@ lemma-for-forcing-logic.appealp-of-build.multi-or-expansion-step
  ;; BOZO add to disjoined-subset.lisp
  (implies (and (logic.appealp base)
                (logic.formula-listp as)
                (@match (proof base (v P Ai)))
                (memberp (@formula Ai) as))
           (and (logic.appealp (build.multi-or-expansion-step base as))
                (equal (logic.conclusion (build.multi-or-expansion-step base as))
                       (logic.por (@formula P) (logic.disjoin-formulas as)))))
  :rule-classes nil)

 (defthm@ forcing-logic.appealp-of-build.multi-or-expansion-step
   (implies (force (and (logic.appealp base)
                        (logic.formula-listp as)
                        (@match (proof base (v P Ai)))
                        (memberp (@formula Ai) as)))
            (equal (logic.appealp (build.multi-or-expansion-step base as))
                   t))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-build.multi-or-expansion-step)))))

 (defthm@ forcing-logic.conclusion-of-build.multi-or-expansion-step
   (implies (force (and (logic.appealp base)
                        (logic.formula-listp as)
                        (@match (proof base (v P Ai)))
                        (memberp (@formula Ai) as)))
            (equal (logic.conclusion (build.multi-or-expansion-step base as))
                   (logic.por (@formula P) (logic.disjoin-formulas as))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-build.multi-or-expansion-step)))))

 (verify-guards build.multi-or-expansion-step)

 (defthm@ forcing-logic.proofp-of-build.multi-or-expansion-step
   (implies (force (and (logic.appealp base)
                        (logic.formula-listp as)
                        (@match (proof base (v P Ai)))
                        (memberp (@formula Ai) as)
                        ;; ---
                        (logic.formula-list-atblp as atbl)
                        (logic.proofp base axioms thms atbl)))
            (equal (logic.proofp (build.multi-or-expansion-step base as) axioms thms atbl)
                   t))))





(defund@ build.multi-or-expansion (base as)
  ;; Derive A1 v ... v An from Ai v Aj for any 1 <= i,j <= n
  ;; Note: this is basically like Shankar's function "M2-Proof"
  (declare (xargs :guard (and (logic.appealp base)
                              (logic.formula-listp as)
                              (@match (proof base (v Ai Aj)))
                              (memberp (@formula Ai) as)
                              (memberp (@formula Aj) as))))

  (if (consp as)
      (@extend ((formula (car as) A1))
        (cond ((equal (@formula Ai) (@formula Aj))
               (@derive ((v Ai Ai)                  (@given base))
                        (Ai                         (build.contraction @-))
                        ((v A1 (v dots An))         (build.multi-expansion @- as))))
              ((equal (@formula Ai) (@formula A1))
               (@derive ((v A1 Aj)                  (@given base))
                        ((v A1 (v dots An))         (build.multi-or-expansion-step @- (cdr as)))))
              ((equal (@formula Aj) (@formula A1))
               (@derive ((v Ai A1)                  (@given base))
                        ((v A1 Ai)                  (build.commute-or @-))
                        ((v A1 (v dots An))         (build.multi-or-expansion-step @- (cdr as)))))
              (t
               (@derive ((v A2 (v dots An))         (build.multi-or-expansion base (cdr as)))
                        ((v A1 (v A2 (v dots An)))  (build.expansion (@formula A1) @-))))))
    ;; Degenerate case.
    (logic.appeal-identity base)))

(encapsulate
 ()
 (local (in-theory (enable build.multi-or-expansion)))

 (defthm build.multi-or-expansion-under-iff
   (iff (build.multi-or-expansion base as)
        t))

 (defthm@ forcing-logic.appealp-of-build.multi-or-expansion
   (implies (force (and (logic.appealp base)
                        (logic.formula-listp as)
                        (@match (proof base (v Ai Aj)))
                        (memberp (@formula Ai) as)
                        (memberp (@formula Aj) as)))
            (equal (logic.appealp (build.multi-or-expansion base as))
                   t)))

 (defthm@ forcing-logic.conclusion-of-build.multi-or-expansion
   (implies (force (and (logic.appealp base)
                        (logic.formula-listp as)
                        (@match (proof base (v Ai Aj)))
                        (memberp (@formula Ai) as)
                        (memberp (@formula Aj) as)))
            (equal (logic.conclusion (build.multi-or-expansion base as))
                   (logic.disjoin-formulas as)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-build.multi-or-expansion
   (implies (force (and (logic.appealp base)
                        (logic.formula-listp as)
                        (@match (proof base (v Ai Aj)))
                        (memberp (@formula Ai) as)
                        (memberp (@formula Aj) as)
                        ;; ---
                        (force (logic.formula-list-atblp as atbl))
                        (force (logic.proofp base axioms thms atbl))))
            (equal (logic.proofp (build.multi-or-expansion base as) axioms thms atbl)
                   t))))



(defderiv build.generic-subset-step-lemma-1
  :from   ((proof x (v (v P A) P)))
  :derive (v P A)
  :proof  (@derive ((v (v P A) P)  (@given x))
                   ((v P (v P A))  (build.commute-or @-))
                   ((v (v P P) A)  (build.associativity @-))
                   ((v A (v P P))  (build.commute-or @-))
                   ((v A P)        (build.disjoined-contraction @-))
                   ((v P A)        (build.commute-or @-))))

(defund@ build.generic-subset-step (proof as)
  ;; Derive A1 v ... v An from (Ai v Aj) v (A1 v ... v An)
  ;;
  ;; I originally based this on Shankar's M3-Proof function, but since then
  ;; I've tweaked it slightly and it no now uses multi-or-expansion-step
  ;; instead of multi-or-expansion.  This seems to save about 4-5% off of
  ;; proofs of the generic subset builder.
  (declare (xargs :guard (and (logic.formula-listp as)
                              (logic.appealp proof)
                              (@match (proof proof (v (v Ai Aj) A1-An)))
                              (memberp (@formula Ai) as)
                              (memberp (@formula Aj) as)
                              (equal (@formula A1-An) (logic.disjoin-formulas as)))))
  (@derive
   ((v (v Ai Aj) A1-An)     (@given proof))
   ((v A1-An (v Ai Aj))     (build.commute-or @-))
   ((v (v A1-An Ai) Aj)     (build.associativity @-))
   ((v (v A1-An Ai) A1-An)  (build.multi-or-expansion-step @- as))
   ((v A1-An Ai)            (build.generic-subset-step-lemma-1 @-))
   ((v A1-An A1-An)         (build.multi-or-expansion-step @- as))
   (A1-An                   (build.contraction @-))))

(encapsulate
 ()
 (local (in-theory (enable build.generic-subset-step)))

 (defthm build.generic-subset-step-under-iff
   (iff (build.generic-subset-step proof as)
        t))

 (defthm@ forcing-logic.appealp-of-build.generic-subset-step
   (implies (force (and (logic.formula-listp as)
                        (logic.appealp proof)
                        (@match (proof proof (v (v Ai Aj) A1-An)))
                        (memberp (@formula Ai) as)
                        (memberp (@formula Aj) as)
                        (equal (@formula A1-An) (logic.disjoin-formulas as))))
            (equal (logic.appealp (build.generic-subset-step proof as))
                   t)))

 (verify-guards build.generic-subset-step)

 (defthm@ forcing-logic.conclusion-of-build.generic-subset-step
   (implies (force (and (logic.formula-listp as)
                        (logic.appealp proof)
                        (@match (proof proof (v (v Ai Aj) A1-An)))
                        (memberp (@formula Ai) as)
                        (memberp (@formula Aj) as)
                        (equal (@formula A1-An) (logic.disjoin-formulas as))))
            (equal (logic.conclusion (build.generic-subset-step proof as))
                   (logic.disjoin-formulas as)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-build.generic-subset-step
   (implies (force (and (logic.formula-listp as)
                        (logic.appealp proof)
                        (@match (proof proof (v (v Ai Aj) A1-An)))
                        (memberp (@formula Ai) as)
                        (memberp (@formula Aj) as)
                        (equal (@formula A1-An) (logic.disjoin-formulas as))
                        ;; ---
                        (logic.formula-list-atblp as atbl)
                        (logic.proofp proof axioms thms atbl)))
            (equal (logic.proofp (build.generic-subset-step proof as) axioms thms atbl)
                   t))))




;: build.generic-subset                               Cost: 12(n^2) + x
;: Derive B1 v ... v Bm
;:   from A1 v ... v An,
;:   where {A1 ... An} is a subset of {B1 ... Bm}
;:
;; Derivation. (defined by induction on n)
;;
;; Base Case:   n = 1                                     Cost: n + x
;;   1. Ai                Given
;;   2. B1 v ... v Bm     Multi Expansion
;;
;; Base Case:   n = 2                                     Cost: 6n + x
;;   1. Ai v Aj
;;   2. B1 v ... v Bm     Multi Or Expansion
;;
;; Induction Case:  n >= 3                                Cost: 12n + x
;;   Let F = (A1 v A2).
;;   F v (A3 v (A4 v ... v An)) is a disjunction of n-1 formulas.
;;   Inductively assume we can prove F v (B1 v ... v Bm) from a proof
;;   of F v (A3 v ... v An).
;;
;; Derivation.
;;   1.   A1 v (A2 v ... v An)         Given
;;   2.   (A1 v A2) v (A3 v ... v An)  Associativity
;;   2'.  F v (A3 v ... v An)          (By the definition of F)
;;   3.   F v (B1 v ... v Bm)          Inductive Hypothesis
;;   3'.  (A1 v A2) v (B1 v ... v Bm)  (By the definition of F)
;;   4.   B1 v B2 v ... v Bm           Disjoined-Subset-Step
;;
;;
;; Note: This is basically like Shankar's function "M-Proof."  We take two
;; lists of formulas, (A1 ... An) and (B1 ... Bm), where each A occurs in the
;; list of B's.  We also take, as another input, a proof of A1 v A2 v ... v An.
;; We construct a proof of B1 v B2 v ... v Bm.  Note that both n,m must be >=
;; 1; i.e., we must have non-empty lists of formulas.

(defund@ build.generic-subset (as bs proof)
  ;; Derive B1 v ... v Bm from A1 v ... v An, where as are a subset of bs
  ;; Note: this is basically like Shankar's function "M-Proof"
  (declare (xargs :guard (and (logic.formula-listp bs)
                              (subsetp as bs)
                              (consp as)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (logic.disjoin-formulas as)))
                  :measure (len as)
                  :verify-guards nil))
  (@extend ((formula (first as) A1)
            (formula (second as) A2)
            (formula (third as) A3))
    (cond ((not (consp as))
           ;; Degenerate case -- this isn't even allowed by our guard
           (logic.appeal-identity proof))

          ((not (consp (cdr as)))
           ;; as = [A1]
           (@derive (A1                   (@given proof))
                    ((v B1 (v dots Bn))   (build.multi-expansion @- bs))))

          ((not (consp (cdr (cdr as))))
           ;; as = [A1 A2]
           (@derive ((v A1 A2)            (@given proof))
                    ((v B1 (v dots Bn))   (build.multi-or-expansion @- bs))))

          (t
           ;; as = [A1 A2 A3 ...]
           (@derive ((v A1 (v A2 (v A3 (v dots An))))   (@given proof))
                    ((v (v A1 A2) (v A3 (v dots An)))   (build.associativity @-))
                    ((v (v A1 A2) (v B1 (v dots Bm)))   (build.generic-subset (cons (@formula (v A1 A2)) (cdr (cdr as)))
                                                                              (cons (@formula (v A1 A2)) bs)
                                                                              @-))
                    ((v B1 (v dots Bm))                 (build.generic-subset-step @- bs)))))))

(encapsulate
 ()
 (local (in-theory (enable build.generic-subset)))

 (defthm build.generic-subset-under-iff
   (iff (build.generic-subset as bs proof)
        t))

 (defthm lemma-for-forcing-logic.appealp-of-build.generic-subset
   (implies (and (logic.formula-listp bs)
                 (subsetp as bs)
                 (consp as)
                 (logic.appealp proof)
                 (equal (logic.conclusion proof) (logic.disjoin-formulas as)))
            (and (logic.appealp (build.generic-subset as bs proof))
                 (equal (logic.conclusion (build.generic-subset as bs proof))
                        (logic.disjoin-formulas bs))))
   :rule-classes nil)

 (defthm forcing-logic.appealp-of-build.generic-subset
   (implies (force (and (logic.formula-listp bs)
                        (logic.appealp proof)
                        (subsetp as bs)
                        (consp as)
                        (equal (logic.conclusion proof) (logic.disjoin-formulas as))))
            (equal (logic.appealp (build.generic-subset as bs proof))
                   t))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-build.generic-subset)))))

 (defthm forcing-logic.conclusion-of-build.generic-subset
   (implies (force (and (logic.formula-listp bs)
                        (logic.appealp proof)
                        (subsetp as bs)
                        (consp as)
                        (equal (logic.conclusion proof) (logic.disjoin-formulas as))))
            (equal (logic.conclusion (build.generic-subset as bs proof))
                   (logic.disjoin-formulas bs)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-build.generic-subset)))))

 (verify-guards build.generic-subset)

 (defthm forcing-logic.proofp-of-build.generic-subset
   (implies (force (and (logic.formula-listp bs)
                        (logic.appealp proof)
                        (subsetp as bs)
                        (consp as)
                        (equal (logic.conclusion proof) (logic.disjoin-formulas as))
                        ;; ---
                        (logic.formula-list-atblp bs atbl)
                        (logic.proofp proof axioms thms atbl)))
            (equal (logic.proofp (build.generic-subset as bs proof) axioms thms atbl)
                   t))))






;; We now introduce build.rev-disjunction, which efficiently builds a proof of
;; (an v ... v a1) from a proof of (a1 v ... v an).  We could already build
;; such proofs with our generic subset builder, but this builder is much more
;; efficient.  For simple tests of the variety shown at the end of this
;; section, we obtain the following savings in terms of "rank":
;;
;;    n   generic-subset   rev-disjunction    savings
;;   ----------------------------------------------------
;;     1             5                 5           0%
;;     2            38                38           0%
;;     3         1,864               771          59%
;;     5        15,194             3,605          76%
;;    10       176,269            18,670          89%
;;    20     2,042,969            83,000          96%
;;    30     8,936,569           192,930          98%
;;   ----------------------------------------------------
;;
;; Our proof construction mirrors the "revappend" function, and is implemented
;; as build.revappend-disjunction.  Most users should call build.rev-disjunction
;; instead, which hides the accumulator.

(defund@ build.revappend-disjunction (todo done proof)
  ;; Derive tn v ... v t1 v d1 v ... v dm from (t1 v ... v tn) v (d1 v ... v dm)
  (declare (xargs :guard (and (logic.formula-listp todo)
                              (logic.formula-listp done)
                              (or (consp todo) (consp done))
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (cond ((and (consp todo)
                                                 (consp done))
                                            (logic.por (logic.disjoin-formulas todo)
                                                 (logic.disjoin-formulas done)))
                                           ((consp todo)
                                            (logic.disjoin-formulas todo))
                                           (t
                                            (logic.disjoin-formulas done)))))
                  :verify-guards nil))
  (if (and (consp todo)
           (consp (cdr todo)))
      (if (consp done)
          (@derive
           ((v (v t1 t2-tn) d1-dm)     (@given proof))
           ((v d1-dm (v t1 t2-tn))     (build.commute-or @-))
           ((v (v d1-dm t1) t2-tn)     (build.associativity @-))
           ((v t2-tn (v d1-dm t1))     (build.commute-or @-))
           ((v t2-tn (v t1 d1-dm))     (build.disjoined-commute-or @-))
           ((v tn-t1 dm-d1)            (build.revappend-disjunction (cdr todo) (cons (car todo) done) @-)))
        (@derive
         ((v t1 t2-n)                  (@given proof))
         ((v t2-n t1)                  (build.commute-or @-))
         (tn-t1                        (build.revappend-disjunction (cdr todo) (list (car todo)) @-))))
    ;; Otherwise, the todo list is only one long, so we already have the proof
    ;; we were looking for.
    (logic.appeal-identity proof)))


(encapsulate
 ()
 (local (in-theory (enable build.revappend-disjunction)))

 (defthm build.revappend-disjunction-under-iff
   (iff (build.revappend-disjunction todo done proof)
        t))

 (local (defthm lemma
          (implies (and (logic.formula-listp todo)
                        (logic.formula-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp todo)
                                           (consp done))
                                      (logic.por (logic.disjoin-formulas todo)
                                                 (logic.disjoin-formulas done)))
                                     ((consp todo)
                                      (logic.disjoin-formulas todo))
                                     (t
                                      (logic.disjoin-formulas done)))))
                   (and (logic.appealp (build.revappend-disjunction todo done proof))
                        (equal (logic.conclusion (build.revappend-disjunction todo done proof))
                               (logic.disjoin-formulas (app (rev todo) done)))))))

 (defthm forcing-logic.appealp-of-build.revappend-disjunction
   (implies (force (and (logic.formula-listp todo)
                        (logic.formula-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp todo)
                                           (consp done))
                                      (logic.por (logic.disjoin-formulas todo)
                                                 (logic.disjoin-formulas done)))
                                     ((consp todo)
                                      (logic.disjoin-formulas todo))
                                     (t
                                      (logic.disjoin-formulas done))))))
            (equal (logic.appealp (build.revappend-disjunction todo done proof))
                   t)))

 (defthm forcing-logic.conclusion-of-build.revappend-disjunction
   (implies (force (and (logic.formula-listp todo)
                        (logic.formula-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp todo)
                                           (consp done))
                                      (logic.por (logic.disjoin-formulas todo)
                                                 (logic.disjoin-formulas done)))
                                     ((consp todo)
                                      (logic.disjoin-formulas todo))
                                     (t
                                      (logic.disjoin-formulas done))))))
            (equal (logic.conclusion (build.revappend-disjunction todo done proof))
                   (logic.disjoin-formulas (app (rev todo) done))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (verify-guards build.revappend-disjunction)

 (defthm forcing-logic.proofp-of-build.revappend-disjunction
   (implies (force (and (logic.formula-listp todo)
                        (logic.formula-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp todo)
                                           (consp done))
                                      (logic.por (logic.disjoin-formulas todo)
                                                 (logic.disjoin-formulas done)))
                                     ((consp todo)
                                      (logic.disjoin-formulas todo))
                                     (t
                                      (logic.disjoin-formulas done))))
                        ;; ---
                        (logic.proofp proof axioms thms atbl)))
            (equal (logic.proofp (build.revappend-disjunction todo done proof) axioms thms atbl)
                   t))))



(defund build.rev-disjunction (x proof)
  ;; Derive tn v ... v t1 from t1 v ... v tn
  (declare (xargs :guard (and (consp x)
                              (logic.formula-listp x)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (logic.disjoin-formulas x)))
                  ;; As far as Milawa is concerned, build.rev-disjunction is going to be
                  ;; an alias for build.generic-subset.  This way we don't have to write
                  ;; any proofs about it, we can just let it expand.
                  :export (build.generic-subset x (fast-rev x) proof)))
  (build.revappend-disjunction x nil proof))

(encapsulate
 ()
 (local (in-theory (enable build.rev-disjunction)))

 (defthm build.rev-disjunction-under-iff
   (iff (build.rev-disjunction x proof)
        t))

 (defthm forcing-logic.appealp-of-build.rev-disjunction
   (implies (force (and (consp x)
                        (logic.formula-listp x)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (logic.disjoin-formulas x))))
            (equal (logic.appealp (build.rev-disjunction x proof))
                   t)))

 (defthm forcing-logic.conclusion-of-build.rev-disjunction
   (implies (force (and (consp x)
                        (logic.formula-listp x)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (logic.disjoin-formulas x))))
            (equal (logic.conclusion (build.rev-disjunction x proof))
                   (logic.disjoin-formulas (rev x))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm forcing-logic.proofp-of-build.rev-disjunction
   (implies (force (and (consp x)
                        (logic.formula-listp x)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (logic.disjoin-formulas x))
                        ;; ---
                        (logic.proofp proof axioms thms atbl)))
            (equal (logic.proofp (build.rev-disjunction x proof) axioms thms atbl)
                   t))))



;; Our test data above was obtained by just running this let expression and
;; commenting out the appropriate number of lines.
;;
;; (let* ((formulas (list
;;                   (logic.pequal 'a1 'a1-prime)
;;                   (logic.pequal 'a2 'a2-prime)
;;                   (logic.pequal 'a3 'a3-prime)
;;                   (logic.pequal 'a4 'a4-prime)
;;                   (logic.pequal 'a5 'a5-prime)
;;                   (logic.pequal 'a6 'a6-prime)
;;                   (logic.pequal 'a7 'a7-prime)
;;                   (logic.pequal 'a8 'a8-prime)
;;                   (logic.pequal 'a9 'a9-prime)
;;                   (logic.pequal 'a10 'a10-prime)
;;                   ;(logic.pequal 'a11 'a11-prime)
;;                   ;(logic.pequal 'a12 'a12-prime)
;;                   ;(logic.pequal 'a13 'a13-prime)
;;                   ;(logic.pequal 'a14 'a14-prime)
;;                   ;(logic.pequal 'a15 'a15-prime)
;;                   ;(logic.pequal 'a16 'a16-prime)
;;                   ;(logic.pequal 'a17 'a17-prime)
;;                   ;(logic.pequal 'a18 'a18-prime)
;;                   ;(logic.pequal 'a19 'a19-prime)
;;                   ;(logic.pequal 'a20 'a20-prime)
;;                   ;(logic.pequal 'a21 'a21-prime)
;;                   ;(logic.pequal 'a22 'a22-prime)
;;                   ;(logic.pequal 'a23 'a23-prime)
;;                   ;(logic.pequal 'a24 'a24-prime)
;;                   ;(logic.pequal 'a25 'a25-prime)
;;                   ;(logic.pequal 'a26 'a26-prime)
;;                   ;(logic.pequal 'a27 'a27-prime)
;;                   ;(logic.pequal 'a28 'a28-prime)
;;                   ;(logic.pequal 'a29 'a29-prime)
;;                   ;(logic.pequal 'a30 'a30-prime)
;;                   ))
;;        (axiom  (build.axiom (logic.disjoin-formulas formulas)))
;;        (proof1 (build.generic-subset formulas (rev formulas) axiom))
;;        (proof2 (build.rev-disjunction formulas axiom)))
;;   (list (list 'OK (equal (logic.conclusion proof1)
;;                          (logic.conclusion proof2)))
;;         (list 'generic-rank (rank proof1))
;;         (list 'rev-rank (rank proof2))))






;; We now introduce the ordered subset bldr, which is more efficient than the
;; generic builder when applied to large, ordered subsets (such as are obtained
;; by applying remove-duplicates or remove-all to a list).  Note that for small
;; lists, the generic builder is actually better.
;;
;;   n     generic-subset       ordered-subset       savings
;; ----------------------------------------------------------------
;;    1              64                 818           Lose
;;    2             523               6,626           Lose
;;    3           8,557              17,378           Lose
;;    4          25,380              33,074           Lose
;;    5          53,714              55,555           Lose
;;    6         103,552              79,298           23%
;;   10         579,540             231,074           60%
;;   15       2,306,725             532,034           77%
;;   20       6,263,860             956,594           85%
;;
;; Note that our test data comes from the experiment shown at the end of this
;; section.

(defund@ build.ordered-subset-aux (sub sup done proof)
  ;; Derive [bm,...,b1,d1,...,dk] from [d1,...,dk] v [a1,...,an]
  ;; where [a1,...,an] is an ordered subset of [b1,...,bm]
  (declare (xargs :guard (and (logic.formula-listp sup)
                              (ordered-subsetp sub sup)
                              (logic.formula-listp done)
                              (or (consp sub) (consp done))
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (cond ((and (consp sub) (consp done))
                                            (logic.por (logic.disjoin-formulas done)
                                                       (logic.disjoin-formulas sub)))
                                           ((consp sub)
                                            (logic.disjoin-formulas sub))
                                           (t
                                            (logic.disjoin-formulas done)))))
                  :verify-guards nil
                  :measure (+ (rank sub) (rank sup))))
  (@extend ((formula (car sub) A1)
            (formula (car sup) B1))
    (cond ((and (consp sub)
                (consp sup))
           (if (consp done)
               (if (equal (@formula A1) (@formula B1))
                   (if (consp (cdr sub))
                       (@derive
                        ;; Case 1: [a1,a2...], [b1=a1,...], [d1,...]
                        ;; Step Goal: [a1,d1,...,dk] v [a2,...,an]
                        ((v D1-Dk (v A1 A2-An))  (@given proof))
                        ((v D1-Dk (v A2-An A1))  (build.disjoined-commute-or @-))
                        ((v (v D1-Dk A2-An) A1)  (build.associativity @-))
                        ((v A1 (v D1-Dk A2-An))  (build.commute-or @-))
                        ((v (v A1 D1-Dk) A2-An)  (build.associativity @-))
                        ((v Bm-B1 D1-Dk)         (build.ordered-subset-aux (cdr sub) (cdr sup) (cons (car sup) done) @-)))
                     (@derive
                      ;; Case 2: [a1], [b1=a1,...], [d1,...]
                      ;; Step Goal: [a1,d1,...,dk]
                      ((v D1-Dk A1)     (@given proof))
                      ((v A1 D1-Dk)     (build.commute-or @-))
                      ((v Bm-B1 D1-Dk)  (build.ordered-subset-aux (cdr sub) (cdr sup) (cons (car sup) done) @-))))
                 ;; Case 3: [a1,...], [b1!=a1,...], [d1,...]
                 ;; Step Goal: [b1,d1,...,dk] v [a1,...,an]
                 (@derive
                  ((v D1-Dk A1-An)         (@given proof))
                  ((v B1 (v D1-Dk A1-An))  (build.expansion (@formula B1) @-))
                  ((v (v B1 D1-Dk) A1-An)  (build.associativity @-))
                  ((v Bm-B1 D1-Dk)         (build.ordered-subset-aux sub (cdr sup) (cons (car sup) done) @-))))
             (if (equal (@formula A1) (@formula B1))
                 ;; Case 4: [a1,...], [b1=a1,...], done = empty
                 ;; Step Goal: a1..n
                 (@derive
                  (A1-An  (@given proof))
                  (Bm-B1  (build.ordered-subset-aux (cdr sub) (cdr sup) (cons (car sup) done) @-)))
               ;; Case 5: [a1,...], [b1!=a1,...], done = empty
               ;; Step Goal: b1 v (a1..n)
               (@derive
                (A1-An         (@given proof))
                ((v B1 A1-An)  (build.expansion (@formula B1) @-))
                (Bm-B1         (build.ordered-subset-aux sub (cdr sup) (cons (car sup) done) @-))))))
          ((consp sup)
           ;; Case 6: sub = empty, [b1,...], done = [d1,...]  (done is nonempty via our guard)
           ;; Step Goal: [b1,d1,...,dk]
           (@derive
            (D1-Dk            (@given proof))
            ((v B1 D1-Dk)     (build.expansion (@formula B1) @-))
            ((v Bm-B1 D1-Dk)  (build.ordered-subset-aux sub (cdr sup) (cons (car sup) done) @-))))
          (t
           ;; Case 7: sup = empty
           (logic.appeal-identity proof)))))

(encapsulate
 ()
 (local (in-theory (enable build.ordered-subset-aux)))

 (defthm build.ordered-subset-aux-under-iff
   (iff (build.ordered-subset-aux sub sup done proof)
        t))

 (defthm forcing-logic.appealp-of-build.ordered-subset-aux
   (implies (force (and (logic.formula-listp sup)
                        (ordered-subsetp sub sup)
                        (logic.formula-listp done)
                        (or (consp sub) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp sub) (consp done))
                                      (logic.por (logic.disjoin-formulas done)
                                                 (logic.disjoin-formulas sub)))
                                     ((consp sub)
                                      (logic.disjoin-formulas sub))
                                     (t
                                      (logic.disjoin-formulas done))))))
            (equal (logic.appealp (build.ordered-subset-aux sub sup done proof))
                   t)))

 (defthm forcing-logic.conclusion-of-build.ordered-subset-aux
   (implies (force (and (logic.formula-listp sup)
                        (ordered-subsetp sub sup)
                        (logic.formula-listp done)
                        (or (consp sub) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp sub) (consp done))
                                      (logic.por (logic.disjoin-formulas done)
                                                 (logic.disjoin-formulas sub)))
                                     ((consp sub)
                                      (logic.disjoin-formulas sub))
                                     (t
                                      (logic.disjoin-formulas done))))))
            (equal (logic.conclusion (build.ordered-subset-aux sub sup done proof))
                   (logic.disjoin-formulas (app (rev sup) done)))))

 (verify-guards build.ordered-subset-aux)

 (defthm forcing-logic.proofp-of-build.ordered-subset-aux
   (implies (force (and (logic.formula-listp sup)
                        (ordered-subsetp sub sup)
                        (logic.formula-listp done)
                        (or (consp sub) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp sub) (consp done))
                                      (logic.por (logic.disjoin-formulas done)
                                                 (logic.disjoin-formulas sub)))
                                     ((consp sub)
                                      (logic.disjoin-formulas sub))
                                     (t
                                      (logic.disjoin-formulas done))))
                        ;; ---
                        (logic.formula-list-atblp sup atbl)
                        (logic.proofp proof axioms thms atbl)))
            (equal (logic.proofp (build.ordered-subset-aux sub sup done proof) axioms thms atbl)
                   t))))



(defund build.ordered-subset (sub sup proof)
  (declare (xargs :guard (and (logic.formula-listp sup)
                              (logic.appealp proof)
                              (consp sub)
                              (ordered-subsetp sub sup)
                              (equal (logic.conclusion proof) (logic.disjoin-formulas sub)))))
  (build.rev-disjunction (fast-rev sup)
                         (build.ordered-subset-aux sub sup nil proof)))

(encapsulate
 ()
 (local (in-theory (enable build.ordered-subset)))

 (defthm build.ordered-subset-under-iff
   (iff (build.ordered-subset sub sup proof)
        t))

 (defthm forcing-logic.appealp-of-build.ordered-subset
   (implies (force (and (logic.formula-listp sup)
                        (logic.appealp proof)
                        (consp sub)
                        (ordered-subsetp sub sup)
                        (equal (logic.conclusion proof) (logic.disjoin-formulas sub))))
            (equal (logic.appealp (build.ordered-subset sub sup proof))
                   t)))

 (defthm forcing-logic.conclusion-of-build.ordered-subset
   (implies (force (and (logic.formula-listp sup)
                        (logic.appealp proof)
                        (consp sub)
                        (ordered-subsetp sub sup)
                        (equal (logic.conclusion proof) (logic.disjoin-formulas sub))))
            (equal (logic.conclusion (build.ordered-subset sub sup proof))
                   (logic.disjoin-formulas sup))))

 (defthm forcing-logic.proofp-of-build.ordered-subset
   (implies (force (and (logic.formula-listp sup)
                        (logic.appealp proof)
                        (consp sub)
                        (ordered-subsetp sub sup)
                        (equal (logic.conclusion proof) (logic.disjoin-formulas sub))
                        ;; ---
                        (logic.formula-list-atblp sup atbl)
                        (logic.proofp proof axioms thms atbl)))
            (equal (logic.proofp (build.ordered-subset sub sup proof) axioms thms atbl)
                   t))))




;; Test data for the build.ordered-subset was taken from running this let*
;; expression with the appropriate lines commented out.

;; (let* ((sub (list
;;              (logic.pequal 'a1 'a1-prime)
;;              (logic.pequal 'a2 'a2-prime)
;;              (logic.pequal 'a3 'a3-prime)
;;              (logic.pequal 'a4 'a4-prime)
;;              (logic.pequal 'a5 'a5-prime)
;;              (logic.pequal 'a6 'a6-prime)
;;              (logic.pequal 'a7 'a7-prime)
;;              (logic.pequal 'a8 'a8-prime)
;;              (logic.pequal 'a9 'a9-prime)
;;              (logic.pequal 'a10 'a10-prime)
;;              (logic.pequal 'a11 'a11-prime)
;;              (logic.pequal 'a12 'a12-prime)
;;              (logic.pequal 'a13 'a13-prime)
;;              (logic.pequal 'a14 'a14-prime)
;;              (logic.pequal 'a15 'a15-prime)
;;              (logic.pequal 'a16 'a16-prime)
;;              (logic.pequal 'a17 'a17-prime)
;;              (logic.pequal 'a18 'a18-prime)
;;              (logic.pequal 'a19 'a19-prime)
;;              (logic.pequal 'a20 'a20-prime)
;;              ))
;;        (sup (list
;;              (logic.pequal 'c1 'c1-prime)
;;              (logic.pequal 'a1 'a1-prime)
;;              (logic.pequal 'b1 'b1-prime)
;;              (logic.pequal 'c2 'c2-prime)
;;              (logic.pequal 'a2 'a2-prime)
;;              (logic.pequal 'b2 'b2-prime)
;;              (logic.pequal 'c3 'c3-prime)
;;              (logic.pequal 'a3 'a3-prime)
;;              (logic.pequal 'b3 'b3-prime)
;;              (logic.pequal 'c4 'c4-prime)
;;              (logic.pequal 'a4 'a4-prime)
;;              (logic.pequal 'b4 'b4-prime)
;;              (logic.pequal 'c5 'c5-prime)
;;              (logic.pequal 'a5 'a5-prime)
;;              (logic.pequal 'b5 'b5-prime)
;;              (logic.pequal 'c6 'c6-prime)
;;              (logic.pequal 'a6 'a6-prime)
;;              (logic.pequal 'b6 'b6-prime)
;;              (logic.pequal 'c7 'c7-prime)
;;              (logic.pequal 'a7 'a7-prime)
;;              (logic.pequal 'b7 'b7-prime)
;;              (logic.pequal 'c8 'c8-prime)
;;              (logic.pequal 'a8 'a8-prime)
;;              (logic.pequal 'b8 'b8-prime)
;;              (logic.pequal 'c9 'c9-prime)
;;              (logic.pequal 'a9 'a9-prime)
;;              (logic.pequal 'b9 'b9-prime)
;;              (logic.pequal 'c10 'c10-prime)
;;              (logic.pequal 'a10 'a10-prime)
;;              (logic.pequal 'b10 'b10-prime)
;;              (logic.pequal 'c11 'c11-prime)
;;              (logic.pequal 'a11 'a11-prime)
;;              (logic.pequal 'b11 'b11-prime)
;;              (logic.pequal 'c12 'c12-prime)
;;              (logic.pequal 'a12 'a12-prime)
;;              (logic.pequal 'b12 'b12-prime)
;;              (logic.pequal 'c13 'c13-prime)
;;              (logic.pequal 'a13 'a13-prime)
;;              (logic.pequal 'b13 'b13-prime)
;;              (logic.pequal 'c14 'c14-prime)
;;              (logic.pequal 'a14 'a14-prime)
;;              (logic.pequal 'b14 'b14-prime)
;;              (logic.pequal 'c15 'c15-prime)
;;              (logic.pequal 'a15 'a15-prime)
;;              (logic.pequal 'b15 'b15-prime)
;;              (logic.pequal 'c16 'c16-prime)
;;              (logic.pequal 'a16 'a16-prime)
;;              (logic.pequal 'b16 'b16-prime)
;;              (logic.pequal 'c17 'c17-prime)
;;              (logic.pequal 'a17 'a17-prime)
;;              (logic.pequal 'b17 'b17-prime)
;;              (logic.pequal 'c18 'c18-prime)
;;              (logic.pequal 'a18 'a18-prime)
;;              (logic.pequal 'b18 'b18-prime)
;;              (logic.pequal 'c19 'c19-prime)
;;              (logic.pequal 'a19 'a19-prime)
;;              (logic.pequal 'b19 'b19-prime)
;;              (logic.pequal 'c20 'c20-prime)
;;              (logic.pequal 'a20 'a20-prime)
;;              (logic.pequal 'b20 'b20-prime)
;;              ))
;;        (proof (build.axiom (logic.disjoin-formulas sub)))
;;        (oproof (build.ordered-subset sub sup proof))
;;        (sproof (build.generic-subset sub sup proof)))
;;   (list
;;    (list 'ok (equal (logic.conclusion oproof) (logic.conclusion sproof)))
;;    (list 'rank-o (rank oproof))
;;    (list 'rank-s (rank sproof))))




;; Finally we introduce our "adaptive" builder.  We check for certain common
;; cases.

(defund build.disjoined-subset (as bs proof)
  (declare (xargs :guard (and (logic.formula-listp bs)
                              (subsetp as bs)
                              (logic.appealp proof)
                              (consp as)
                              (equal (logic.conclusion proof)
                                     (logic.disjoin-formulas as)))
                  :export (build.generic-subset as bs proof)))
  (cond ((equal bs as)
         ;; The best case: we can just reuse the proof verbatim.
         (logic.appeal-identity proof))
        ((equal bs (fast-rev as))
         ;; Another good case, we can use our reversal builder.
         (build.rev-disjunction as proof))
        ((ordered-subsetp as bs)
         ;; Here we may be able to optimize.  As a heuristic, if there are more
         ;; than 5 members in the subset or more than 10 in the superset, we
         ;; just use the ordered builder since the generic builder is probably
         ;; not as efficient.  Otherwise, we'll try both builders and just use
         ;; whichever proof turns out to be smaller.
         (if (or (< 5 (len as))
                 (< 10 (len bs)))
             (build.ordered-subset as bs proof)
           (let* ((proof1 (build.generic-subset as bs proof))
                  (proof2 (build.ordered-subset as bs proof))
                  (rank1  (rank proof1))
                  (rank2  (rank proof2)))
             (ACL2::prog2$
              (ACL2::cw "BDJS n,m,generic,ord = ~x0, ~x1, ~x2, ~x3~%"
                  (len as) (len bs) rank1 rank2)
              (if (< (rank proof1) (rank proof2))
                  proof1
                proof2)))))
        (t
         ;; If we get here, we have no special tricks to use.  We fall back to
         ;; using the generic subset builder.
         (build.generic-subset as bs proof))))

(encapsulate
 ()
 (local (in-theory (enable build.disjoined-subset)))

 (defthm build.disjoined-subset-under-iff
   (iff (build.disjoined-subset as bs proof)
        t))

 (defthm forcing-logic.appealp-of-build.disjoined-subset
   (implies (force (and (logic.formula-listp bs)
                        (subsetp as bs)
                        (logic.appealp proof)
                        (consp as)
                        (equal (logic.conclusion proof)
                               (logic.disjoin-formulas as))))
            (equal (logic.appealp (build.disjoined-subset as bs proof))
                   t)))

 (defthm forcing-logic.conclusion-of-build.disjoined-subset
   (implies (force (and (logic.formula-listp bs)
                        (subsetp as bs)
                        (logic.appealp proof)
                        (consp as)
                        (equal (logic.conclusion proof)
                               (logic.disjoin-formulas as))))
            (equal (logic.conclusion (build.disjoined-subset as bs proof))
                   (logic.disjoin-formulas bs)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm forcing-logic.proofp-of-build.disjoined-subset
   (implies (force (and (logic.formula-listp bs)
                        (subsetp as bs)
                        (logic.appealp proof)
                        (consp as)
                        (equal (logic.conclusion proof)
                               (logic.disjoin-formulas as))
                        ;; ---
                        (logic.formula-list-atblp bs atbl)
                        (logic.proofp proof axioms thms atbl)))
            (equal (logic.proofp (build.disjoined-subset as bs proof) axioms thms atbl)
                   t))))




;; We can now also talk about building a lists of proofs X1,...,Xn from another
;; list of proofs Y1,...,Ym, where "each Xi is a superset of some Yi".

(defund build.all-superset-of-some (x y proofs)
  (declare (xargs :guard (and (logic.formula-list-listp x)
                              (logic.formula-list-listp y)
                              (cons-listp y)
                              (all-superset-of-somep x y)
                              (logic.appeal-listp proofs)
                              (subsetp (logic.disjoin-each-formula-list y)
                                       (logic.strip-conclusions proofs)))))
  (if (consp x)
      (let* ((subset (find-subset (car x) y))
             (proof  (logic.find-proof (logic.disjoin-formulas subset) proofs)))
        ;; Proof is now a proof of subset, which is a subset of (car x).
        ;; We can just expand the proof to get a proof of (car x).
        (cons (build.disjoined-subset subset (car x) proof)
              (build.all-superset-of-some (cdr x) y proofs)))
    nil))

(encapsulate
 ()
 (local (in-theory (enable build.all-superset-of-some)))

 (defthm forcing-logic.appeal-listp-of-build.all-superset-of-some
   (implies (force (and (logic.formula-list-listp x)
                        (logic.formula-list-listp y)
                        (cons-listp y)
                        (all-superset-of-somep x y)
                        (logic.appeal-listp proofs)
                        (subsetp (logic.disjoin-each-formula-list y)
                                 (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (build.all-superset-of-some x y proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-build.all-superset-of-some
   (implies (force (and (logic.formula-list-listp x)
                        (logic.formula-list-listp y)
                        (cons-listp y)
                        (all-superset-of-somep x y)
                        (logic.appeal-listp proofs)
                        (subsetp (logic.disjoin-each-formula-list y)
                                 (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (build.all-superset-of-some x y proofs))
                   (logic.disjoin-each-formula-list x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm forcing-logic.proof-listp-of-build.all-superset-of-some
   (implies (force (and (logic.formula-list-listp x)
                        (logic.formula-list-listp y)
                        (cons-listp y)
                        (all-superset-of-somep x y)
                        (logic.appeal-listp proofs)
                        (subsetp (logic.disjoin-each-formula-list y)
                                 (logic.strip-conclusions proofs))
                        ;; ---
                        (logic.formula-list-list-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)))
            (equal (logic.proof-listp (build.all-superset-of-some x y proofs) axioms thms atbl)
                   t))))



(defund build.generic-subset-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'build.generic-subset)
         (equal (len subproofs) 1)
         (tuplep 2 extras)
         (let ((as (first extras))
               (bs (second extras)))
           (and (logic.formula-listp bs)
                (logic.formula-list-atblp bs atbl)
                (subsetp as bs)
                (consp as)
                (equal conclusion (logic.disjoin-formulas bs))
                (equal (logic.conclusion (first subproofs))
                       (logic.disjoin-formulas as)))))))


(encapsulate
 ()
 (local (in-theory (enable build.generic-subset-okp)))

 (defthm booleanp-of-build.generic-subset-okp
   (equal (booleanp (build.generic-subset-okp x atbl))
          t)
   :hints(("goal" :in-theory (disable forcing-true-listp-of-logic.subproofs))))

 (defthm build.generic-subset-okp-of-logic.appeal-identity
   (equal (build.generic-subset-okp (logic.appeal-identity x) atbl)
          (build.generic-subset-okp x atbl))
   :hints(("goal" :in-theory (disable forcing-true-listp-of-logic.subproofs))))

 (defthm forcing-soundness-of-build.generic-subset-okp
   (implies (and (build.generic-subset-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (build.generic-subset
                                 (first (logic.extras x))
                                 (second (logic.extras x))
                                 (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                                         axioms thms atbl)))))))))



(dd.close)