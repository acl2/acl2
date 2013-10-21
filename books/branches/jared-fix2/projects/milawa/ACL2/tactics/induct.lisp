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
(include-book "colors")
(include-book "skeletonp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)




(defund build.stepwise-modus-ponens-2 (x y)
  ;; X are proofs of [~A1, ..., ~An]
  ;; Y are proofs of [A1 v B1, ..., An v Bn]
  ;; -----------------------------------------
  ;; Prove [B1, ..., Bn]
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.appeal-listp y)
                              (logic.all-negationsp (logic.strip-conclusions x))
                              (logic.all-disjunctionsp (logic.strip-conclusions y))
                              (equal (logic.vlhses (logic.strip-conclusions y))
                                     (logic.~args (logic.strip-conclusions x)))
                              (equal (len x) (len y)))))
  (if (and (consp x)
           (consp y))
      (cons (build.modus-ponens-2 (car x) (car y))
            (build.stepwise-modus-ponens-2 (cdr x) (cdr y)))
    nil))

(encapsulate
 ()
 (local (in-theory (enable build.stepwise-modus-ponens-2)))

 (defthm true-listp-of-build.stepwise-modus-ponens-2
   (equal (true-listp (build.stepwise-modus-ponens-2 x y))
          t))

 (defthm forcing-logic.appeal-list-of-build.stepwise-modus-ponens-2
   (implies (force (and (logic.appeal-listp x)
                        (logic.appeal-listp y)
                        (logic.all-negationsp (logic.strip-conclusions x))
                        (logic.all-disjunctionsp (logic.strip-conclusions y))
                        (equal (logic.vlhses (logic.strip-conclusions y))
                               (logic.~args (logic.strip-conclusions x)))
                        (equal (len x) (len y))))
            (equal (logic.appeal-listp (build.stepwise-modus-ponens-2 x y))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-build.stepwise-modus-ponens-2
   (implies (force (and (logic.appeal-listp x)
                        (logic.appeal-listp y)
                        (logic.all-negationsp (logic.strip-conclusions x))
                        (logic.all-disjunctionsp (logic.strip-conclusions y))
                        (equal (logic.vlhses (logic.strip-conclusions y))
                               (logic.~args (logic.strip-conclusions x)))
                        (equal (len x) (len y))))
            (equal (logic.strip-conclusions (build.stepwise-modus-ponens-2 x y))
                   (logic.vrhses (logic.strip-conclusions y))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm forcing-logic.proof-list-of-build.stepwise-modus-ponens-2
   (implies (force (and (logic.appeal-listp x)
                        (logic.appeal-listp y)
                        (logic.all-negationsp (logic.strip-conclusions x))
                        (logic.all-disjunctionsp (logic.strip-conclusions y))
                        (equal (logic.vlhses (logic.strip-conclusions y))
                               (logic.~args (logic.strip-conclusions x)))
                        (equal (len x) (len y))
                        ;; ---
                        (logic.proof-listp x axioms thms atbl)
                        (logic.proof-listp y axioms thms atbl)))
            (equal (logic.proof-listp (build.stepwise-modus-ponens-2 x y) axioms thms atbl)
                   t))))




(defund tactic.induct-basis-clause (clause qs)
  (declare (xargs :guard (and (logic.term-listp clause)
                              (consp clause)
                              (logic.term-listp qs))))
  (let* ((clause-as-formula (clause.clause-formula clause))
         (qs-as-formulas    (logic.term-list-formulas qs))
         (basis-as-formula  (logic.make-basis-step clause-as-formula qs-as-formulas))
         (basis-as-term     (logic.compile-formula basis-as-formula))
         (basis-as-clause   (list basis-as-term)))
    basis-as-clause))

(defthm forcing-logic.term-listp-of-tactic.induct-basis-clause
  (implies (force (and (logic.term-listp clause)
                       (consp clause)
                       (logic.term-listp qs)))
           (equal (logic.term-listp (tactic.induct-basis-clause clause qs))
                  t))
  :hints(("Goal" :in-theory (enable tactic.induct-basis-clause))))

(defthm consp-of-tactic.induct-basis-clause
  (equal (consp (tactic.induct-basis-clause clause qs))
         t)
  :hints(("Goal" :in-theory (enable tactic.induct-basis-clause))))



(defund@ tactic.compile-induct-basis-clause (clause qs proof)
  ;; Prove basis-as-formula from a proof of basis-as-clause.
  (declare (xargs :guard (and (logic.term-listp clause)
                              (consp clause)
                              (logic.term-listp qs)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (clause.clause-formula (tactic.induct-basis-clause clause qs))))
                  :verify-guards nil))
  ;; Proof is (clause.clause-formula basis-as-clause)
  ;;            <-> (logic.term-formula basis-as-term)
  ;;            <-> (logic.term-formula (logic.compile-formula basis-as-formula))
  ;;            <-> (logic.compile-formula basis-as-formula) != nil
  ;;            <-> basis-as-term != nil
  (let* ((clause-as-formula (clause.clause-formula clause))
         (qs-as-formulas    (logic.term-list-formulas qs))
         (basis-as-formula  (logic.make-basis-step clause-as-formula qs-as-formulas)))
    ;; Let BAF be basis-as-formula
    ;; Let BAT be basis-as-term
    (@derive ((v BAF (= BAT nil))  (@given (second (build.compile-formula basis-as-formula))))
             ((v (= BAT nil) BAF)  (build.commute-or @-))
             ((!= BAT nil)         (@given proof))
             (BAF                  (build.modus-ponens-2 @- @--)))))

(defobligations tactic.compile-induct-basis-clause
  (build.compile-formula
   build.commute-or
   build.modus-ponens2))

(encapsulate
 ()
 (local (in-theory (enable logic.term-formula
                           tactic.induct-basis-clause
                           tactic.compile-induct-basis-clause)))

 (verify-guards tactic.compile-induct-basis-clause)

 (defthm forcing-logic.appealp-of-tactic.compile-induct-basis-clause
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.term-listp qs)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (tactic.induct-basis-clause clause qs)))))
            (equal (logic.appealp (tactic.compile-induct-basis-clause clause qs proof))
                   t)))

 (defthm forcing-logic.conclusion-of-tactic.compile-induct-basis-clause
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.term-listp qs)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (tactic.induct-basis-clause clause qs)))))
            (equal (logic.conclusion (tactic.compile-induct-basis-clause clause qs proof))
                   (logic.make-basis-step (clause.clause-formula clause)
                                          (logic.term-list-formulas qs))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-tactic.compile-induct-basis-clause
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.term-listp qs)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (tactic.induct-basis-clause clause qs)))
                        ;; ---
                        (logic.term-list-atblp clause atbl)
                        (logic.term-list-atblp qs atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (logic.proofp proof axioms thms atbl)
                        (@obligations tactic.compile-induct-basis-clause)))
            (equal (logic.proofp (tactic.compile-induct-basis-clause clause qs proof) axioms thms atbl)
                   t))))





(defund tactic.induct-inductive-clauses (clause qs all-sigmas)
  (declare (xargs :guard (and (logic.term-listp clause)
                              (consp clause)
                              (logic.term-listp qs)
                              (logic.sigma-list-listp all-sigmas)
                              (equal (len qs) (len all-sigmas)))))
  (let* ((clause-as-formula     (clause.clause-formula clause))
         (qs-as-formulas        (logic.term-list-formulas qs))
         (inductive-as-formulas (logic.make-induction-steps clause-as-formula qs-as-formulas all-sigmas))
         (inductive-as-terms    (logic.compile-formula-list inductive-as-formulas))
         (inductive-as-clauses  (listify-each inductive-as-terms)))
    inductive-as-clauses))

(defthm forcing-logic.term-list-listp-of-tactic.induct-inductive-clauses
  (implies (force (and (logic.term-listp clause)
                              (consp clause)
                              (logic.term-listp qs)
                              (logic.sigma-list-listp all-sigmas)
                              (equal (len qs) (len all-sigmas))))
           (equal (logic.term-list-listp (tactic.induct-inductive-clauses clause qs all-sigmas))
                  t))
  :hints(("Goal" :in-theory (enable tactic.induct-inductive-clauses))))

(defthm cons-listp-of-tactic.induct-inductive-clauses
  (equal (cons-listp (tactic.induct-inductive-clauses clause qs all-sigmas))
         t)
  :hints(("Goal" :in-theory (enable tactic.induct-inductive-clauses))))

(defthm true-listp-of-tactic.induct-inductive-clauses
  (equal (true-listp (tactic.induct-inductive-clauses clause qs all-sigmas))
         t)
  :hints(("Goal" :in-theory (enable tactic.induct-inductive-clauses))))




(defund tactic.compile-induct-inductive-clauses (clause qs all-sigmas proofs)
  (declare (xargs :guard (and (logic.term-listp clause)
                              (consp clause)
                              (logic.term-listp qs)
                              (logic.sigma-list-listp all-sigmas)
                              (equal (len qs) (len all-sigmas))
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (clause.clause-list-formulas (tactic.induct-inductive-clauses clause qs all-sigmas))))
                  :verify-guards nil))
  ;; Let G1-f, ..., Gn-f be inductive-as-formulas
  ;; Let G1-t, ..., Gn-t be inductive-as-terms
  ;; Let G1-c, ..., Gn-c be inductive-as-clauses
  ;;
  ;; We are given proofs of (clause.clause-list-formulas [G1-c, ..., Gn-c])
  ;;                         <-> (logic.term-list-formulas [G1-t, ..., Gn-t])
  ;;                         <-> [G1-t != nil, ..., Gn-t != nil]
  ;;
  (let* ((clause-as-formula     (clause.clause-formula clause))
         (qs-as-formulas        (logic.term-list-formulas qs))
         (inductive-as-formulas (logic.make-induction-steps clause-as-formula qs-as-formulas all-sigmas))
         ;; compile-lemmas: [G1-t = nil v G1-f, ..., Gn-t = nil v Gn-f]
         (compile-lemmas        (build.compile-formula-list-comm-2 inductive-as-formulas)))
    ;; Our goal, then, is just a stepwise-modus-ponens-2 away.
    (build.stepwise-modus-ponens-2 proofs compile-lemmas)))

(defobligations tactic.compile-induct-inductive-clauses
  (build.compile-formula-list-comm-2
   build.stepwise-modus-ponens-2))

(encapsulate
 ()
 (local (in-theory (enable tactic.induct-inductive-clauses
                           tactic.compile-induct-inductive-clauses)))

 (local (defthm lemma
          (implies (equal (logic.strip-conclusions proofs)
                          (logic.negate-formulas x))
                   (equal (len proofs)
                          (len x)))
          :hints(("Goal"
                  :in-theory (disable len-of-logic.negate-formulas
                                      len-of-logic.strip-conclusions)
                  :use ((:instance len-of-logic.negate-formulas)
                        (:instance len-of-logic.strip-conclusions (x proofs)))))))

 (verify-guards tactic.compile-induct-inductive-clauses)

 (defthm forcing-logic.appeal-listp-of-tactic.compile-induct-inductive-clauses
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.term-listp qs)
                        (logic.sigma-list-listp all-sigmas)
                        (equal (len qs) (len all-sigmas))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (tactic.induct-inductive-clauses clause qs all-sigmas)))))
            (equal (logic.appeal-listp (tactic.compile-induct-inductive-clauses clause qs all-sigmas proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.compile-induct-inductive-clauses
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.term-listp qs)
                        (logic.sigma-list-listp all-sigmas)
                        (equal (len qs) (len all-sigmas))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (tactic.induct-inductive-clauses clause qs all-sigmas)))))
            (equal (logic.strip-conclusions (tactic.compile-induct-inductive-clauses clause qs all-sigmas proofs))
                   (logic.make-induction-steps (clause.clause-formula clause)
                                               (logic.term-list-formulas qs)
                                               all-sigmas)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-tactic.compile-induct-inductive-clauses
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.term-listp qs)
                        (logic.sigma-list-listp all-sigmas)
                        (equal (len qs) (len all-sigmas))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (tactic.induct-inductive-clauses clause qs all-sigmas)))
                        ;; ---
                        (logic.term-list-atblp clause atbl)
                        (logic.term-list-atblp qs atbl)
                        (logic.sigma-list-list-atblp all-sigmas atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations tactic.compile-induct-inductive-clauses)
                        ))
            (equal (logic.proof-listp (tactic.compile-induct-inductive-clauses clause qs all-sigmas proofs) axioms thms atbl)
                   t))))




(defund tactic.induct-ordinal-clause (m)
  (declare (xargs :guard (logic.termp m)))
  (let* ((ordinal-as-formula (logic.make-ordinal-step m))
         (ordinal-as-term    (logic.compile-formula ordinal-as-formula))
         (ordinal-as-clause  (list ordinal-as-term)))
    ordinal-as-clause))

(defthm forcing-logic.term-listp-of-tactic.induct-ordinal-clause
  (implies (force (logic.termp m))
           (equal (logic.term-listp (tactic.induct-ordinal-clause m))
                  t))
  :hints(("Goal" :in-theory (enable tactic.induct-ordinal-clause))))

(defthm consp-of-tactic.induct-ordinal-clause
  (equal (consp (tactic.induct-ordinal-clause m))
         t)
  :hints(("Goal" :in-theory (enable tactic.induct-ordinal-clause))))

(defund@ tactic.compile-induct-ordinal-clause (m proof)
  (declare (xargs :guard (and (logic.termp m)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (clause.clause-formula (tactic.induct-ordinal-clause m))))
                  :verify-guards nil))
  ;; Let OAF be ordinal-as-formula
  ;; Let OAT be ordinal-as-term
  (let ((ordinal-as-formula (logic.make-ordinal-step m)))
    (@derive
     ((v OAF (= OAT nil))   (@given (second (build.compile-formula ordinal-as-formula))))
     ((v (= OAT nil) OAF)   (build.commute-or @-))
     ((!= OAT nil)          (@given proof))
     (OAF                   (build.modus-ponens-2 @- @--)))))

(defobligations tactic.compile-induct-ordinal-clause
  (build.compile-formula
   build.commute-or
   build.modus-ponens-2))

(encapsulate
 ()
 (local (in-theory (enable logic.term-formula
                           tactic.induct-ordinal-clause
                           tactic.compile-induct-ordinal-clause)))

 (verify-guards tactic.compile-induct-ordinal-clause)

 (defthm forcing-logic.appealp-of-tactic.compile-induct-ordinal-clause
   (implies (force (and (logic.termp m)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (tactic.induct-ordinal-clause m)))))
            (equal (logic.appealp (tactic.compile-induct-ordinal-clause m proof))
                   t)))

 (defthm forcing-logic.conclusion-of-tactic.compile-induct-ordinal-clause
   (implies (force (and (logic.termp m)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (tactic.induct-ordinal-clause m)))))
            (equal (logic.conclusion (tactic.compile-induct-ordinal-clause m proof))
                   (logic.make-ordinal-step m))))

 (defthm@ forcing-logic.proofp-of-tactic.compile-induct-ordinal-clause
   (implies (force (and (logic.termp m)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (tactic.induct-ordinal-clause m)))
                        ;; ---
                        (logic.term-atblp m atbl)
                        (logic.proofp proof axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'ordp atbl)) 1)
                        (@obligations tactic.compile-induct-ordinal-clause)
                        ))
            (equal (logic.proofp (tactic.compile-induct-ordinal-clause m proof) axioms thms atbl)
                   t))))




(defund tactic.induct-measure-clauses (m qs all-sigmas)
  (declare (xargs :guard (and (logic.termp m)
                              (logic.term-listp qs)
                              (logic.sigma-list-listp all-sigmas)
                              (equal (len qs) (len all-sigmas)))))
  (let* ((qs-as-formulas      (logic.term-list-formulas qs))
         (measure-as-formulas (logic.make-all-measure-steps m qs-as-formulas all-sigmas))
         (measure-as-terms    (logic.compile-formula-list measure-as-formulas))
         (measure-as-clauses  (listify-each measure-as-terms)))
    measure-as-clauses))

(defthm forcing-logic.term-list-listp-of-tactic.induct-measure-clauses
  (implies (force (and (logic.termp m)
                       (logic.term-listp qs)
                       (logic.sigma-list-listp all-sigmas)
                       (equal (len qs) (len all-sigmas))))
           (equal (logic.term-list-listp (tactic.induct-measure-clauses m qs all-sigmas))
                  t))
  :hints(("Goal" :in-theory (e/d (tactic.induct-measure-clauses)
                                 (FORCING-LOGIC.TERM-LIST-ATBLP-OF-LOGIC.COMPILE-FORMULA-LIST)))))

(defthm cons-listp-of-tactic.induct-measure-clauses
  (equal (cons-listp (tactic.induct-measure-clauses m qs all-sigmas))
         t)
  :hints(("Goal" :in-theory (enable tactic.induct-measure-clauses))))

(defthm true-listp-of-tactic.induct-measure-clauses
  (equal (true-listp (tactic.induct-measure-clauses m qs all-sigmas))
         t)
  :hints(("Goal" :in-theory (enable tactic.induct-measure-clauses))))


(defund tactic.compile-induct-measure-clauses (m qs all-sigmas proofs)
  (declare (xargs :guard (and (logic.termp m)
                              (logic.term-listp qs)
                              (logic.sigma-list-listp all-sigmas)
                              (equal (len qs) (len all-sigmas))
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (clause.clause-list-formulas (tactic.induct-measure-clauses m qs all-sigmas))))
                  :verify-guards nil))
  ;; Goal is to prove measure-as-formulas.
  ;;
  ;; Let [G1-f, ..., Gn-f] be measure-as-formulas
  ;; Let [G1-t, ..., Gn-t] be measure-as-terms
  ;; Let [G1-c, ..., Gn-c] be measure-as-clauses
  ;;
  ;; Proofs are (clause.clause-list-formulas [G1-c, ..., Gn-c])
  ;;              <-> (logic.term-list-formulas [G1-t, ..., Gn-t])
  ;;              <-> [G1-t != nil, ..., Gn-t != nil]
  ;;
  (let* ((qs-as-formulas        (logic.term-list-formulas qs))
         (measure-as-formulas   (logic.make-all-measure-steps m qs-as-formulas all-sigmas))
         ;; compile-lemmas: [G1-t = nil v G1-f, ..., Gn-t = nil v Gn-f]
         (compile-lemmas        (build.compile-formula-list-comm-2 measure-as-formulas)))
    ;; Our goal, then, is just a stepwise-modus-ponens-2 away.
    (build.stepwise-modus-ponens-2 proofs compile-lemmas)))

(defobligations tactic.compile-induct-measure-clauses
  (build.compile-formula-list-comm-2
   build.stepwise-modus-ponens-2))

(encapsulate
 ()
 (local (in-theory (enable tactic.induct-measure-clauses tactic.compile-induct-measure-clauses)))

 (local (defthm lemma
          (implies (equal (logic.strip-conclusions proofs)
                          (logic.negate-formulas x))
                   (equal (len proofs)
                          (len x)))
          :hints(("Goal"
                  :in-theory (disable len-of-logic.negate-formulas
                                      len-of-logic.strip-conclusions)
                  :use ((:instance len-of-logic.negate-formulas)
                        (:instance len-of-logic.strip-conclusions (x proofs)))))))

 (verify-guards tactic.compile-induct-measure-clauses)

 (defthm true-listp-of-tactic.compile-induct-measure-clauses
   (equal (true-listp (tactic.compile-induct-measure-clauses m qs all-sigmas measure-proofs))
          t))


 (defthm forcing-logic.appeal-list-of-tactic.compile-induct-measure-clauses
   (implies (force (and (logic.termp m)
                        (logic.term-listp qs)
                        (logic.sigma-list-listp all-sigmas)
                        (equal (len qs) (len all-sigmas))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (tactic.induct-measure-clauses m qs all-sigmas)))))
            (equal (logic.appeal-listp (tactic.compile-induct-measure-clauses m qs all-sigmas proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.compile-induct-measure-clauses
   (implies (force (and (logic.termp m)
                        (logic.term-listp qs)
                        (logic.sigma-list-listp all-sigmas)
                        (equal (len qs) (len all-sigmas))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (tactic.induct-measure-clauses m qs all-sigmas)))))
            (equal (logic.strip-conclusions (tactic.compile-induct-measure-clauses m qs all-sigmas proofs))
                   (logic.make-all-measure-steps m (logic.term-list-formulas qs) all-sigmas)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-tactic.compile-induct-measure-clauses
   (implies (force (and (logic.termp m)
                        (logic.term-listp qs)
                        (logic.sigma-list-listp all-sigmas)
                        (equal (len qs) (len all-sigmas))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (tactic.induct-measure-clauses m qs all-sigmas)))
                        ;; ---
                        (logic.term-atblp m atbl)
                        (logic.term-list-atblp qs atbl)
                        (logic.sigma-list-list-atblp all-sigmas atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'ord< atbl)) 2)
                        (@obligations tactic.compile-induct-measure-clauses)
                        ))
            (equal (logic.proof-listp (tactic.compile-induct-measure-clauses m qs all-sigmas proofs) axioms thms atbl)
                   t))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))



(defund tactic.induct-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'induct)
         (tuplep 3 extras)
         (let ((m          (first extras))
               (qs         (second extras))
               (all-sigmas (third extras))
               (old-goals  (tactic.skeleton->goals history)))
           (and (logic.termp m)
                ;; We use terms instead of formulas for our qs.
                (logic.term-listp qs)
                (logic.sigma-list-listp all-sigmas)
                (equal (len qs) (len all-sigmas))
                (consp old-goals)
                (let ((clause1 (car old-goals)))
                  (and (consp clause1)
                       (let ((basis     (tactic.induct-basis-clause clause1 qs))
                             (ordinal   (tactic.induct-ordinal-clause m))
                             (inductive (tactic.induct-inductive-clauses clause1 qs all-sigmas))
                             (measure   (tactic.induct-measure-clauses m qs all-sigmas)))
                         (equal goals
                                (cons basis (cons ordinal (fast-app inductive (fast-app measure (cdr old-goals))))))))))))))

(defthm booleanp-of-tactic.induct-okp
  (equal (booleanp (tactic.induct-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.induct-okp)
                                 ((:executable-counterpart acl2::force))))))

(defund tactic.induct-env-okp (x atbl)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.induct-okp x)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable tactic.induct-okp)))))
  (let* ((extras     (tactic.skeleton->extras x))
         (m          (first extras))
         (qs         (second extras))
         (all-sigmas (third extras)))
    (and (logic.term-atblp m atbl)
         (logic.term-list-atblp qs atbl)
         (logic.sigma-list-list-atblp all-sigmas atbl))))

(defthm booleanp-of-tactic.induct-env-okp
  (equal (booleanp (tactic.induct-env-okp x atbl))
         t)
  :hints(("Goal" :in-theory (enable tactic.induct-env-okp))))




(defund tactic.induct-tac (x m qs all-sigmas)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (logic.termp m)
                              (logic.term-listp qs)
                              (logic.sigma-list-listp all-sigmas)
                              (equal (len qs) (len all-sigmas)))))
  (let ((goals (tactic.skeleton->goals x)))
    (cond ((not (consp goals))
           (ACL2::cw "~s0induct-tac failure~s1: all clauses have already been proven.~%" *red* *black*))
          (t
           (let* ((clause1   (car goals))
                  (basis     (tactic.induct-basis-clause clause1 qs))
                  (ordinal   (tactic.induct-ordinal-clause m))
                  (inductive (tactic.induct-inductive-clauses clause1 qs all-sigmas))
                  (measure   (tactic.induct-measure-clauses m qs all-sigmas)))
             (tactic.extend-skeleton (cons basis (cons ordinal (fast-app inductive (fast-app measure (cdr goals)))))
                                     'induct
                                     (list m qs all-sigmas)
                                     x))))))

(defthm forcing-tactic.skeletonp-of-tactic.induct-tac
  (implies (and (tactic.induct-tac x m qs all-sigmas)
                (force (and (tactic.skeletonp x)
                            (logic.termp m)
                            (logic.term-listp qs)
                            (logic.sigma-list-listp all-sigmas)
                            (equal (len qs) (len all-sigmas)))))
           (equal (tactic.skeletonp (tactic.induct-tac x m qs all-sigmas))
                  t))
  :hints(("Goal" :in-theory (enable tactic.induct-tac))))

(defthm forcing-tactic.induct-okp-of-tactic.induct-tac
  (implies (and (tactic.induct-tac x m qs all-sigmas)
                (force (and (tactic.skeletonp x)
                            (logic.termp m)
                            (logic.term-listp qs)
                            (logic.sigma-list-listp all-sigmas)
                            (equal (len qs) (len all-sigmas)))))
           (equal (tactic.induct-okp (tactic.induct-tac x m qs all-sigmas))
                  t))
  :hints(("Goal" :in-theory (enable tactic.induct-tac tactic.induct-okp))))






(defund tactic.induct-compile-aux (clause m qs all-sigmas basis-proof ordinal-proof inductive-proofs measure-proofs)
  (declare (xargs :guard (and (logic.term-listp clause)
                              (consp clause)
                              (logic.termp m)
                              (logic.term-listp qs)
                              (logic.sigma-list-listp all-sigmas)
                              (equal (len qs) (len all-sigmas))
                              (logic.appealp basis-proof)
                              (logic.appealp ordinal-proof)
                              (logic.appeal-listp inductive-proofs)
                              (logic.appeal-listp measure-proofs)
                              (equal (logic.conclusion basis-proof)
                                     (clause.clause-formula (tactic.induct-basis-clause clause qs)))
                              (equal (logic.conclusion ordinal-proof)
                                     (clause.clause-formula (tactic.induct-ordinal-clause m)))
                              (equal (logic.strip-conclusions inductive-proofs)
                                     (clause.clause-list-formulas (tactic.induct-inductive-clauses clause qs all-sigmas)))
                              (equal (logic.strip-conclusions measure-proofs)
                                     (clause.clause-list-formulas (tactic.induct-measure-clauses m qs all-sigmas))))))
  ;; We are given proofs of all the clauses that we split into.
  ;; We start by compiling all these with our step compilers into formulas suitable for build.induction
  (let ((f-basis-proof      (tactic.compile-induct-basis-clause clause qs basis-proof))
        (f-ordinal-proof    (tactic.compile-induct-ordinal-clause m ordinal-proof))
        (f-inductive-proofs (tactic.compile-induct-inductive-clauses clause qs all-sigmas inductive-proofs))
        (f-measure-proofs   (tactic.compile-induct-measure-clauses m qs all-sigmas measure-proofs))
        (f-clause           (clause.clause-formula clause))
        (f-qs               (logic.term-list-formulas qs)))
    ;; We now use build.induction to prove f-clause.
    (build.induction f-clause m f-qs all-sigmas
                     (cons f-basis-proof
                           (cons f-ordinal-proof
                                 ;; BOZO revappend would be better, not really important though
                                 (fast-app f-inductive-proofs f-measure-proofs))))))

(defobligations tactic.induct-compile-aux
  (tactic.compile-induct-basis-clause
   tactic.compile-induct-ordinal-clause
   tactic.compile-induct-inductive-clauses
   tactic.compile-induct-measure-clauses
   build.induction))

(encapsulate
 ()
 (local (in-theory (enable tactic.induct-compile-aux)))

 (defthm forcing-logic.appealp-of-tactic.induct-compile-aux
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.termp m)
                        (logic.term-listp qs)
                        (logic.sigma-list-listp all-sigmas)
                        (equal (len qs) (len all-sigmas))
                        (logic.appealp basis-proof)
                        (logic.appealp ordinal-proof)
                        (logic.appeal-listp inductive-proofs)
                        (logic.appeal-listp measure-proofs)
                        (equal (logic.conclusion basis-proof)
                               (clause.clause-formula (tactic.induct-basis-clause clause qs)))
                        (equal (logic.conclusion ordinal-proof)
                               (clause.clause-formula (tactic.induct-ordinal-clause m)))
                        (equal (logic.strip-conclusions inductive-proofs)
                               (clause.clause-list-formulas (tactic.induct-inductive-clauses clause qs all-sigmas)))
                        (equal (logic.strip-conclusions measure-proofs)
                               (clause.clause-list-formulas (tactic.induct-measure-clauses m qs all-sigmas)))))
            (equal (logic.appealp (tactic.induct-compile-aux clause m qs all-sigmas basis-proof ordinal-proof inductive-proofs measure-proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-tactic.induct-compile-aux
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.termp m)
                        (logic.term-listp qs)
                        (logic.sigma-list-listp all-sigmas)
                        (equal (len qs) (len all-sigmas))
                        (logic.appealp basis-proof)
                        (logic.appealp ordinal-proof)
                        (logic.appeal-listp inductive-proofs)
                        (logic.appeal-listp measure-proofs)
                        (equal (logic.conclusion basis-proof)
                               (clause.clause-formula (tactic.induct-basis-clause clause qs)))
                        (equal (logic.conclusion ordinal-proof)
                               (clause.clause-formula (tactic.induct-ordinal-clause m)))
                        (equal (logic.strip-conclusions inductive-proofs)
                               (clause.clause-list-formulas (tactic.induct-inductive-clauses clause qs all-sigmas)))
                        (equal (logic.strip-conclusions measure-proofs)
                               (clause.clause-list-formulas (tactic.induct-measure-clauses m qs all-sigmas)))))
            (equal (logic.conclusion (tactic.induct-compile-aux clause m qs all-sigmas basis-proof ordinal-proof inductive-proofs measure-proofs))
                   (clause.clause-formula clause)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-tactic.induct-compile-aux
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.termp m)
                        (logic.term-listp qs)
                        (logic.sigma-list-listp all-sigmas)
                        (equal (len qs) (len all-sigmas))
                        (logic.appealp basis-proof)
                        (logic.appealp ordinal-proof)
                        (logic.appeal-listp inductive-proofs)
                        (logic.appeal-listp measure-proofs)
                        (equal (logic.conclusion basis-proof)
                               (clause.clause-formula (tactic.induct-basis-clause clause qs)))
                        (equal (logic.conclusion ordinal-proof)
                               (clause.clause-formula (tactic.induct-ordinal-clause m)))
                        (equal (logic.strip-conclusions inductive-proofs)
                               (clause.clause-list-formulas (tactic.induct-inductive-clauses clause qs all-sigmas)))
                        (equal (logic.strip-conclusions measure-proofs)
                               (clause.clause-list-formulas (tactic.induct-measure-clauses m qs all-sigmas)))
                        ;; ---
                        (logic.term-list-atblp clause atbl)
                        (logic.term-atblp m atbl)
                        (logic.term-list-atblp qs atbl)
                        (logic.sigma-list-list-atblp all-sigmas atbl)
                        (logic.proofp basis-proof axioms thms atbl)
                        (logic.proofp ordinal-proof axioms thms atbl)
                        (logic.proof-listp inductive-proofs axioms thms atbl)
                        (logic.proof-listp measure-proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'ordp atbl)) 1)
                        (equal (cdr (lookup 'ord< atbl)) 2)
                        (@obligations tactic.induct-compile-aux)))
            (equal (logic.proofp (tactic.induct-compile-aux clause m qs all-sigmas basis-proof ordinal-proof inductive-proofs measure-proofs) axioms thms atbl)
                   t))))




(defund tactic.induct-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.induct-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((history       (tactic.skeleton->history x))
         (old-goals     (tactic.skeleton->goals history))
         (extras        (tactic.skeleton->extras x))
         (m             (first extras))
         (qs            (second extras))
         (all-sigmas    (third extras))
         (clause1       (car old-goals))
         ;; Not very optimal; maybe it doesn't matter since we don't induct often.
         (inductive-len (len (tactic.induct-inductive-clauses clause1 qs all-sigmas)))
         (measure-len   (len (tactic.induct-measure-clauses m qs all-sigmas)))
         ;; Extract the appropriate proofs.
         (basis-proof      (first proofs))
         (ordinal-proof    (second proofs))
         (inductive-proofs (firstn inductive-len (cdr (cdr proofs))))
         (other-proofs     (restn inductive-len (cdr (cdr proofs))))
         (measure-proofs   (firstn measure-len other-proofs))
         (cdr-goals-proofs (restn measure-len other-proofs)))
    (cons (tactic.induct-compile-aux clause1 m qs all-sigmas
                                     basis-proof ordinal-proof inductive-proofs measure-proofs)
          cdr-goals-proofs)))

(defobligations tactic.induct-compile
  (tactic.induct-compile-aux))

(encapsulate
 ()
 (local (in-theory (enable tactic.induct-okp
                           tactic.induct-env-okp
                           tactic.induct-compile)))

 (local (defthm crock
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (logic.strip-conclusions proofs)
                          (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))))))

 (local (defthm crock2
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (logic.strip-conclusions (firstn n proofs))
                          (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (firstn n goals)))))
          :hints(("Goal"
                  :in-theory (disable FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                  :use ((:instance FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                                   (Y n)
                                   (X (LOGIC.TERM-LIST-LIST-FORMULAS goals))))))))

 (local (defthm crock3
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (logic.strip-conclusions (firstn n (cdr (cdr proofs))))
                          (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (firstn n (cdr (cdr goals)))))))
          :hints(("Goal"
                  :in-theory (disable FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                  :use ((:instance FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                                   (Y n)
                                   (X (LOGIC.TERM-LIST-LIST-FORMULAS (cdr (cdr goals))))))))))

 (local (defthm crock4
          (implies (equal (app a b) x)
                   (equal (firstn (len a) x)
                          (list-fix a)))))

 (local (defthm crock5
          (implies (equal (app a b) x)
                   (equal (restn (len a) x)
                          (list-fix b)))))

 (local (defthm crock6
          (implies (equal (app a (app b c)) x)
                   (equal (firstn (len b) (restn (len a) x))
                          (list-fix b)))))

 (local (defthm crock7
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (logic.conclusion (car proofs))
                          (logic.disjoin-formulas (logic.term-list-formulas (car goals)))))))

 (local (defthm crock8
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (logic.conclusion (second proofs))
                          (logic.disjoin-formulas (logic.term-list-formulas (second goals)))))))

 (local (defthm crock9
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (consp proofs)
                          (consp goals)))))

 (local (defthm crock10
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (consp (cdr proofs))
                          (consp (cdr goals))))))

 (local (defthm crock11
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (logic.strip-conclusions (restn n (cdr (cdr proofs))))
                          (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (restn n (cdr (cdr goals)))))))
          :hints(("Goal"
                  :in-theory (disable RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                  :use ((:instance RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                                   (Y n)
                                   (X (LOGIC.TERM-LIST-LIST-FORMULAS (cdr (cdr goals))))))))))

 (local (defthm crock12
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (logic.strip-conclusions (firstn n (restn m proofs)))
                          (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (firstn n (restn m goals))))))
          :hints(("Goal"
                  :in-theory (disable FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                                      RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                  :use ((:instance FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                                   (Y n)
                                   (X (LOGIC.TERM-LIST-LIST-FORMULAS (restn m goals))))
                        (:instance RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                                   (Y m)
                                   (X (LOGIC.TERM-LIST-LIST-FORMULAS goals))))))))

 (local (defthm crock13
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (logic.strip-conclusions (firstn n (restn m (cdr (cdr proofs)))))
                          (LOGIC.DISJOIN-EACH-FORMULA-LIST
                           (LOGIC.TERM-LIST-LIST-FORMULAS (firstn n (restn m (cdr (cdr goals))))))))))

 (local (defthm crock14
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (logic.strip-conclusions (restn n (restn m proofs)))
                          (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (restn n (restn m goals))))))
          :hints(("Goal"
                  :in-theory (disable RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                  :use ((:instance RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                                   (Y n)
                                   (X (LOGIC.TERM-LIST-LIST-FORMULAS (restn m goals))))
                        (:instance RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                                   (Y m)
                                   (X (LOGIC.TERM-LIST-LIST-FORMULAS goals))))))))

 (local (defthm crock15
          (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                          (LOGIC.STRIP-CONCLUSIONS PROOFS))
                   (equal (logic.strip-conclusions (restn n (restn m (cdr (cdr proofs)))))
                          (LOGIC.DISJOIN-EACH-FORMULA-LIST
                           (LOGIC.TERM-LIST-LIST-FORMULAS (restn n (restn m (cdr (cdr goals))))))))))

 (verify-guards tactic.induct-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.induct-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.induct-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.induct-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.induct-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.induct-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.induct-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.induct-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.induct-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.induct-env-okp x atbl)
                        (tactic.skeleton-atblp x atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'ordp atbl)) 1)
                        (equal (cdr (lookup 'ord< atbl)) 2)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.induct-compile)))
            (equal (logic.proof-listp (tactic.induct-compile x proofs) axioms thms atbl)
                   t))))
