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
(include-book "level5")
(include-book "../clauses/aux-split-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund level6.step-okp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method (logic.method x)))
    (cond
     ((equal method 'clause.simple-split-bldr)     (clause.simple-split-bldr-okp x atbl))
     ((equal method 'clause.simple-limsplit-bldr)  (clause.simple-limsplit-bldr-okp x atbl))
     ((equal method 'clause.factor-bldr)           (clause.factor-bldr-okp x atbl))
     (t
      (level5.step-okp x axioms thms atbl)))))

(defobligations level6.step-okp
  (clause.simple-split-bldr
   clause.simple-limsplit-bldr
   clause.factor-bldr
   level5.step-okp))

(encapsulate
 ()
 (local (in-theory (enable level6.step-okp)))

 (defthm@ soundness-of-level6.step-okp
   (implies (and (level6.step-okp x axioms thms atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (mapp atbl)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3)
                             (@obligations level6.step-okp))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t)))

 (defthm level6.step-okp-when-level5.step-okp
   ;; This shows that our new step checker is "complete" in the sense that all
   ;; previously acceptable appeals are still acceptable.
   (implies (level5.step-okp x axioms thms atbl)
            (level6.step-okp x axioms thms atbl))
   :hints(("Goal" :in-theory (enable level5.step-okp level4.step-okp level3.step-okp level2.step-okp logic.appeal-step-okp))))

 (defthm level6.step-okp-when-not-consp
   (implies (not (consp x))
            (equal (level6.step-okp x axioms thms atbl)
                   nil))
   :hints(("Goal" :in-theory (enable logic.method)))))



(encapsulate
 ()
 (defund level6.flag-proofp-aux (flag x axioms thms atbl)
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
       (and (level6.step-okp x axioms thms atbl)
            (level6.flag-proofp-aux 'list (logic.subproofs x) axioms thms atbl))
     (if (consp x)
         (and (level6.flag-proofp-aux 'proof (car x) axioms thms atbl)
              (level6.flag-proofp-aux 'list (cdr x) axioms thms atbl))
       t)))

 (definlined level6.proofp-aux (x axioms thms atbl)
   (declare (xargs :guard (and (logic.appealp x)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level6.flag-proofp-aux 'proof x axioms thms atbl))

 (definlined level6.proof-listp-aux (x axioms thms atbl)
   (declare (xargs :guard (and (logic.appeal-listp x)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level6.flag-proofp-aux 'list x axioms thms atbl))

 (defthmd definition-of-level6.proofp-aux
   (equal (level6.proofp-aux x axioms thms atbl)
          (and (level6.step-okp x axioms thms atbl)
               (level6.proof-listp-aux (logic.subproofs x) axioms thms atbl)))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level6.proofp-aux level6.proof-listp-aux level6.flag-proofp-aux))))

 (defthmd definition-of-level6.proof-listp-aux
   (equal (level6.proof-listp-aux x axioms thms atbl)
          (if (consp x)
              (and (level6.proofp-aux (car x) axioms thms atbl)
                   (level6.proof-listp-aux (cdr x) axioms thms atbl))
            t))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level6.proofp-aux level6.proof-listp-aux level6.flag-proofp-aux))))

 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition level6.proofp-aux))))
 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition demo.proof-list)))))



(defthm level6.proofp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level6.proofp-aux x axioms thms atbl)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-level6.proofp-aux))))

(defthm level6.proof-listp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level6.proof-listp-aux x axioms thms atbl)
                  t))
  :hints (("Goal" :in-theory (enable definition-of-level6.proof-listp-aux))))

(defthm level6.proof-listp-aux-of-cons
  (equal (level6.proof-listp-aux (cons a x) axioms thms atbl)
         (and (level6.proofp-aux a axioms thms atbl)
              (level6.proof-listp-aux x axioms thms atbl)))
  :hints (("Goal" :in-theory (enable definition-of-level6.proof-listp-aux))))

(defthms-flag
  :thms ((proof booleanp-of-level6.proofp-aux
                (equal (booleanp (level6.proofp-aux x axioms thms atbl))
                       t))
         (t booleanp-of-level6.proof-listp-aux
            (equal (booleanp (level6.proof-listp-aux x axioms thms atbl))
                   t)))
  :hints(("Goal"
          :in-theory (enable definition-of-level6.proofp-aux)
          :induct (logic.appeal-induction flag x))))

(deflist level6.proof-listp-aux (x axioms thms atbl)
  (level6.proofp-aux x axioms thms atbl)
  :already-definedp t)

(defthms-flag
  ;; We now prove that level6.proofp-aux is sound.  I.e., it only accepts appeals
  ;; whose conclusions are provable in the sense of logic.proofp.
  :@contextp t
  :shared-hyp (and (@obligations level6.step-okp)
                   (mapp atbl)
                   (equal (cdr (lookup 'not atbl)) 1)
                   (equal (cdr (lookup 'equal atbl)) 2)
                   (equal (cdr (lookup 'iff atbl)) 2)
                   (equal (cdr (lookup 'if atbl)) 3))
  :thms ((proof logic.provablep-when-level6.proofp-aux
                (implies (and (logic.appealp x)
                              (level6.proofp-aux x axioms thms atbl))
                         (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                                t)))
         (t logic.provable-listp-when-level6.proof-listp-aux
            (implies (and (logic.appeal-listp x)
                          (level6.proof-listp-aux x axioms thms atbl))
                     (equal (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-level6.proofp-aux))))

(defthms-flag
  ;; We also show that any proof accepted by logic.proofp is still accepted,
  ;; i.e., level6.proofp-aux is "strictly more capable" than logic.proofp.
  ;; THESE THEOREMS MUST BE LEFT DISABLED!
  :thms ((proof level6.proofp-aux-when-logic.proofp
                (implies (logic.proofp x axioms thms atbl)
                         (equal (level6.proofp-aux x axioms thms atbl)
                                t)))
         (t level6.proof-listp-aux-when-logic.proof-listp
            (implies (logic.proof-listp x axioms thms atbl)
                     (equal (level6.proof-listp-aux x axioms thms atbl)
                            t))))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-level6.proofp-aux
                              definition-of-logic.proofp))))

(in-theory (disable level6.proofp-aux-when-logic.proofp
                    level6.proof-listp-aux-when-logic.proof-listp))

(defthm forcing-level6.proofp-aux-of-logic.provable-witness
  ;; Corollary: Suppose F is any provable formula.  Then, the witnessing
  ;; proof of F is acceptable by level6.proofp-aux.
  (implies (force (logic.provablep formula axioms thms atbl))
           (equal (level6.proofp-aux (logic.provable-witness formula axioms thms atbl) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level6.proofp-aux-when-logic.proofp))))



(definlined@ level6.proofp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (and (@obligations level6.step-okp)
       (mapp atbl)
       (equal (cdr (lookup 'not atbl)) 1)
       (equal (cdr (lookup 'equal atbl)) 2)
       (equal (cdr (lookup 'iff atbl)) 2)
       (equal (cdr (lookup 'if atbl)) 3)
       (level6.proofp-aux x axioms thms atbl)))

(defthm booleanp-of-level6.proofp
  (equal (booleanp (level6.proofp x axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable level6.proofp))))

(defthm logic.provablep-when-level6.proofp
  (implies (and (logic.appealp x)
                (level6.proofp x axioms thms atbl))
           (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level6.proofp))))

