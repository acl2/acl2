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
(include-book "level10")
(include-book "../tactics/compiler")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund level11.step-okp (x worlds defs axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (tactic.world-listp worlds)
                              (definition-listp defs)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method (logic.method x)))
    (cond
     ((equal method 'tactic.compile-skeleton)
      (tactic.compile-skeleton-okp x worlds axioms thms atbl))
     (t
      (level10.step-okp x worlds defs axioms thms atbl)))))

(defobligations level11.step-okp
  (tactic.compile-skeleton
   level10.step-okp))

(encapsulate
 ()
 (local (in-theory (enable level11.step-okp)))

 (defthm@ soundness-of-level11.step-okp
   (implies (and (level11.step-okp x worlds defs axioms thms atbl)
                 (force (and (logic.appealp x)
                             (tactic.world-listp worlds)
                             (tactic.world-list-atblp worlds atbl)
                             (tactic.world-list-env-okp worlds axioms thms)
                             (logic.formula-list-atblp defs atbl)
                             (definition-listp defs)
                             (subsetp defs axioms)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (mapp atbl)
                             (equal (cdr (lookup 'if atbl)) 3)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'ordp atbl)) 1)
                             (equal (cdr (lookup 'ord< atbl)) 2)
                             (equal (cdr (lookup 'car atbl)) 1)
                             (equal (cdr (lookup 'cdr atbl)) 1)
                             (equal (cdr (lookup 'consp atbl)) 1)
                             (equal (cdr (lookup 'cons atbl)) 2)
                             (@obligations level11.step-okp))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t)))

 (defthm level11.step-okp-when-level10.step-okp
   ;; This shows that our new step checker is "complete" in the sense that all
   ;; previously acceptable appeals are still acceptable.
   (implies (level10.step-okp x worlds defs axioms thms atbl)
            (level11.step-okp x worlds defs axioms thms atbl))
   :hints(("Goal" :in-theory (enable level10.step-okp
                                     level9.step-okp
                                     level8.step-okp
                                     level7.step-okp
                                     level6.step-okp
                                     level5.step-okp
                                     level4.step-okp
                                     level3.step-okp
                                     level2.step-okp
                                     logic.appeal-step-okp))))

 (defthm level11.step-okp-when-not-consp
   (implies (not (consp x))
            (equal (level11.step-okp x worlds defs axioms thms atbl)
                   nil))
   :hints(("Goal" :in-theory (enable logic.method)))))


(encapsulate
 ()
 (defund level11.flag-proofp-aux (flag x worlds defs axioms thms atbl)
   (declare (xargs :guard (and (if (equal flag 'proof)
                                   (logic.appealp x)
                                 (and (equal flag 'list)
                                      (logic.appeal-listp x)))
                               (tactic.world-listp worlds)
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))
                   :measure (two-nats-measure (rank x) (if (equal flag 'proof) 1 0))))
   (if (equal flag 'proof)
       (and (level11.step-okp x worlds defs axioms thms atbl)
            (level11.flag-proofp-aux 'list (logic.subproofs x) worlds defs axioms thms atbl))
     (if (consp x)
         (and (level11.flag-proofp-aux 'proof (car x) worlds defs axioms thms atbl)
              (level11.flag-proofp-aux 'list (cdr x) worlds defs axioms thms atbl))
       t)))

 (definlined level11.proofp-aux (x worlds defs axioms thms atbl)
   (declare (xargs :guard (and (logic.appealp x)
                               (tactic.world-listp worlds)
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level11.flag-proofp-aux 'proof x worlds defs axioms thms atbl))

 (definlined level11.proof-listp-aux (x worlds defs axioms thms atbl)
   (declare (xargs :guard (and (logic.appeal-listp x)
                               (tactic.world-listp worlds)
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level11.flag-proofp-aux 'list x worlds defs axioms thms atbl))

 (defthmd definition-of-level11.proofp-aux
   (equal (level11.proofp-aux x worlds defs axioms thms atbl)
          (and (level11.step-okp x worlds defs axioms thms atbl)
               (level11.proof-listp-aux (logic.subproofs x) worlds defs axioms thms atbl)))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level11.proofp-aux level11.proof-listp-aux level11.flag-proofp-aux))))

 (defthmd definition-of-level11.proof-listp-aux
   (equal (level11.proof-listp-aux x worlds defs axioms thms atbl)
          (if (consp x)
              (and (level11.proofp-aux (car x) worlds defs axioms thms atbl)
                   (level11.proof-listp-aux (cdr x) worlds defs axioms thms atbl))
            t))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level11.proofp-aux level11.proof-listp-aux level11.flag-proofp-aux))))

 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition level11.proofp-aux))))
 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition level11.proof-listp)))))



(defthm level11.proofp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level11.proofp-aux x worlds defs axioms thms atbl)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-level11.proofp-aux))))

(defthm level11.proof-listp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level11.proof-listp-aux x worlds defs axioms thms atbl)
                  t))
  :hints (("Goal" :in-theory (enable definition-of-level11.proof-listp-aux))))

(defthm level11.proof-listp-aux-of-cons
  (equal (level11.proof-listp-aux (cons a x) worlds defs axioms thms atbl)
         (and (level11.proofp-aux a worlds defs axioms thms atbl)
              (level11.proof-listp-aux x worlds defs axioms thms atbl)))
  :hints (("Goal" :in-theory (enable definition-of-level11.proof-listp-aux))))

(defthms-flag
  :thms ((proof booleanp-of-level11.proofp-aux
                (equal (booleanp (level11.proofp-aux x worlds defs axioms thms atbl))
                       t))
         (t booleanp-of-level11.proof-listp-aux
            (equal (booleanp (level11.proof-listp-aux x worlds defs axioms thms atbl))
                   t)))
  :hints(("Goal"
          :in-theory (enable definition-of-level11.proofp-aux)
          :induct (logic.appeal-induction flag x))))

(deflist level11.proof-listp-aux (x worlds defs axioms thms atbl)
  (level11.proofp-aux x worlds defs axioms thms atbl)
  :already-definedp t)

(defthms-flag
  ;; We now prove that level11.proofp-aux is sound.  I.e., it only accepts appeals
  ;; whose conclusions are provable in the sense of logic.proofp.
  :@contextp t
  :shared-hyp (and (@obligations level11.step-okp)
                   (equal (cdr (lookup 'if atbl)) 3)
                   (equal (cdr (lookup 'equal atbl)) 2)
                   (equal (cdr (lookup 'iff atbl)) 2)
                   (equal (cdr (lookup 'not atbl)) 1)
                   (equal (cdr (lookup 'ordp atbl)) 1)
                   (equal (cdr (lookup 'ord< atbl)) 2)
                   (equal (cdr (lookup 'car atbl)) 1)
                   (equal (cdr (lookup 'cdr atbl)) 1)
                   (equal (cdr (lookup 'consp atbl)) 1)
                   (equal (cdr (lookup 'cons atbl)) 2)
                   (logic.formula-list-atblp defs atbl)
                   (definition-listp defs)
                   (subsetp defs axioms)
                   (mapp atbl)
                   (tactic.world-listp worlds)
                   (tactic.world-list-atblp worlds atbl)
                   (tactic.world-list-env-okp worlds axioms thms)
                   )
  :thms ((proof logic.provablep-when-level11.proofp-aux
                (implies (and (logic.appealp x)
                              (level11.proofp-aux x worlds defs axioms thms atbl))
                         (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                                t)))
         (t logic.provable-listp-when-level11.proof-listp-aux
            (implies (and (logic.appeal-listp x)
                          (level11.proof-listp-aux x worlds defs axioms thms atbl))
                     (equal (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-level11.proofp-aux))))

(defthms-flag
  ;; We also show that any proof accepted by logic.proofp is still accepted,
  ;; i.e., level11.proofp-aux is "strictly more capable" than logic.proofp.
  ;; THESE THEOREMS MUST BE LEFT DISABLED!
  :thms ((proof level11.proofp-aux-when-logic.proofp
                (implies (logic.proofp x axioms thms atbl)
                         (equal (level11.proofp-aux x worlds defs axioms thms atbl)
                                t)))
         (t level11.proof-listp-aux-when-logic.proof-listp
            (implies (logic.proof-listp x axioms thms atbl)
                     (equal (level11.proof-listp-aux x worlds defs axioms thms atbl)
                            t))))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-level11.proofp-aux
                              definition-of-logic.proofp))))

(in-theory (disable level11.proofp-aux-when-logic.proofp
                    level11.proof-listp-aux-when-logic.proof-listp))

(defthm forcing-level11.proofp-aux-of-logic.provable-witness
  ;; Corollary: Suppose F is any provable formula.  Then, the witnessing
  ;; proof of F is acceptable by level11.proofp-aux.
  (implies (force (logic.provablep formula axioms thms atbl))
           (equal (level11.proofp-aux (logic.provable-witness formula axioms thms atbl) worlds defs axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level11.proofp-aux-when-logic.proofp))))


;; The level 11 adapter trace will be named level11.proofp and will have, as its extras,
;; a list of the form (defs worlds core).

(defun@ level11.static-checksp (worlds defs axioms thms atbl)
  ;; NOTE!  We leave this enabled!
  (declare (xargs :guard (and (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (and (mapp atbl)
       (@obligations level11.step-okp)
       (equal (cdr (lookup 'if atbl)) 3)
       (equal (cdr (lookup 'equal atbl)) 2)
       (equal (cdr (lookup 'iff atbl)) 2)
       (equal (cdr (lookup 'not atbl)) 1)
       (equal (cdr (lookup 'ordp atbl)) 1)
       (equal (cdr (lookup 'ord< atbl)) 2)
       (equal (cdr (lookup 'car atbl)) 1)
       (equal (cdr (lookup 'cdr atbl)) 1)
       (equal (cdr (lookup 'consp atbl)) 1)
       (equal (cdr (lookup 'cons atbl)) 2)
       (definition-listp defs)
       (logic.fast-arities-okp (logic.formula-list-arities defs nil) atbl)
       (ordered-list-subsetp (mergesort defs) (mergesort axioms))
       (tactic.world-listp worlds)
       (tactic.fast-world-list-atblp worlds atbl)
       (tactic.fast-world-list-env-okp worlds axioms thms)))

(defund@ level11.proofp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'level11.proofp)
         (not subproofs)
         (tuplep 3 extras)
         (let ((defs   (first extras))
               (worlds (second extras))
               (core   (third extras)))
           (and
            (ACL2::time$ (level11.static-checksp worlds defs axioms thms atbl))
            (logic.appealp core)
            (equal conclusion (logic.conclusion core))
            (level11.proofp-aux core worlds defs axioms thms atbl))))))

(defthm booleanp-of-level11.proofp
  (equal (booleanp (level11.proofp x axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable level11.proofp))))

(defthm logic.provablep-when-level11.proofp
  (implies (and (logic.appealp x)
                (level11.proofp x axioms thms atbl))
           (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                  t))
  :hints(("Goal"
          :in-theory (e/d (level11.proofp)
                          (logic.provablep-when-level11.proofp-aux))
          :use ((:instance logic.provablep-when-level11.proofp-aux
                           (x      (third (logic.extras x)))
                           (defs   (first (logic.extras x)))
                           (worlds (second (logic.extras x))))))))

(defun level11.adapter (proof defs initial-world all-worlds)
  (declare (xargs :mode :program)
           (ignore initial-world))
  (logic.appeal 'level11.proofp
                (logic.conclusion proof)
                nil
                (list defs all-worlds proof)))

