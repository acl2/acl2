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
(include-book "find-proof")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


; Proof Replacement.
;
; A basic goal of this file is to be able to support reasoning of the form,
;
;  Given: BLDR is sound as long as FOO is a theorem.
;  Given: A proof of FOO.
;  Conclude: BLDR's conclusions are sound even when FOO is not a theorem.
;
; To carry out this sort of thing, we introduce a proof-replacing function,
; which walks through an appeal and replaces any conclusions of some form
; with a new proof.  Then, we see that
;
;   Replace(BLDR's output, Proof of FOO)
;
; Is a proof of BLDR's output which is true even without having FOO as a
; theorem of the history.

(defund logic.flag-replace-proofs (flag x proofs)
  (declare (xargs :guard (and (if (equal flag 'proof)
                                  (logic.appealp x)
                                (and (equal flag 'list)
                                     (logic.appeal-listp x)))
                              (logic.appeal-listp proofs))
                  :measure (two-nats-measure (rank x) (if (equal flag 'proof) 1 0))
                  :verify-guards nil))
  (if (equal flag 'proof)
      (or (logic.find-proof (logic.conclusion x) proofs)
          (logic.appeal (logic.method x)
                        (logic.conclusion x)
                        (logic.flag-replace-proofs 'list (logic.subproofs x) proofs)
                        (logic.extras x)))
    (if (consp x)
        (cons (logic.flag-replace-proofs 'proof (car x) proofs)
              (logic.flag-replace-proofs 'list (cdr x) proofs))
      nil)))

(defund logic.replace-proofs (x proofs)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.appeal-listp proofs))
                  :verify-guards nil))
  (logic.flag-replace-proofs 'proof x proofs))

(defund logic.replace-proofs-list (x proofs)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.appeal-listp proofs))
                  :verify-guards nil))
  (logic.flag-replace-proofs 'list x proofs))

(defthmd definition-of-logic.replace-proofs
  (equal (logic.replace-proofs x proofs)
         (or (logic.find-proof (logic.conclusion x) proofs)
             (logic.appeal (logic.method x)
                           (logic.conclusion x)
                           (logic.replace-proofs-list (logic.subproofs x) proofs)
                           (logic.extras x))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.flag-replace-proofs
                                    logic.replace-proofs
                                    logic.replace-proofs-list))))

(defthmd definition-of-logic.replace-proofs-list
  (equal (logic.replace-proofs-list x proofs)
         (if (consp x)
             (cons (logic.replace-proofs (car x) proofs)
                   (logic.replace-proofs-list (cdr x) proofs))
           nil))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable logic.flag-replace-proofs
                             logic.replace-proofs
                             logic.replace-proofs-list)
          :expand (logic.flag-replace-proofs 'list x proofs))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.replace-proofs))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.replace-proofs-list))))

(defthm logic.replace-proofs-list-when-not-consp
  (implies (not (consp x))
           (equal (logic.replace-proofs-list x proofs)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.replace-proofs-list))))

(defthm logic.replace-proofs-list-of-cons
  (equal (logic.replace-proofs-list (cons a x) proofs)
         (cons (logic.replace-proofs a proofs)
               (logic.replace-proofs-list x proofs)))
  :hints(("Goal" :in-theory (enable definition-of-logic.replace-proofs-list))))

(defprojection
  :list (logic.replace-proofs-list x proofs)
  :element (logic.replace-proofs x proofs)
  :already-definedp t)



(defthms-flag
  :shared-hyp (force (logic.appeal-listp proofs))
  :thms ((proof logic.appealp-of-logic.replace-proofs
                (implies (force (logic.appealp x))
                         (equal (logic.appealp (logic.replace-proofs x proofs))
                                t)))
         (t logic.appeal-listp-of-logic.replace-proofs-list
            (implies (force (logic.appeal-listp x))
                     (equal (logic.appeal-listp (logic.replace-proofs-list x proofs))
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (e/d (definition-of-logic.replace-proofs)
                          ((ACL2::force))))))

(defthms-flag
  :shared-hyp (force (logic.appeal-listp proofs))
  :thms ((proof logic.conclusion-of-logic.replace-proofs
                (implies (force (logic.appealp x))
                         (equal (logic.conclusion (logic.replace-proofs x proofs))
                                (logic.conclusion x))))
         (t logic.strip-conclusions-of-logic.replace-proofs-list
            (implies (force (logic.appeal-listp x))
                     (equal (logic.strip-conclusions (logic.replace-proofs-list x proofs))
                            (logic.strip-conclusions x)))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (e/d (definition-of-logic.replace-proofs)
                          ((ACL2::force))))))

(defthmd lemma-1-for-logic.proofp-of-logic.replace-proofs
  (implies (and (not (equal (logic.method x) 'axiom))
                (not (equal (logic.method x) 'theorem)))
           (equal
            (logic.appeal-step-okp x
                                   (difference axioms remove)
                                   (difference thms remove)
                                   atbl)
            (logic.appeal-step-okp x axioms thms atbl)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthmd lemma-2-for-logic.proofp-of-logic.replace-proofs
  (implies (and (or (equal (logic.method x) 'axiom)
                    (equal (logic.method x) 'theorem))
                (not (memberp (logic.conclusion x) remove)))
           (equal
            (logic.appeal-step-okp x
                                   (difference axioms remove)
                                   (difference thms remove)
                                   atbl)
            (logic.appeal-step-okp x axioms thms atbl)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp
                                    logic.axiom-okp
                                    logic.theorem-okp))))

(defthmd lemma-3-for-logic.proofp-of-logic.replace-proofs
  (implies (not (memberp (logic.conclusion x) remove))
           (equal (logic.appeal-step-okp x
                                         (difference axioms remove)
                                         (difference thms remove)
                                         atbl)
                  (logic.appeal-step-okp x axioms thms atbl)))
  :hints(("Goal" :use ((:instance lemma-1-for-logic.proofp-of-logic.replace-proofs)
                       (:instance lemma-2-for-logic.proofp-of-logic.replace-proofs)))))

(defthmd lemma-4-for-logic.proofp-of-logic.replace-proofs
  (implies (and (logic.proof-listp (logic.replace-proofs-list (logic.subproofs x) proofs)
                                   (difference axioms (logic.strip-conclusions proofs))
                                   (difference thms (logic.strip-conclusions proofs))
                                   atbl)
                (logic.appeal-listp proofs)
                (logic.proof-listp proofs
                                   (difference axioms (logic.strip-conclusions proofs))
                                   (difference thms (logic.strip-conclusions proofs))
                                   atbl)
                (logic.appealp x)
                (logic.appeal-step-okp x axioms thms atbl)
                (logic.proof-listp (logic.subproofs x) axioms thms atbl)
                (not (logic.find-proof (logic.conclusion x) proofs)))
           (logic.proofp (logic.appeal (logic.method x)
                                       (logic.conclusion x)
                                       (logic.replace-proofs-list (logic.subproofs x)
                                                                  proofs)
                                       (logic.extras x))
                         (difference axioms (logic.strip-conclusions proofs))
                         (difference thms (logic.strip-conclusions proofs))
                         atbl))
  :hints(("Goal"
          :in-theory (enable definition-of-logic.proofp)
          :use ((:instance lemma-appeal-step-for-forcing-logic.provablep-when-logic.subproofs-provable
                           (new-subproofs (logic.replace-proofs-list (logic.subproofs x) proofs)))
                (:instance lemma-3-for-logic.proofp-of-logic.replace-proofs
                           (x (logic.appeal (logic.method x)
                                            (logic.conclusion x)
                                            (logic.replace-proofs-list (logic.subproofs x) proofs)
                                            (logic.extras x)))
                           (remove (logic.strip-conclusions proofs)))))))

(defthms-flag
  :shared-hyp (and (force (logic.appeal-listp proofs))
                   (force (logic.proof-listp proofs
                                             (difference axioms (logic.strip-conclusions proofs))
                                             (difference thms (logic.strip-conclusions proofs))
                                             atbl)))
  :thms ((proof logic.proofp-of-logic.replace-proofs
                (implies (and (force (logic.appealp x))
                              (force (logic.proofp x axioms thms atbl)))
                         (equal (logic.proofp (logic.replace-proofs x proofs)
                                              (difference axioms (logic.strip-conclusions proofs))
                                              (difference thms (logic.strip-conclusions proofs))
                                              atbl)
                                t)))

         (t logic.proof-listp-of-logic.replace-proofs-list
            (implies (and (force (logic.appeal-listp x))
                          (force (logic.proof-listp x axioms thms atbl)))
                     (equal (logic.proof-listp (logic.replace-proofs-list x proofs)
                                               (difference axioms (logic.strip-conclusions proofs))
                                               (difference thms (logic.strip-conclusions proofs))
                                               atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-logic.replace-proofs
                             definition-of-logic.proofp
                             lemma-4-for-logic.proofp-of-logic.replace-proofs))))



(defthm logic.appeal-step-okp-in-larger-axiom-set
  (implies (and (subsetp axioms more-axioms)
                (logic.appeal-step-okp x axioms thms atbl))
           (equal (logic.appeal-step-okp x more-axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp
                                    logic.axiom-okp))))

(defthms-flag
  :shared-hyp (subsetp axioms more-axioms)
  :thms ((proof logic.proofp-in-larger-axiom-set
                (implies (logic.proofp x axioms thms atbl)
                         (equal (logic.proofp x more-axioms thms atbl)
                                t)))
         (t logic.proof-listp-in-larger-axiom-set
            (implies (logic.proof-listp x axioms thms atbl)
                     (equal (logic.proof-listp x more-axioms thms atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-logic.proofp))))

(defthm logic-provablep-in-larger-axiom-set
  (implies (and (subsetp axioms more-axioms)
                (logic.provablep x axioms thms atbl))
           (equal (logic.provablep x more-axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.provablep)
                                 ((ACL2::force))))))



(defthm logic.appeal-step-okp-in-larger-theorem-set
  (implies (and (subsetp thms more-thms)
                (logic.appeal-step-okp x axioms thms atbl))
           (equal (logic.appeal-step-okp x axioms more-thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp
                                    logic.theorem-okp))))

(defthms-flag
  :shared-hyp (subsetp thms more-thms)
  :thms ((proof logic.proofp-in-larger-theorem-set
                (implies (logic.proofp x axioms thms atbl)
                         (equal (logic.proofp x axioms more-thms atbl)
                                t)))
         (t logic.proof-listp-in-larger-theorem-set
            (implies (logic.proof-listp x axioms thms atbl)
                     (equal (logic.proof-listp x axioms more-thms atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-logic.proofp))))

(defthm logic-provablep-in-larger-theorem-set
  (implies (and (subsetp thms more-thms)
                (logic.provablep x axioms thms atbl))
           (equal (logic.provablep x axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.provablep)
                                 ((ACL2::force))))))




