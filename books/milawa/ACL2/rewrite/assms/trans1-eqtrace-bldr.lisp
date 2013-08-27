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
(include-book "eqtrace-okp")
(include-book "transitivity-eqtraces")
(include-book "../../clauses/basic-bldrs")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund rw.trans1-eqtrace-bldr (x box proofs)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box)
                              (rw.trans1-eqtrace-okp x)
                              (rw.eqtrace-okp x box)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box)))
                  :verify-guards nil)
           (ignore box))
  (if (rw.eqtrace->iffp x)
      (let ((proof1 (if (rw.eqtrace->iffp (first (rw.eqtrace->subtraces x)))
                        (first proofs)
                      (build.disjoined-iff-from-equal (first proofs))))
            (proof2 (if (rw.eqtrace->iffp (second (rw.eqtrace->subtraces x)))
                        (second proofs)
                      (build.disjoined-iff-from-equal (second proofs)))))
        (build.disjoined-transitivity-of-iff proof1 proof2))
    (build.disjoined-transitivity-of-equal (first proofs) (second proofs))))

(defobligations rw.trans1-eqtrace-bldr
  (build.disjoined-iff-from-equal
   build.disjoined-transitivity-of-equal
   build.disjoined-transitivity-of-iff))

(defthmd lemma-1-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
  (implies (and (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list x box))
                (force (consp x)))
           (equal (logic.conclusion (car proofs))
                  (rw.eqtrace-formula (car x) box))))

(defthmd lemma-2-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
  (implies (and (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list x box))
                (force (consp (cdr x))))
           (equal (logic.conclusion (second proofs))
                  (rw.eqtrace-formula (second x) box))))

(defthmd lemma-3-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
  (implies (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list x box))
           (equal (consp proofs)
                  (consp x))))

(defthmd lemma-4-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
  (implies (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list x box))
           (equal (consp (cdr proofs))
                  (consp (cdr x)))))


(encapsulate
 ()
 (local (in-theory (enable rw.eqtrace-formula
                           rw.trans1-eqtrace-bldr
                           rw.trans1-eqtrace-okp
                           lemma-1-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                           lemma-2-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                           lemma-3-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                           lemma-4-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr)))

 (defthm forcing-rw.trans1-eqtrace-bldr-under-iff
   (iff (rw.trans1-eqtrace-bldr x box proofs)
        t))

 (defthm forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.trans1-eqtrace-okp x)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))))
            (equal (logic.appealp (rw.trans1-eqtrace-bldr x box proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.trans1-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.trans1-eqtrace-okp x)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))))
            (equal (logic.conclusion (rw.trans1-eqtrace-bldr x box proofs))
                   (rw.eqtrace-formula x box)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.trans1-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.trans1-eqtrace-okp x)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))
                        ;; ---
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.trans1-eqtrace-bldr)))
            (equal (logic.proofp (rw.trans1-eqtrace-bldr x box proofs) axioms thms atbl)
                   t)))

 (verify-guards rw.trans1-eqtrace-bldr))
