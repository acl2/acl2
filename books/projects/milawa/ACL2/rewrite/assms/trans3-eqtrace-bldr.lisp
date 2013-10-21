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
(include-book "trans1-eqtrace-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund rw.trans3-eqtrace-bldr (x box proofs)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box)
                              (rw.trans3-eqtrace-okp x)
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
        (build.disjoined-transitivity-of-iff proof1 (build.disjoined-commute-iff proof2)))
    (build.disjoined-transitivity-of-equal (first proofs)
                                           (build.disjoined-commute-equal (second proofs)))))

(defobligations rw.trans3-eqtrace-bldr
  (build.disjoined-iff-from-equal
   build.disjoined-transitivity-of-equal
   build.disjoined-transitivity-of-iff
   build.disjoined-commute-equal
   build.disjoined-commute-iff))

(encapsulate
 ()
 (local (in-theory (enable rw.eqtrace-formula
                           rw.trans3-eqtrace-bldr
                           rw.trans3-eqtrace-okp
                           lemma-1-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                           lemma-2-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                           lemma-3-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                           lemma-4-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr)))

 (defthm rw.trans3-eqtrace-bldr-under-iff
   (iff (rw.trans3-eqtrace-bldr x box proofs)
        t))

 (defthm forcing-logic.appealp-of-rw.trans3-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.trans3-eqtrace-okp x)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))))
            (equal (logic.appealp (rw.trans3-eqtrace-bldr x box proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.trans3-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.trans3-eqtrace-okp x)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))))
            (equal (logic.conclusion (rw.trans3-eqtrace-bldr x box proofs))
                   (rw.eqtrace-formula x box)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.trans3-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.trans3-eqtrace-okp x)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))
                        ;; ---
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.trans3-eqtrace-bldr)))
            (equal (logic.proofp (rw.trans3-eqtrace-bldr x box proofs) axioms thms atbl)
                   t)))

 (verify-guards rw.trans3-eqtrace-bldr))

