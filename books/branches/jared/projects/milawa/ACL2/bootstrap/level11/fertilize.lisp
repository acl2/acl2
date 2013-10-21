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
(include-book "skeletonp")
(include-book "replace-subterm")
(%interactive)

(defthm logic.term-listp-when-tuplep-2-of-logic.termps
  ;; BOZO unlocalize in tactics/fertilize
  (implies (and (tuplep 2 x)
                (logic.termp (first x))
                (logic.termp (second x)))
           (equal (logic.term-listp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(%autoprove logic.term-listp-when-tuplep-2-of-logic.termps)

(%autoadmit tactic.fertilize-okp)
(%autoadmit tactic.fertilize-env-okp)

(%autoprove booleanp-of-tactic.fertilize-okp
            (%enable default tactic.fertilize-okp))

(%autoprove booleanp-of-tactic.fertilize-env-okp
            (%enable default tactic.fertilize-env-okp))


(%autoadmit tactic.fertilize-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.fertilize-tac
            (%enable default tactic.fertilize-tac))

(%autoprove forcing-tactic.fertilize-okp-of-tactic.fertilize-tac
            (%enable default
                     tactic.fertilize-tac
                     tactic.fertilize-okp))

(%autoprove forcing-tactic.fertilize-env-okp-of-tactic.fertilize-tac
            (%enable default
                     tactic.fertilize-tac
                     tactic.fertilize-env-okp))


(%deftheorem tactic.fertilize-lemma1-helper)

(%autoadmit tactic.fertilize-lemma1)

(encapsulate
 ()
 (local (%enable default
                 tactic.fertilize-lemma1-helper
                 tactic.fertilize-lemma1))

 (%autoprove tactic.fertilize-lemma1-under-iff)
 (%autoprove forcing-logic.appealp-of-tactic.fertilize-lemma1)
 (%autoprove forcing-logic.conclusion-of-tactic.fertilize-lemma1)
 (%autoprove forcing-logic.proofp-of-tactic.fertilize-lemma1))




(%autoadmit tactic.fertilize-bldr)

(encapsulate
 ()
 (local (%enable default tactic.fertilize-bldr))
 (%autoprove tactic.fertilize-bldr-under-iff)
 (%autoprove forcing-logic.appealp-of-tactic.fertilize-bldr)
 (%autoprove forcing-logic.conclusion-of-tactic.fertilize-bldr)
 (%autoprove forcing-logic.proofp-of-tactic.fertilize-bldr))



(%autoadmit tactic.fertilize-compile)


(encapsulate
 ()
 (local (%enable default
                 tactic.fertilize-okp
                 tactic.fertilize-env-okp
                 tactic.fertilize-compile
                 logic.term-formula))

 (defthmd crock-for-tactic.fertilize-compile
   (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
            (equal (logic.conclusion (first proofs))
                   (clause.clause-formula (first goals)))))

 (%autoprove crock-for-tactic.fertilize-compile)

 (local (%enable default crock-for-tactic.fertilize-compile))

 (%autoprove forcing-logic.appeal-listp-of-tactic.fertilize-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.fertilize-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.fertilize-compile))

(%ensure-exactly-these-rules-are-missing "../../tactic/fertilize")