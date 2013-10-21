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
(%interactive)


(%autoadmit tactic.use-okp)

(%autoprove booleanp-of-tactic.use-okp
            (%enable default tactic.use-okp))

(%autoadmit tactic.use-env-okp)

(%autoprove booleanp-of-tactic.use-env-okp
            (%enable default tactic.use-env-okp))



(%autoadmit tactic.use-tac)
(%autoprove forcing-tactic.skeletonp-of-tactic.use-tac
            (%enable default tactic.use-tac))
(%autoprove forcing-tactic.use-okp-of-tactic.use-tac
            (%enable default tactic.use-tac tactic.use-okp))
(%autoprove forcing-tactic.use-env-okp-of-tactic.use-tac
            (%enable default tactic.use-tac tactic.use-env-okp))



(defthmd crock-1-for-tactic.use-compile
  ;; BOZO unlocalize/rename
  (implies (and (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (TACTIC.SKELETON->GOALS X)))
                       (LOGIC.STRIP-CONCLUSIONS PROOFS))
                (force (tactic.skeletonp x))
                (force (consp proofs)))
           (equal (logic.conclusion (first proofs))
                  (logic.disjoin-formulas
                   (logic.term-list-formulas (first (tactic.skeleton->goals x)))))))

(%autoprove crock-1-for-tactic.use-compile)
(local (%enable default crock-1-for-tactic.use-compile))

(%autoadmit tactic.use-compile)

(encapsulate
 ()
 (local (%enable default
                 tactic.use-okp
                 tactic.use-env-okp
                 tactic.use-compile
                 logic.term-formula))

 (%autoprove forcing-logic.appeal-listp-of-tactic.use-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.use-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.use-compile))

(%ensure-exactly-these-rules-are-missing "../../tactics/use")