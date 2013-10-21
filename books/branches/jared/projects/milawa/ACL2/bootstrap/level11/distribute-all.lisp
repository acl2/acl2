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
(include-book "fertilize")
(%interactive)

(encapsulate
 ()
 (%autoadmit distribute.type1-literalp)
 (%autoadmit distribute.type1-var)
 (%autoadmit distribute.type1-expr)
 (%autoadmit distribute.substitute-type1-literal)
 (%autoadmit distribute.substitute-type1-literal-bldr)

 (local (%enable default
                 distribute.substitute-type1-literal-bldr
                 distribute.substitute-type1-literal
                 distribute.type1-literalp
                 distribute.type1-var
                 distribute.type1-expr))

 (%autoprove booleanp-of-distribute.type1-literalp)
 (%autoprove cons-listp-of-distribute.substitute-type1-literal)
 (%autoprove forcing-logic.term-listp-of-distribute.substitute-type1-literal)
 (%autoprove forcing-logic.term-list-atblp-of-distribute.substitute-type1-literal)
 (%autoprove distribute.substitute-type1-literal-bldr-under-iff)
 (%autoprove forcing-logic.appealp-of-distribute.substitute-type1-literal-bldr)
 (%autoprove forcing-logic.conclusion-of-distribute.substitute-type1-literal-bldr)
 (%autoprove forcing-logic.proofp-of-distribute.substitute-type1-literal-bldr))


(encapsulate
 ()
 (%autoadmit distribute.type2-literalp)
 (%autoadmit distribute.type2-var)
 (%autoadmit distribute.type2-expr)
 (%autoadmit distribute.substitute-type2-literal)
 (%autoadmit distribute.substitute-type2-literal-bldr)

 (local (%enable default
                 distribute.type2-literalp
                 distribute.type2-var
                 distribute.type2-expr
                 distribute.substitute-type2-literal
                 distribute.substitute-type2-literal-bldr))

 (%autoprove booleanp-of-distribute.type2-literalp)
 (%autoprove cons-listp-of-distribute.substitute-type2-literal)
 (%autoprove forcing-logic.term-listp-of-distribute.substitute-type2-literal)
 (%autoprove forcing-logic.term-list-atblp-of-distribute.substitute-type2-literal)
 (%autoprove distribute.substitute-type2-literal-bldr-under-iff)
 (%autoprove forcing-logic.appealp-of-distribute.substitute-type2-literal-bldr)
 (%autoprove forcing-logic.conclusion-of-distribute.substitute-type2-literal-bldr)
 (%autoprove forcing-logic.proofp-of-distribute.substitute-type2-literal-bldr))



(encapsulate
 ()
 (%autoadmit distribute.find-type1-literal)

 (%autoprove distribute.type1-literalp-of-distribute.find-type1-literal
             (%autoinduct distribute.find-type1-literal)
             (%restrict default distribute.find-type1-literal (equal x 'x)))

 (%autoprove forcing-logic.termp-of-distribute.find-type1-literal
             (%autoinduct distribute.find-type1-literal)
             (%restrict default distribute.find-type1-literal (equal x 'x)))

 (%autoprove memberp-of-distribute.find-type1-literal
             (%autoinduct distribute.find-type1-literal)
             (%restrict default distribute.find-type1-literal (equal x 'x))))

(encapsulate
 ()
 (%autoadmit distribute.find-type2-literal)

 (%autoprove distribute.type2-literalp-of-distribute.find-type2-literal
             (%autoinduct distribute.find-type2-literal)
             (%restrict default distribute.find-type2-literal (equal x 'x)))

 (%autoprove forcing-logic.termp-of-distribute.find-type2-literal
             (%autoinduct distribute.find-type2-literal)
             (%restrict default distribute.find-type2-literal (equal x 'x)))

 (%autoprove memberp-of-distribute.find-type2-literal
             (%autoinduct distribute.find-type2-literal)
             (%restrict default distribute.find-type2-literal (equal x 'x))))


(encapsulate
 ()
 (%autoadmit distribute.try-distributing-clause)
 (%autoadmit distribute.try-distributing-clause-bldr)
 (local (%enable default
                 distribute.try-distributing-clause
                 distribute.try-distributing-clause-bldr))
 (%autoprove consp-of-distribute.try-distributing-clause)
 (%autoprove forcing-logic.term-listp-of-distribute.try-distributing-clause)
 (%autoprove forcing-logic.term-list-atblp-of-distribute.try-distributing-clause)
 (%autoprove distribute.try-distributing-clause-bldr-under-iff)
 (%autoprove forcing-logic.appealp-of-distribute.try-distributing-clause-bldr)
 (%autoprove forcing-logic.conclusion-of-distribute.try-distributing-clause-bldr)
 (%autoprove forcing-logic.proofp-of-distribute.try-distributing-clause-bldr))


(%defprojection
 :list (distribute.try-distributing-clause-list x)
 :element (distribute.try-distributing-clause x))

(%autoprove cons-listp-of-distribute.try-distributing-clause-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-listp-of-distribute.try-distributing-clause-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-distribute.try-distributing-clause-list
            (%cdr-induction x))


(encapsulate
 ()
 (%autoadmit distribute.try-distributing-clause-list-bldr)
 (%autoprove forcing-logic.appeal-listp-of-distribute.try-distributing-clause-list-bldr
             (%autoinduct distribute.try-distributing-clause-list-bldr)
             (%restrict default distribute.try-distributing-clause-list-bldr (equal x 'x)))
 (%autoprove forcing-logic.strip-conclusions-of-distribute.try-distributing-clause-list-bldr
             (%autoinduct distribute.try-distributing-clause-list-bldr)
             (%restrict default distribute.try-distributing-clause-list-bldr (equal x 'x)))
 (%autoprove forcing-logic.proof-listp-of-distribute.try-distributing-clause-list-bldr
             (%autoinduct distribute.try-distributing-clause-list-bldr)
             (%restrict default distribute.try-distributing-clause-list-bldr (equal x 'x))))


(%autoadmit tactic.distribute-all-okp)

(%autoprove booleanp-of-tactic.distribute-all-okp
            (%enable default tactic.distribute-all-okp))


(%autoadmit tactic.distribute-all-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.distribute-all-tac
            (%enable default tactic.distribute-all-tac))

(%autoprove forcing-tactic.distribute-all-okp-of-tactic.distribute-all-tac
            (%enable default
                     tactic.distribute-all-tac
                     tactic.distribute-all-okp))



(encapsulate
 ()
 (%autoadmit tactic.distribute-all-compile)
 (local (%enable default
                 tactic.distribute-all-okp
                 tactic.distribute-all-compile))
 (%autoprove forcing-logic.appeal-listp-of-tactic.distribute-all-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.distribute-all-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.distribute-all-compile))

(%ensure-exactly-these-rules-are-missing "../../tactics/distribute-all")