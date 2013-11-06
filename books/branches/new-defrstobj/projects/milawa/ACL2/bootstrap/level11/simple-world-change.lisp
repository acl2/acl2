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


(%autoadmit tactic.simple-world-change-aux)

(%autoprove tactic.worldp-of-tactic.simple-world-change-aux
            (%autoinduct tactic.simple-world-change-aux)
            (%restrict default tactic.simple-world-change-aux (equal changes 'changes)))

(%autoprove tactic.world-atblp-of-tactic.simple-world-change-aux
            (%autoinduct tactic.simple-world-change-aux)
            (%restrict default tactic.simple-world-change-aux (equal changes 'changes)))

(%autoprove tactic.world-env-okp-of-tactic.simple-world-change-aux
            (%autoinduct tactic.simple-world-change-aux)
            (%restrict default tactic.simple-world-change-aux (equal changes 'changes)))

(%autoprove tactic.world->index-of-tactic.simple-world-change-aux
            (%autoinduct tactic.simple-world-change-aux)
            (%restrict default tactic.simple-world-change-aux (equal changes 'changes)))


(%autoadmit tactic.simple-world-change)

(%autoprove tactic.worldp-of-tactic.simple-world-change
            (%enable default tactic.simple-world-change))

(%autoprove tactic.world-atblp-of-tactic.simple-world-change
            (%enable default tactic.simple-world-change))

(%autoprove tactic.world-env-okp-of-tactic.simple-world-change
            (%enable default tactic.simple-world-change))

(%autoprove tactic.world->index-of-tactic.simple-world-change
            (%enable default tactic.simple-world-change))


(%autoadmit tactic.simple-change-world-okp)

(%autoprove booleanp-of-tactic.simple-change-world-okp
            (%enable default tactic.simple-change-world-okp))

(%autoprove tactic.skeleton->goals-when-tactic.simple-change-world-okp
            (%enable default tactic.simple-change-world-okp))


(%autoadmit tactic.simple-change-world-tac)

(%autoprove tactic.skeletonp-of-tactic.simple-change-world-tac
            (%enable default tactic.simple-change-world-tac))

(%autoprove tactic.simple-change-world-okp-of-tactic.simple-change-world-tac
            (%enable default
                     tactic.simple-change-world-tac
                     tactic.simple-change-world-okp))

(%autoadmit tactic.simple-change-world-compile-world)

(%autoprove tactic.worldp-of-tactic.simple-change-world-compile-world
            (%enable default tactic.simple-change-world-compile-world))

(%autoprove tactic.world-atblp-of-tactic.simple-change-world-compile-world
            (%enable default tactic.simple-change-world-compile-world))

(%autoprove tactic.world-env-okp-of-tactic.simple-change-world-compile-world
            (%enable default tactic.simple-change-world-compile-world))


(%ensure-exactly-these-rules-are-missing "../../tactics/simple-world-change")
