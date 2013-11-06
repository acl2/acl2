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
(include-book "translate")
(%interactive)


(%autoprove rw.theory-list-atblp-of-range-of-clean-update
            (%autoinduct clean-update theoryname val theories))
(%autoprove rw.theory-list-env-okp-of-range-of-clean-update
            (%autoinduct clean-update theoryname val theories))


(%autoadmit tactic.find-theory)
(%autoprove rw.theoryp-of-tactic.find-theory
            (%enable default tactic.find-theory))
(%autoprove rw.theory-atblp-of-tactic.find-theory
            (%enable default tactic.find-theory))
(%autoprove rw.theory-env-okp-of-tactic.find-theory
            (%enable default tactic.find-theory))


(%autoadmit tactic.find-rule)
(%autoprove rw.rulep-of-tactic.find-rule
            (%enable default tactic.find-rule))
(%autoprove rw.rule-atblp-of-tactic.find-rule
            (%enable default tactic.find-rule))
(%autoprove rw.rule-env-okp-of-tactic.find-rule
            (%enable default tactic.find-rule))


(%autoadmit tactic.create-theory)
(%autoprove tactic.worldp-of-tactic.create-theory
            (%enable default tactic.create-theory))
(%autoprove tactic.worldp-atblp-of-tactic.create-theory
            ;; BOZO misnamed
            (%enable default tactic.create-theory))
(%autoprove tactic.world-env-okp-of-tactic.create-theory
            (%enable default tactic.create-theory))
(%autoprove tactic.world->index-of-tactic.create-theory
            (%enable default tactic.create-theory))


(%autoadmit tactic.create-theory-okp)
(%autoprove booleanp-of-tactic.create-theory-okp
            (%enable default tactic.create-theory-okp))
(%autoprove tactic.skeleton->goals-when-tactic.create-theory-okp
            (%enable default tactic.create-theory-okp))


(%autoadmit tactic.create-theory-tac)
(%autoprove tactic.skeletonp-of-tactic.create-theory-tac
            (%enable default tactic.create-theory-tac))
(%autoprove tactic.create-theory-okp-of-tactic.create-theory-tac
            (%enable default
                     tactic.create-theory-tac
                     tactic.create-theory-okp))


(%autoadmit tactic.create-theory-compile-world)
(%autoprove tactic.worldp-of-tactic.create-theory-compile-world
            (%enable default
                     tactic.create-theory-compile-world
                     tactic.create-theory-okp))
(%autoprove tactic.world-atblp-of-tactic.create-theory-compile-world
   (%enable default
            tactic.create-theory-compile-world
            tactic.create-theory-okp))
(%autoprove tactic.world-env-okp-of-tactic.create-theory-compile-world
            (%enable default
                     tactic.create-theory-compile-world
                     tactic.create-theory-okp))


(%autoadmit tactic.collect-rules)
(%autoprove true-listp-of-tactic.collect-rules
            (%autoinduct tactic.collect-rules x world acc)
            (%restrict default tactic.collect-rules (equal x 'x)))
(%autoprove rw.rule-listp-of-tactic.collect-rules
            (%autoinduct tactic.collect-rules x world acc)
            (%restrict default tactic.collect-rules (equal x 'x)))
(%autoprove rw.rule-list-atblp-of-tactic.collect-rules
            (%autoinduct tactic.collect-rules x world acc)
            (%restrict default tactic.collect-rules (equal x 'x)))
(%autoprove rw.rule-list-env-okp-of-tactic.collect-rules
            (%autoinduct tactic.collect-rules x world acc)
            (%restrict default tactic.collect-rules (equal x 'x)))


(%autoadmit tactic.e/d)
(%autoprove tactic.worldp-of-tactic.e/d
            (%enable default tactic.e/d))
(%autoprove tactic.worldp-atblp-of-tactic.e/d
            ;; BOZO misnamed
            (%enable default tactic.e/d))
(%autoprove tactic.world-env-okp-of-tactic.e/d
            (%enable default tactic.e/d))
(%autoprove tactic.world->index-of-tactic.e/d
            (%enable default tactic.e/d))


(%autoadmit tactic.e/d-okp)
(%autoprove booleanp-of-tactic.e/d-okp
            (%enable default tactic.e/d-okp))
(%autoprove tactic.skeleton->goals-when-tactic.e/d-okp
            (%enable default tactic.e/d-okp))


(%autoadmit tactic.e/d-tac)
(%autoprove tactic.skeletonp-of-tactic.e/d-tac
            (%enable default tactic.e/d-tac))
(%autoprove tactic.e/d-okp-of-tactic.e/d-tac
            (%enable default tactic.e/d-tac tactic.e/d-okp))


(%autoadmit tactic.e/d-compile-world)
(%autoprove tactic.worldp-of-tactic.e/d-compile-world
            (%enable default tactic.e/d-compile-world tactic.e/d-okp))
(%autoprove tactic.world-atblp-of-tactic.e/d-compile-world
            (%enable default tactic.e/d-compile-world tactic.e/d-okp))
(%autoprove tactic.world-env-okp-of-tactic.e/d-compile-world
            (%enable default tactic.e/d-compile-world tactic.e/d-okp))


(%autoadmit tactic.restrict)
(%autoprove tactic.worldp-of-tactic.restrict
            (%enable default tactic.restrict))
(%autoprove tactic.worldp-atblp-of-tactic.restrict
            ;; BOZO misnamed
            (%enable default tactic.restrict))
(%autoprove lemma-for-tactic.world-env-okp-of-tactic.restrict
            (%enable default rw.rule-env-okp rw.rule-clause))
(%autoprove tactic.world-env-okp-of-tactic.restrict
            (%enable default tactic.restrict))
(%autoprove tactic.world->index-of-tactic.restrict
            (%enable default tactic.restrict))


(%autoadmit tactic.restrict-okp)
(%autoprove booleanp-of-tactic.restrict-okp
            (%enable default tactic.restrict-okp))
(%autoprove tactic.skeleton->goals-when-tactic.restrict-okp
            (%enable default tactic.restrict-okp))


(%autoadmit tactic.restrict-tac)
(%autoprove tactic.skeletonp-of-tactic.restrict-tac
            (%enable default tactic.restrict-tac))
(%autoprove tactic.restrict-okp-of-tactic.restrict-tac
            (%enable default tactic.restrict-tac tactic.restrict-okp))


(%autoadmit tactic.restrict-compile-world)
(%autoprove tactic.worldp-of-tactic.restrict-compile-world
            (%enable default tactic.restrict-compile-world tactic.restrict-okp))
(%autoprove tactic.world-atblp-of-tactic.restrict-compile-world
            (%enable default tactic.restrict-compile-world tactic.restrict-okp))
(%autoprove tactic.world-env-okp-of-tactic.restrict-compile-world
            (%enable default tactic.restrict-compile-world tactic.restrict-okp))


(%autoadmit tactic.update-noexec)
(%autoprove tactic.worldp-of-tactic.update-noexec
            (%enable default tactic.update-noexec))
(%autoprove tactic.worldp-atblp-of-tactic.update-noexec
            ;; BOZO misnamed
            (%enable default tactic.update-noexec))
(%autoprove tactic.world-env-okp-of-tactic.update-noexec
            (%enable default tactic.update-noexec))
(%autoprove tactic.world->index-of-tactic.update-noexec
            (%enable default tactic.update-noexec))


(%autoadmit tactic.update-noexec-okp)
(%autoprove booleanp-of-tactic.update-noexec-okp
            (%enable default tactic.update-noexec-okp))
(%autoprove tactic.skeleton->goals-when-tactic.update-noexec-okp
            (%enable default tactic.update-noexec-okp))


(%autoadmit tactic.update-noexec-tac)
(%autoprove tactic.skeletonp-of-tactic.update-noexec-tac
            (%enable default tactic.update-noexec-tac))
(%autoprove tactic.update-noexec-okp-of-tactic.update-noexec-tac
            (%enable default tactic.update-noexec-tac tactic.update-noexec-okp))


(%autoadmit tactic.update-noexec-compile-world)
(%autoprove tactic.worldp-of-tactic.update-noexec-compile-world
            (%enable default
                     tactic.update-noexec-compile-world
                     tactic.update-noexec-okp))
(%autoprove tactic.world-atblp-of-tactic.update-noexec-compile-world
            (%enable default
                     tactic.update-noexec-compile-world
                     tactic.update-noexec-okp))
(%autoprove tactic.world-env-okp-of-tactic.update-noexec-compile-world
            (%enable default
                     tactic.update-noexec-compile-world
                     tactic.update-noexec-okp))


(%autoadmit tactic.cheapen-each-hyp)
(%autoprove rw.hyp-list-terms-of-tactic.cheapen-each-hyp
            (%autoinduct tactic.cheapen-each-hyp)
            (%restrict default tactic.cheapen-each-hyp (equal hyps 'hyps)))
(%autoprove forcing-rw.hyp-listp-of-tactic.cheapen-each-hyp
            (%autoinduct tactic.cheapen-each-hyp)
            (%restrict default tactic.cheapen-each-hyp (equal hyps 'hyps)))
(%autoprove forcing-rw.hyp-list-atblp-of-tactic.cheapen-each-hyp
            (%autoinduct tactic.cheapen-each-hyp)
            (%restrict default tactic.cheapen-each-hyp (equal hyps 'hyps)))


(%autoadmit tactic.cheapen-rule)
(%autoprove rw.rulep-of-tactic.cheapen-rule
            (%enable default tactic.cheapen-rule))
(%autoprove rw.rule-atblp-of-tactic.cheapen-rule
            (%enable default tactic.cheapen-rule))
(%autoprove rw.rule-env-okp-of-tactic.cheapen-rule
            (%enable default tactic.cheapen-rule rw.rule-env-okp rw.rule-clause))


(%autoadmit tactic.cheapen-rules)
(%autoprove rw.rule-listp-of-tactic.cheapen-rules
            (%autoinduct tactic.cheapen-rules)
            (%restrict default tactic.cheapen-rules (equal rules 'rules)))
(%autoprove rw.rule-list-atblp-of-tactic.cheapen-rules
            (%autoinduct tactic.cheapen-rules)
            (%restrict default tactic.cheapen-rules (equal rules 'rules)))
(%autoprove rw.rule-list-env-okp-of-tactic.cheapen-rules
            (%autoinduct tactic.cheapen-rules)
            (%restrict default tactic.cheapen-rules (equal rules 'rules)))


(%autoadmit tactic.cheapen)
(%autoprove tactic.worldp-of-tactic.cheapen
            (%enable default tactic.cheapen))
(%autoprove tactic.worldp-atblp-of-tactic.cheapen
            ;; BOZO misnamed
            (%enable default tactic.cheapen))
(%autoprove tactic.world-env-okp-of-tactic.cheapen
            (%enable default tactic.cheapen))
(%autoprove tactic.world->index-of-tactic.cheapen
            (%enable default tactic.cheapen))


(%autoadmit tactic.cheapen-okp)
(%autoprove booleanp-of-tactic.cheapen-okp
            (%enable default tactic.cheapen-okp))
(%autoprove tactic.skeleton->goals-when-tactic.cheapen-okp
            (%enable default tactic.cheapen-okp))


(%autoadmit tactic.cheapen-tac)
(%autoprove tactic.skeletonp-of-tactic.cheapen-tac
            (%enable default tactic.cheapen-tac))
(%autoprove tactic.cheapen-okp-of-tactic.cheapen-tac
            (%enable default tactic.cheapen-tac tactic.cheapen-okp))


(%autoadmit tactic.cheapen-compile-world)
(%autoprove tactic.worldp-of-tactic.cheapen-compile-world
            (%enable default tactic.cheapen-compile-world tactic.cheapen-okp))
(%autoprove tactic.world-atblp-of-tactic.cheapen-compile-world
            (%enable default tactic.cheapen-compile-world tactic.cheapen-okp))
(%autoprove tactic.world-env-okp-of-tactic.cheapen-compile-world
            (%enable default tactic.cheapen-compile-world tactic.cheapen-okp))


(%ensure-exactly-these-rules-are-missing "../../tactics/theory-change")