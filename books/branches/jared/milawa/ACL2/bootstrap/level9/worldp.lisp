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
(include-book "gather")
(%interactive)

(%autoprove rw.theory-env-okp-of-lookup-when-rw.theory-list-env-okp-of-range
            (%cdr-induction theories))


(%defaggregate tactic.world
  (index
   forcingp
   betamode
   liftlimit
   splitlimit
   blimit
   rlimit
   rwn
   urwn
   noexec
   theories
   defs
   depth
   allrules
   assm-primaryp
   assm-secondaryp
   assm-directp
   assm-negativep
   )
  :require
  ((natp-of-tactic.world->index                         (natp index))
   (booleanp-of-tactic.world->forcingp                  (booleanp forcingp))
   (symbolp-of-tactic.world->betamode                   (symbolp betamode))
   (natp-of-tactic.world->liftlimit                     (natp liftlimit))
   (natp-of-tactic.world->splitlimit                    (natp splitlimit))
   (natp-of-tactic.world->blimit                        (natp blimit))
   (natp-of-tactic.world->rlimit                        (natp rlimit))
   (natp-of-tactic.world->rwn                           (natp rwn))
   (natp-of-tactic.world->urwn                          (natp urwn))
   (definition-listp-of-tactic.world->defs              (definition-listp defs))
   (natp-of-tactic.world->depth                         (natp depth))
   (rw.theory-mapp-of-tactic.world->theories            (rw.theory-mapp theories))
   (logic.function-symbol-listp-of-tactic.world->noexec (logic.function-symbol-listp noexec))
   (rw.rule-listp-of-tactic.world->allrules             (rw.rule-listp allrules))
   (booleanp-of-tactic.world->assm-primaryp             (booleanp assm-primaryp))
   (booleanp-of-tactic.world->assm-secondaryp           (booleanp assm-secondaryp))
   (booleanp-of-tactic.world->assm-directp              (booleanp assm-directp))
   (booleanp-of-tactic.world->assm-negativep            (booleanp assm-negativep))
   ))

(%deflist tactic.world-listp (x)
          (tactic.worldp x))

(%autoadmit tactic.world-atblp)

(%autoprove booleanp-of-tactic.world-atblp
            (%enable default tactic.world-atblp))

(%autoprove tactic.world-atblp-of-nil
            (%enable default tactic.world-atblp))

(%autoprove lemma-for-rw.theory-atblp-of-looked-up-theory
            (%cdr-induction theories))

(%autoprove rw.theory-atblp-of-looked-up-theory
            (%enable default
                     tactic.world-atblp
                     lemma-for-rw.theory-atblp-of-looked-up-theory))

(%autoprove tactic.world-atblp-of-tactic.world
            (%enable default tactic.world-atblp))

(%autoprove rw.theory-list-atblp-of-range-of-tactic.world->theories
            (%enable default tactic.world-atblp))

(%autoprove logic.formula-list-atblp-of-tactic.world->defs
            (%enable default tactic.world-atblp))

(%autoprove rw.rule-list-atblp-of-tactic.world->allrules
            (%enable default tactic.world-atblp))

(%deflist tactic.world-list-atblp (x atbl)
          (tactic.world-atblp x atbl))



(%autoadmit tactic.world-env-okp)

(%autoprove booleanp-of-tactic.world-env-okp
            (%enable default tactic.world-env-okp))

(%autoprove tactic.world-env-okp-of-nil
            (%enable default tactic.world-env-okp))

(%autoprove lemma-for-rw.theory-env-okp-of-looked-up-theory
            (%cdr-induction theories))

(%autoprove rw.theory-env-okp-of-looked-up-theory
            (%enable default
                     tactic.world-env-okp
                     lemma-for-rw.theory-env-okp-of-looked-up-theory))

(%autoprove tactic.world-env-okp-of-tactic.world
            (%enable default tactic.world-env-okp))

(%autoprove rw.theory-list-env-okp-of-range-of-tactic.world->theories
            (%enable default tactic.world-env-okp))

(%autoprove subsetp-of-tactic.world->defs-and-axioms
            (%enable default tactic.world-env-okp))

(%autoprove rw.rule-list-env-okp-of-tactic.world->allrules
            (%enable default tactic.world-env-okp))

(%deflist tactic.world-list-env-okp (x axioms thms)
  (tactic.world-env-okp x axioms thms))


(%autoprove subsetp-of-tactic.world->defs-when-memberp
            (%cdr-induction worlds))

(%autoprove subsetp-of-tactic.world->defs-when-memberp-alt)

(%autoprove rw.theory-env-okp-when-memberp
            (%cdr-induction worlds))

(%autoprove rw.theory-env-okp-when-memberp-alt
            (%cdr-induction worlds))





(%autoadmit tactic.find-world)

(%autoprove tactic.worldp-of-tactic.find-world-under-iff
            (%autoinduct tactic.find-world)
            (%restrict default tactic.find-world (equal worlds 'worlds)))

(%autoprove tactic.world-atblp-of-tactic.find-world-under-iff
            (%autoinduct tactic.find-world)
            (%restrict default tactic.find-world (equal worlds 'worlds)))

(%autoprove tactic.world-env-okp-of-tactic.find-world-under-iff
            (%autoinduct tactic.find-world)
            (%restrict default tactic.find-world (equal worlds 'worlds)))

(%autoprove tactic.world->index-of-tactic.find-world
            (%autoinduct tactic.find-world)
            (%restrict default tactic.find-world (equal worlds 'worlds)))

(%autoprove subsetp-of-tactic.world->defs-of-tactic.find-world-and-axioms
            (%disable default subsetp-of-tactic.world->defs-and-axioms)
            (%use (%instance (%thm subsetp-of-tactic.world->defs-and-axioms)
                             (world (tactic.find-world index worlds)))))

(%autoprove rw.theory-list-env-okp-of-range-of-tactic.world->theories-of-find-world
            (%disable default rw.theory-list-env-okp-of-range-of-tactic.world->theories)
            (%use (%instance (%thm rw.theory-list-env-okp-of-range-of-tactic.world->theories)
                             (world (tactic.find-world world worlds)))))


(%autoadmit tactic.increment-world-index)

(%autoprove tactic.worldp-of-tactic.increment-world-index
            (%enable default tactic.increment-world-index))

(%autoprove tactic.world-atblp-of-tactic.increment-world-index
            (%enable default tactic.increment-world-index))

(%autoprove tactic.world-env-okp-of-tactic.increment-world-index
            (%enable default tactic.increment-world-index))

(%autoprove tactic.world->index-of-tactic.increment-world-index
            (%enable default tactic.increment-world-index))


(%ensure-exactly-these-rules-are-missing "../../tactics/worldp")
