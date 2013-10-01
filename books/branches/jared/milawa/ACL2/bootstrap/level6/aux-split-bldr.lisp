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
(include-book "aux-split-double-negate")
(include-book "aux-split-negated-if")
(include-book "aux-split-positive-if")
(include-book "aux-split-negative-default")
(include-book "aux-split-positive-default")
(%interactive)


(local (%disable default
                 type-set-like-rules
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 expensive-term/formula-inference
                 expensive-subsetp-rules
                 unusual-consp-rules))

(%autoadmit clause.aux-split-bldr)

(%autoprove lemma-for-forcing-logic.appealp-of-clause.aux-split-bldr
            (%autoinduct clause.aux-split)
            (%enable default clause.aux-split-goal-when-not-consp-of-todo)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default clause.aux-split-bldr (equal todo 'todo))
            (%restrict default clause.aux-split (equal todo 'todo))
            (%restrict default clause.split-count-list (equal x 'todo))
            (%auto :strategy (cleanup split urewrite crewrite)))

(%autoprove forcing-logic.appealp-of-clause.aux-split-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.aux-split-bldr))))

(%autoprove lemma-for-forcing-logic.proofp-of-clause.aux-split-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.aux-split-bldr))))

(local (%max-proof-size 800000000))

(%autoprove forcing-logic.proofp-of-clause.aux-split-bldr
            (%autoinduct clause.aux-split)
            (%enable default
                     clause.aux-split-goal-when-not-consp-of-todo
                     lemma-for-forcing-logic.proofp-of-clause.aux-split-bldr)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default clause.split-count-list (equal x 'todo))
            (%restrict default clause.aux-split-bldr (equal todo 'todo))
            (%restrict default clause.aux-split (equal todo 'todo))
            (%auto :strategy (cleanup split urewrite crewrite)))

(%autoprove forcing-logic.conclusion-of-clause.aux-split-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-clause.aux-split-bldr)))
            (%enable default clause.aux-split-goal))


