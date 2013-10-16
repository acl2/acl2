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
(include-book "worldp")
(include-book "fast-urewrite")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defsection tactic.world->control
  (%autoadmit tactic.world->control)
  (local (%enable default tactic.world->control))
  (%autoprove rw.controlp-of-tactic.world->control)
  (%autoprove rw.control-atblp-of-tactic.world->control)
  (%autoprove rw.control-env-okp-of-tactic.world->control))


(%autoadmit rw.world-urewrite)
(%enable default rw.world-urewrite)

(%autoadmit rw.world-urewrite-list)
(%autoadmit rw.world-urewrite-list-list)

(%autoprove rw.world-urewrite-list-redefinition
            (%cdr-induction x)
            (%restrict default rw.world-urewrite-list (equal x 'x)))

(%autoprove rw.world-urewrite-list-list-redefinition
            (%cdr-induction x)
            (%restrict default rw.world-urewrite-list-list (equal x 'x)))

(%autoadmit rw.fast-urewrite-list-list)

(%autoprove rw.fast-urewrite-list-list-removal
            (%cdr-induction x)
            (%restrict default rw.fast-urewrite-list-list (equal x 'x)))

(%autoadmit rw.fast-world-urewrite)
(%enable default rw.fast-world-urewrite)

(%autoadmit rw.fast-world-urewrite-list)

(%autoprove definition-of-rw.fast-world-urewrite-list
            (%cdr-induction x)
            (%restrict default rw.fast-world-urewrite-list (equal x 'x))
            (%restrict default definition-of-rw.fast-urewrite-list (equal x 'x))
            (%disable default tactic.world->control))

(%autoadmit rw.fast-world-urewrite-list-list)

(%autoprove definition-of-rw.fast-world-urewrite-list-list
            (%cdr-induction x)
            (%restrict default rw.fast-world-urewrite-list-list (equal x 'x))
            (%restrict default rw.fast-urewrite-list-list (equal x 'x))
            (%disable default tactic.world->control))


