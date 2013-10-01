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
(include-book "absurd")
(include-book "normalize-nots")
(%interactive)


(%autoadmit disabled-equal)
(%autoadmit clause.clean-clauses)

(defsection clause.clean-clauses
  (local (%enable default clause.clean-clauses disabled-equal))
  (%autoprove booleanp-of-first-of-clause.clean-clauses)
  (%autoprove booleanp-of-second-of-clause.clean-clauses)
  (%autoprove logic.term-list-listp-of-third-of-clause.clean-clauses)
  (%autoprove logic.cons-listp-of-third-of-clause.clean-clauses)
  (%autoprove true-listp-of-third-of-clause.clean-clauses))

(%autoadmit clause.clean-clauses-bldr)

(%autoprove forcing-logic.appeal-listp-of-clause.clean-clauses-bldr
            (%enable default clause.clean-clauses-bldr clause.clean-clauses disabled-equal)
            (%disable default consp-when-memberp-of-cons-listp))

(%autoprove forcing-logic.strip-conclusions-of-clause.clean-clauses-bldr
            (%enable default clause.clean-clauses-bldr clause.clean-clauses disabled-equal)
            (%disable default consp-when-memberp-of-cons-listp))

(%autoprove forcing-logic.proof-listp-of-clause.clean-clauses-bldr
            (%enable default clause.clean-clauses-bldr clause.clean-clauses disabled-equal)
            (%disable default consp-when-memberp-of-cons-listp))



(%autoadmit clause.fast-clean-part1)

(%autoprove clause.fast-clean-part1-removal
            (%autoinduct clause.fast-clean-part1 x acc)
            (%restrict default clause.fast-clean-part1 (equal x 'x))
            (%enable default
                     clause.normalize-nots-term-list-of-rev
                     [outside]clause.normalize-nots-term-list-of-rev)
            (%disable default
                      rev-of-clause.normalize-nots-term-list
                      [outside]rev-of-clause.normalize-nots-term-list))


(%autoadmit clause.fast-clean-clauses)

(%autoprove clause.fast-clean-clauses-removal
            (%enable default
                     clause.fast-clean-clauses
                     clause.clean-clauses)
            (%enable default
                     clause.normalize-nots-clauses-of-rev
                     clause.remove-obvious-clauses-of-rev
                     clause.remove-complement-clauses-of-rev)
            (%disable default
                      rev-of-clause.normalize-nots-clauses
                      rev-of-clause.remove-obvious-clauses
                      rev-of-clause.remove-complement-clauses
                      [outside]rev-of-clause.normalize-nots-clauses
                      [outside]rev-of-clause.remove-obvious-clauses
                      [outside]rev-of-clause.remove-complement-clauses)
            (%disable default consp-when-memberp-of-cons-listp) ;; wtf?
            )



