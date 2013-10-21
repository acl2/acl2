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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(%autoadmit clause.casesplit)

(%autoprove clause.casesplit-when-not-consp
            (%restrict default clause.casesplit (equal cases 'cases)))

(%autoprove clause.casesplit-of-cons
            (%restrict default clause.casesplit (equal cases '(cons a cases))))

(defmacro %clause.cases-induction (cases assignment)
  `(%induct (rank ,cases)
            ((not (consp ,cases))
             nil)
            ((consp ,cases)
             (((,cases (cdr ,cases)) (,assignment (update (car ,cases) t ,assignment)))
              ((,cases (cdr ,cases)) (,assignment (update (car ,cases) nil ,assignment)))))))

(%autoprove forcing-logic.termp-of-clause.casesplit
            (%clause.cases-induction cases assignment))

(%autoprove forcing-logic.term-atblp-of-clause.casesplit
            (%clause.cases-induction cases assignment))



(%autoadmit clause.cases)

(%autoprove clause.cases-when-not-consp
            (%restrict default clause.cases (equal cases 'cases)))

(%autoprove clause.cases-of-cons
            (%restrict default clause.cases (equal cases '(cons a cases))))

(%autoprove consp-of-clause.cases
            (%clause.cases-induction cases assignment))

(%autoprove domain-of-clause.cases
            (%clause.cases-induction cases baseassign))

(%autoprove clause.simple-term-listp-of-domain-of-clause.cases)

(%autoprove disjoint-from-nonep-of-domain-of-clause.cases)


(%ensure-exactly-these-rules-are-missing "../../clauses/if-lifting/casesplit")