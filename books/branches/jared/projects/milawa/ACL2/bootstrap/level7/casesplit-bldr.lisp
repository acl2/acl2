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
(include-book "casesplit")
(%interactive)


(%autoprove cdr-of-logic.smart-negate-formulas)

(%autoprove car-of-logic.smart-negate-formulas
            (%forcingp nil))

(%autoadmit clause.cases-bldr)


(defthm lemma-for-forcing-logic.appealp-of-clause.cases-bldr-alt
  ;; BOZO the real lemma needs :rule-classes nil added
  (implies (and (logic.termp a)
                (logic.term-listp cases)
                (logic.term-listp (domain assignment)))
           (and (logic.appealp (clause.cases-bldr a cases assignment))
                (equal (logic.conclusion (clause.cases-bldr a cases assignment))
                       (if (consp assignment)
                           (logic.por (logic.disjoin-formulas (logic.smart-negate-formulas (assignment-formulas assignment)))
                                      (logic.pequal a (clause.casesplit a cases assignment)))
                         (logic.pequal a (clause.casesplit a cases assignment))))))
  :rule-classes nil)


(%autoprove lemma-for-forcing-logic.appealp-of-clause.cases-bldr-alt
            (%clause.cases-induction cases assignment)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      expensive-term/formula-inference
                      type-set-like-rules
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free)
            (%auto :strategy (cleanup split))
            (%restrict default clause.cases-bldr (equal cases 'cases))
            (%restrict default clause.casesplit (equal cases 'cases)))

(%autoprove forcing-logic.appealp-of-clause.cases-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.cases-bldr-alt))))

(%autoprove forcing-logic.conclusion-of-clause.cases-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.cases-bldr-alt))))



(%autoprove forcing-proofp-of-clause.cases-bldr
            (%clause.cases-induction cases assignment)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      expensive-term/formula-inference
                      type-set-like-rules
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free)
            (%auto :strategy (cleanup split))
            (%restrict default clause.cases-bldr (equal cases 'cases))
            (%restrict default clause.casesplit (equal cases 'cases)))
