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
(include-book "proofp")
(%interactive)

(%autoadmit logic.functional-axiom)

(%autoprove forcing-logic.formulap-of-logic.functional-axiom
            (%enable default logic.functional-axiom))

(%autoprove forcing-logic.formula-atblp-of-logic.functional-axiom
            (%enable default logic.functional-axiom))



(%autoadmit logic.functional-axiom-alt1)

(defmacro %logic.functional-axiom-alt1-induction (ti si tacc sacc)
  `(%induct (rank ,ti)
            ((or (not (consp ,ti))
                 (not (consp ,si)))
             nil)
            ((and (consp ,ti)
                  (consp ,si))
             (((,ti (cdr ,ti))
               (,si (cdr ,si))
               (,tacc (cons (car ,ti) ,tacc))
               (,sacc (cons (car ,si) ,sacc)))))))

(%autoprove logic.check-functional-axiom-of-logic.functional-axiom-alt1
            (%logic.functional-axiom-alt1-induction ti si tacc sacc)
            (%restrict default logic.functional-axiom-alt1 (equal ti 'ti))
            (%auto)
            (%restrict default logic.check-functional-axiom (equal ti 'tacc)))


(%autoadmit logic.functional-axiom-alt2)

(%autoprove logic.functional-axiom-alt1/alt2-equivalence
            ;; broken with the alternate rewriter strategy withotu assms
            ;; (%skip) reverting
            (%logic.functional-axiom-alt1-induction ti si tacc sacc)
            (%restrict default logic.functional-axiom-alt1 (equal ti 'ti))
            (%enable default logic.functional-axiom-alt2)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots
                      forcing-logic.formulap-of-logic.por
                      forcing-logic.formulap-of-logic.pequal
                      forcing-logic.formulap-of-logic.pnot
                      forcing-logic.formulap-of-logic.pequal-list
                      forcing-equal-of-logic.por-rewrite-two
                      forcing-equal-of-logic.por-rewrite
                      forcing-logic.fmtype-of-logic.disjoin-formulas
                      [outside]consp-of-logic.pequal-list ;; why ??
                      ))

(%autoprove logic.functional-axiom-alt2/main-equivalence
            (%disable default
                      forcing-logic.formulap-of-logic.pequal-list
                      logic.formula-listp-of-logic.negate-formulas
                      forcing-logic.termp-of-logic.function
                      forcing-equal-of-logic.pequal-list-rewrite
                      forcing-logic.formula-listp-of-app
                      forcing-logic.formulap-of-logic.pequal
                      equal-of-logic.pequal-list-and-logic.pequal-list
                      equal-of-logic.disjoin-formulas-and-logic.disjoin-formulas-when-same-len)
            (%enable default
                     logic.functional-axiom-alt2
                     logic.functional-axiom))

(%autoprove forcing-logic.check-functional-axiom-of-logic.functional-axiom
            (%use (%instance (%thm logic.check-functional-axiom-of-logic.functional-axiom-alt1)
                             (tacc nil)
                             (sacc nil))))

(%ensure-exactly-these-rules-are-missing "../../logic/functional-axiom")

