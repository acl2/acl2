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
(include-book "evaluator")
(%interactive)

(%autoadmit flag-generic-evaluator-bldr)
(%autoadmit generic-evaluator-bldr)
(%autoadmit generic-evaluator-list-bldr)

(%autoprove definition-of-generic-evaluator-bldr
            (%enable default generic-evaluator-bldr generic-evaluator-list-bldr)
            (%restrict default flag-generic-evaluator-bldr (equal x 'x)))

(%autoprove definition-of-generic-evaluator-list-bldr
            (%enable default generic-evaluator-bldr generic-evaluator-list-bldr)
            (%restrict default flag-generic-evaluator-bldr (equal x 'x)))

(%autoprove flag-generic-evaluator-bldr-of-term
            (%enable default generic-evaluator-bldr))

(%autoprove flag-generic-evaluator-bldr-of-list
            (%enable default generic-evaluator-list-bldr))

(%autoprove forcing-len-of-cdr-of-generic-evaluator-list-bldr
            (%cdr-induction x)
            (%restrict default definition-of-generic-evaluator-list-bldr (equal x 'x)))



(defthmd lemma-2-for-forcing-logic.appealp-of-generic-evaluator-bldr
  ;; BOZO called "crock" and local in the other file.
  (implies (submapp (logic.initial-arity-table) atbl)
           (equal (lookup 'if atbl)
                  '(if . 3)))
  :hints(("Goal"
          :in-theory (enable logic.initial-arity-table)
          :use ((:instance equal-of-lookups-when-submapp
                           (x (logic.initial-arity-table))
                           (y atbl)
                           (a 'if))))))

(%autoprove lemma-2-for-forcing-logic.appealp-of-generic-evaluator-bldr
            (%enable default logic.initial-arity-table)
            (%use (%instance (%thm equal-of-lookups-when-submapp)
                           (x (logic.initial-arity-table))
                           (y atbl)
                           (a 'if))))

(local (%enable default lemma-2-for-forcing-logic.appealp-of-generic-evaluator-bldr))





(encapsulate
 ()
 (local (%max-proof-size 1200000000))
 (%autoprove lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr
             ;; This is a particularly difficult proof because of the complexity
             ;; of the induction scheme and the number of cases involved when we
             ;; open up the functions.  Our approach is not very complicated --
             ;; we basically try to solve as much as we can "on the cheap" by
             ;; only using urewrite and very limited crewriting.  Only after the
             ;; big mess is made do we cheaply
             (%flag-generic-evaluator-induction flag x defs n)
             (%disable default
                       formula-decomposition
                       expensive-term/formula-inference
                       expensive-arithmetic-rules
                       expensive-arithmetic-rules-two
                       expensive-subsetp-rules
                       type-set-like-rules
                       forcing-logic.function-of-logic.function-name-and-logic.function-args
                       forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                       forcing-lookup-of-logic.function-name
                       same-length-prefixes-equal-cheap
                       definitionp-when-memberp-of-definition-listp
                       definition-list-lookup-when-not-consp)
             (%auto :strategy (split urewrite))
             (%forcingp nil)
             (%crewrite default)
             (%restrict default definition-of-generic-evaluator (equal x 'x))
             (%restrict default definition-of-generic-evaluator-bldr (equal x 'x))
             (%restrict default definition-of-generic-evaluator-list (equal x 'x))
             (%restrict default definition-of-generic-evaluator-list-bldr (equal x 'x))
             (%auto :strategy (split urewrite))
             (%crewrite default)
             (%forcingp t)
             (%enable default
                      formula-decomposition
                      expensive-term/formula-inference
                      type-set-like-rules)
             (%disable default
                       logic.termp-when-logic.formulap
                       logic.termp-when-invalid-maybe-expensive
                       logic.formulap-when-logic.termp
                       logic.formula-listp-when-definition-listp
                       consp-when-logic.lambdap-cheap
                       consp-when-logic.functionp-cheap
                       consp-of-car-when-none-consp
                       consp-of-car-when-cons-listp
                       logic.substitute-when-malformed-cheap
                       logic.lambdap-when-not-anything-else-maybe-expensive)
             (%cheapen default
                       logic.substitute-when-logic.constantp
                       logic.substitute-when-logic.variablep
                       logic.constantp-when-logic.variablep
                       logic.variablep-when-logic.constantp
                       logic.constantp-when-logic.functionp)
             (%auto :strategy (split cleanup urewrite crewrite elim))))

(%autoprove forcing-logic.appealp-of-generic-evaluator-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr)
                             (flag 'term))))

(%autoprove forcing-logic.conclusion-of-generic-evaluator-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr)
                             (flag 'term))))

(%autoprove forcing-consp-of-generic-evaluator-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr)
                             (flag 'list))))

(%autoprove forcing-logic.appeal-listp-of-generic-evaluator-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr)
                             (flag 'list))))

(%autoprove forcing-logic.strip-conclusions-of-generic-evaluator-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr)
                             (flag 'list))))

(%autoprove forcing-generic-evaluator-bldr-under-iff
            (%disable default forcing-logic.appealp-of-generic-evaluator-bldr)
            (%use (%instance (%thm forcing-logic.appealp-of-generic-evaluator-bldr))))

(%autoprove forcing-generic-evaluator-list-bldr-under-iff
            (%disable default forcing-consp-of-generic-evaluator-list-bldr)
            (%use (%instance (%thm forcing-consp-of-generic-evaluator-list-bldr))))


