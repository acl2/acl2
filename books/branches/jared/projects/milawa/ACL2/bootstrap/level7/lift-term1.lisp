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
(include-book "depth-3-special")
(%interactive)

(%autoadmit clause.lift-term1)


(defmacro %clause.lift-term1-induction (x)
  `(%induct (rank ,x)
            ((logic.constantp ,x)
             nil)
            ((logic.variablep ,x)
             nil)
            ((logic.functionp ,x)
             (((,x (first (logic.function-args ,x))))
              ((,x (second (logic.function-args ,x))))
              ((,x (third (logic.function-args ,x))))))
            ((logic.lambdap ,x)
             nil)
            ((and (not (logic.constantp ,x))
                  (not (logic.variablep ,x))
                  (not (logic.functionp ,x))
                  (not (logic.lambdap ,x)))
             nil)))


(local (%disable default
                 same-length-prefixes-equal-cheap
                 logic.termp-when-logic.formulap))

(%autoprove forcing-logic.termp-of-clause.lift-term1
            (%clause.lift-term1-induction x)
            (%restrict default clause.lift-term1 (equal x 'x))
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules))

(%autoprove forcing-logic.term-atblp-of-clause.lift-term1
            (%clause.lift-term1-induction x)
            (%restrict default clause.lift-term1 (equal x 'x))
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules))

(%autoprove clause.lift-term1-when-no-clause.unlifted-subterms
            (%clause.lift-term1-induction x)
            (%restrict default clause.lift-term1 (equal x 'x))
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules))



(%autoprove forcing-clause.depth-of-clause.factor-strong)

(local (%enable default forcing-clause.depth-of-clause.factor-strong))


(%autoprove lemma-for-clause.depth-decreases-in-lambda-case
            (%disable default clause.deepest-weakly-deeper-than-any-member)
            (%use (%instance (%thm clause.deepest-weakly-deeper-than-any-member)
                             (x (logic.lambda-actuals x))
                             (a (clause.deepest-after-factoring (logic.lambda-actuals x) assignment)))))

(%autoprove lemma2-for-clause.depth-decreases-in-lambda-case
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules
                      clause.simple-term-listp-of-domain-of-clause.cases
                      disjoint-from-nonep-of-domain-of-clause.cases
                      lemma-for-clause.depth-decreases-in-lambda-case)
            (%use (%instance (%thm lemma-for-clause.depth-decreases-in-lambda-case)
                             (assignment (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.lambda-actuals x)) nil)))))

            (%use (%instance (%thm clause.simple-term-listp-of-domain-of-clause.cases)
                             (x     (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.lambda-actuals x)) nil)))
                             (cases (clause.simple-tests-list (logic.lambda-actuals x)))
                             (assignment nil)))

            (%use (%instance (%thm disjoint-from-nonep-of-domain-of-clause.cases)
                             (x     (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.lambda-actuals x)) nil)))
                             (cases (clause.simple-tests-list (logic.lambda-actuals x)))
                             (set   (clause.term-paths-list (logic.lambda-actuals x)))
                             (assignment nil))))

(%autoprove clause.depth-decreases-in-lambda-case
            (%enable default
                     clause.depth-list-redefinition
                     lemma2-for-clause.depth-decreases-in-lambda-case)
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules))



(%autoprove lemma-for-clause.depth-decreases-in-logic.functionp-case
            (%disable default clause.deepest-weakly-deeper-than-any-member)
            (%use (%instance (%thm clause.deepest-weakly-deeper-than-any-member)
                             (x (logic.function-args x))
                             (a (clause.deepest-after-factoring (logic.function-args x) assignment)))))

(%autoprove lemma2-for-clause.depth-decreases-in-logic.functionp-case
            (%disable default
                      clause.simple-term-listp-of-domain-of-clause.cases
                      disjoint-from-nonep-of-domain-of-clause.cases
                      lemma-for-clause.depth-decreases-in-logic.functionp-case
                      type-set-like-rules
                      expensive-arithmetic-rules)
            (%use (%instance (%thm lemma-for-clause.depth-decreases-in-logic.functionp-case)
                             (assignment (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.function-args x)) nil)))))
            (%use (%instance (%thm clause.simple-term-listp-of-domain-of-clause.cases)
                             (x     (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.function-args x)) nil)))
                             (cases (clause.simple-tests-list (logic.function-args x)))
                             (assignment nil)))
            (%use (%instance (%thm disjoint-from-nonep-of-domain-of-clause.cases)
                             (x     (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.function-args x)) nil)))
                             (cases (clause.simple-tests-list (logic.function-args x)))
                             (set   (clause.term-paths-list (logic.function-args x)))
                             (assignment nil))))

(%autoprove clause.depth-decreases-in-non-if-logic.functionp-case
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules
                      clause.simple-termp-when-bad-args-logic.functionp
                      clause.unlifted-subterms-when-bad-args-logic.functionp)
            (%enable default
                     clause.depth-list-redefinition
                     lemma2-for-clause.depth-decreases-in-logic.functionp-case))

(%autoprove clause.depth-decreases-in-bad-args-logic.functionp-case
            (%enable default
                     clause.depth-list-redefinition
                     lemma2-for-clause.depth-decreases-in-logic.functionp-case))

(%autoprove clause.lift-term1-makes-progress
            (%clause.lift-term1-induction x)
            (%auto :strategy (cleanup split urewrite))
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules)
            (%crewrite default)
            (%auto :strategy (cleanup split urewrite))
            (%restrict default definition-of-clause.depth (equal x 'x))
            (%restrict default clause.lift-term1 (equal x 'x))
            (%enable default
                     clause.depth-decreases-in-bad-args-logic.functionp-case
                     clause.depth-decreases-in-non-if-logic.functionp-case
                     clause.depth-decreases-in-lambda-case)
            (%disable default
                      expensive-arithmetic-rules-two
                      clause.depth-list-when-length-three)
            (%crewrite default)
            (%auto :strategy (cleanup split urewrite))
            (%crewrite default)
            (%auto :strategy (cleanup split urewrite))
            (%enable default
                     clause.depth-list-when-length-three
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     type-set-like-rules))



