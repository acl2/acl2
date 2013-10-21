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
(%interactive)


(%autoadmit clause.flag-term-tests)
(%autoadmit clause.term-tests)
(%autoadmit clause.term-tests-list)
(%autoadmit clause.slow-term-tests)

(defmacro %clause.flag-term-tests-induction (flag x acc)
  `(%induct (rank ,x)
            ((and (equal ,flag 'term)
                  (logic.constantp ,x))
             nil)
            ((and (equal ,flag 'term)
                  (logic.variablep ,x))
             nil)
            ((and (equal ,flag 'term)
                  (logic.functionp ,x)
                  (equal (logic.function-name ,x) 'if)
                  (equal (len (logic.function-args ,x)) 3))
             (((,flag 'term)
               (,x (first (logic.function-args ,x)))
               (,acc (clause.flag-term-tests 'term
                                             (second (logic.function-args ,x))
                                             (clause.flag-term-tests 'term
                                                                     (third (logic.function-args ,x))
                                                                     ,acc))))
              ((,flag 'term)
               (,x (second (logic.function-args ,x)))
               (,acc (clause.flag-term-tests 'term
                                             (third (logic.function-args ,x))
                                             ,acc)))
              ((,flag 'term)
               (,x (third (logic.function-args ,x)))
               (,acc ,acc))))
            ((and (equal ,flag 'term)
                  (logic.functionp ,x)
                  (or (not (equal (logic.function-name ,x) 'if))
                      (not (equal (len (logic.function-args ,x)) 3))))
             (((,flag 'list)
               (,x (logic.function-args ,x))
               (,acc ,acc))))
            ((and (equal ,flag 'term)
                  (logic.lambdap ,x))
             (((,flag 'list)
               (,x (logic.lambda-actuals ,x))
               (,acc ,acc))))
            ((and (equal ,flag 'term)
                  (not (logic.constantp ,x))
                  (not (logic.variablep ,x))
                  (not (logic.functionp ,x))
                  (not (logic.lambdap ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (consp ,x))
             (((,flag 'term)
               (,x (car ,x))
               (,acc (clause.flag-term-tests 'list (cdr ,x) ,acc)))
              ((,flag 'list)
               (,x (cdr ,x))
               (,acc ,acc))))))

(encapsulate
 ()
 (%autoprove lemma-1-for-definition-of-clause.term-tests
             (%logic.term-induction flag x)
             (%restrict default clause.slow-term-tests (equal x 'x)))

 (%autoprove lemma-2-for-definition-of-clause.term-tests
             (%clause.flag-term-tests-induction flag x acc)
             (%restrict default clause.flag-term-tests (equal x 'x)))

 (local (%enable default
                 lemma-1-for-definition-of-clause.term-tests
                 [outside]lemma-1-for-definition-of-clause.term-tests
                 lemma-2-for-definition-of-clause.term-tests
                 [outside]lemma-2-for-definition-of-clause.term-tests))

 (%autoprove lemma-3-for-definition-of-clause.term-tests
             (%clause.flag-term-tests-induction flag x acc)
             (%restrict default clause.flag-term-tests (equal x 'x))
             (%restrict default clause.slow-term-tests (equal x 'x)))

 (local (%enable default
                 lemma-3-for-definition-of-clause.term-tests))

 (%autoprove definition-of-clause.term-tests
             (%enable default clause.term-tests clause.term-tests-list)
             (%restrict default clause.flag-term-tests (equal x 'x))
             (%restrict default clause.slow-term-tests (equal x 'x)))

 (%autoprove definition-of-clause.term-tests-list
             (%enable default clause.term-tests clause.term-tests-list)
             (%restrict default clause.flag-term-tests (equal x 'x))
             (%restrict default clause.slow-term-tests (equal x 'x)))

 (%autoprove clause.flag-term-tests-removal
             (%enable default clause.term-tests)
             (%restrict default clause.slow-term-tests (equal x 'x)))

 (%autoprove clause.flag-term-tests-list-removal
             (%enable default clause.term-tests-list)
             (%restrict default clause.slow-term-tests (equal x 'x))))



(%autoprove clause.term-tests-when-logic.constantp
            (%restrict default definition-of-clause.term-tests (equal x 'x)))

(%autoprove clause.term-tests-when-logic.variablep
            (%restrict default definition-of-clause.term-tests (equal x 'x)))

(%autoprove clause.term-tests-when-non-if-logic.functionp
            (%restrict default definition-of-clause.term-tests (equal x 'x)))

(%autoprove clause.term-tests-when-bad-args-logic.functionp
            (%restrict default definition-of-clause.term-tests (equal x 'x)))

(%autoprove clause.term-tests-when-if-logic.functionp
            (%restrict default definition-of-clause.term-tests (equal x 'x)))

(%autoprove clause.term-tests-when-logic.lambdap
            (%restrict default definition-of-clause.term-tests (equal x 'x)))

(%autoprove clause.term-tests-when-degenerate
            (%restrict default definition-of-clause.term-tests (equal x 'x)))



(%autoprove clause.term-tests-list-when-not-consp
            (%restrict default definition-of-clause.term-tests-list (equal x 'x)))

(%autoprove clause.term-tests-list-of-cons
            (%restrict default definition-of-clause.term-tests-list (equal x '(cons a x))))

(%autoprove clause.term-tests-list-when-len-three)



(%autoprove lemma-for-clause.term-tests-when-clause.simple-termp
            (%clause.simple-term-induction flag x))

(%autoprove clause.term-tests-when-clause.simple-termp
            (%use (%instance (%thm lemma-for-clause.term-tests-when-clause.simple-termp)
                             (flag 'term))))

(%autoprove clause.term-tests-list-when-clause.simple-term-listp
            (%use (%instance (%thm lemma-for-clause.term-tests-when-clause.simple-termp)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.term-listp-of-clause.term-tests
            (%clause.simple-term-induction flag x)
            (%disable default
                      expensive-arithmetic-rules
                      unusual-subsetp-rules
                      type-set-like-rules
                      formula-decomposition
                      expensive-term/formula-inference
                      logic.term-listp-of-subsetp-when-logic.term-listp
                      logic.termp-when-memberp-of-logic.term-listp))

(%autoprove forcing-logic.term-listp-of-clause.term-tests
            (%use (%instance (%thm lemma-for-forcing-logic.term-listp-of-clause.term-tests)
                             (flag 'term))))

(%autoprove forcing-logic.term-listp-of-clause.term-tests-list
            (%use (%instance (%thm lemma-for-forcing-logic.term-listp-of-clause.term-tests)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.term-list-atblp-of-clause.term-tests
            (%clause.simple-term-induction flag x)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      formula-decomposition
                      expensive-term/formula-inference
                      unusual-subsetp-rules
                      same-length-prefixes-equal-cheap
                      logic.term-list-atblp-of-subsetp-when-logic.term-list-atblp
                      logic.term-atblp-when-memberp-of-logic.term-list-atblp
                      logic.term-list-atblp-when-logic.variable-listp
                      logic.term-list-atblp-when-not-consp
                      clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                      logic.term-list-atblp-when-logic.constant-listp))

(%autoprove forcing-logic.term-list-atblp-of-clause.term-tests
            (%use (%instance (%thm lemma-for-forcing-logic.term-list-atblp-of-clause.term-tests)
                             (flag 'term))))

(%autoprove forcing-logic.term-list-atblp-of-clause.term-tests-list
            (%use (%instance (%thm lemma-for-forcing-logic.term-list-atblp-of-clause.term-tests)
                             (flag 'list))))






(%autoadmit clause.flag-simple-tests)
(%autoadmit clause.simple-tests)
(%autoadmit clause.simple-tests-list)
(%autoadmit clause.slow-simple-tests)

(defmacro %clause.flag-simple-tests-induction (flag x acc)
  `(%induct (rank ,x)
            ((and (equal ,flag 'term)
                  (logic.constantp ,x))
             nil)
            ((and (equal ,flag 'term)
                  (logic.variablep ,x))
             nil)
            ((and (equal ,flag 'term)
                  (logic.functionp ,x)
                  (equal (logic.function-name ,x) 'if)
                  (equal (len (logic.function-args ,x)) 3)
                  (clause.simple-termp (first (logic.function-args ,x))))
             (((,flag 'term)
               (,x    (second (logic.function-args ,x)))
               (,acc  (clause.flag-simple-tests 'term (third (logic.function-args ,x)) ,acc)))
              ((,flag 'term)
               (,x    (third (logic.function-args ,x)))
               (,acc ,acc))))
            ((and (equal ,flag 'term)
                  (logic.functionp ,x)
                  (or (not (equal (logic.function-name ,x) 'if))
                      (not (equal (len (logic.function-args ,x)) 3))
                      (not (clause.simple-termp (first (logic.function-args ,x))))))
             (((,flag 'list)
               (,x (logic.function-args ,x))
               (,acc ,acc))))
            ((and (equal ,flag 'term)
                  (logic.lambdap ,x))
             (((,flag 'list)
               (,x (logic.lambda-actuals ,x))
               (,acc ,acc))))
            ((and (equal ,flag 'term)
                  (not (logic.constantp ,x))
                  (not (logic.variablep ,x))
                  (not (logic.functionp ,x))
                  (not (logic.lambdap ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (consp ,x))
             (((,flag 'term)
               (,x (car ,x))
               (,acc (clause.flag-simple-tests 'list (cdr ,x) ,acc)))
              ((,flag 'list)
               (,x (cdr ,x))
               (,acc ,acc))))))

(encapsulate
 ()
 (%autoprove lemma-1-for-definition-of-clause.simple-tests
             (%logic.term-induction flag x)
             (%restrict default clause.slow-simple-tests (equal x 'x)))

 (%autoprove lemma-2-for-definition-of-clause.simple-tests
             (%clause.flag-simple-tests-induction flag x acc)
             (%restrict default clause.flag-simple-tests (equal x 'x)))

 (local (%enable default
                 lemma-1-for-definition-of-clause.simple-tests
                 lemma-2-for-definition-of-clause.simple-tests))

 (%autoprove lemma-3-for-definition-of-clause.simple-tests
             (%clause.flag-simple-tests-induction flag x acc)
             (%restrict default clause.flag-simple-tests (equal x 'x))
             (%restrict default clause.slow-simple-tests (equal x 'x)))

 (local (%enable default lemma-3-for-definition-of-clause.simple-tests))

 (%autoprove definition-of-clause.simple-tests
             (%enable default clause.simple-tests clause.simple-tests-list)
             (%restrict default clause.slow-simple-tests (equal x 'x))
             (%forcingp nil))

 (%autoprove definition-of-clause.simple-tests-list
             (%enable default clause.simple-tests clause.simple-tests-list)
             (%restrict default clause.slow-simple-tests (equal x 'x)))

 (%autoprove clause.flag-simple-tests-removal
             (%enable default clause.simple-tests clause.simple-tests-list)
             (%restrict default clause.slow-simple-tests (equal x 'x))
             (%forcingp nil))

 (%autoprove clause.flag-simple-tests-list-removal
             (%enable default clause.simple-tests clause.simple-tests-list)
             (%restrict default clause.slow-simple-tests (equal x 'x)))

 (local (%disable default
                  clause.flag-simple-tests-removal
                  clause.flag-simple-tests-list-removal))

 (%autoprove clause.slow-simple-tests-removal
             (%enable default clause.simple-tests))

 ;; BOZO clause.slow-simple-tests-list-removal doesn't seem to exist.
 )

(%autoprove clause.simple-tests-when-logic.constantp
            (%restrict default definition-of-clause.simple-tests (equal x 'x)))

(%autoprove clause.simple-tests-when-logic.variablep
            (%restrict default definition-of-clause.simple-tests (equal x 'x)))

(%autoprove clause.simple-tests-when-non-if-logic.functionp
            (%restrict default definition-of-clause.simple-tests (equal x 'x)))

(%autoprove clause.simple-tests-when-bad-args-logic.functionp
            (%restrict default definition-of-clause.simple-tests (equal x 'x)))

(%autoprove clause.simple-tests-when-if
            (%restrict default definition-of-clause.simple-tests (equal x 'x)))

(%autoprove clause.simple-tests-when-logic.lambdap
            (%restrict default definition-of-clause.simple-tests (equal x 'x)))

(%autoprove clause.simple-tests-when-degenerate
            (%restrict default definition-of-clause.simple-tests (equal x 'x)))


(%autoprove clause.simple-tests-list-when-not-consp
            (%restrict default definition-of-clause.simple-tests-list (equal x 'x)))

(%autoprove clause.simple-tests-list-of-cons
            (%restrict default definition-of-clause.simple-tests-list (equal x '(cons a x))))

(%autoprove clause.simple-tests-list-when-len-three)


(%autoprove true-listp-of-clause.simple-tests-list
            (%cdr-induction x))

(%autoprove clause.simple-tests-list-of-list-fix
            (%cdr-induction x))

(%autoprove clause.simple-tests-list-of-app
            (%cdr-induction x))



(%create-theory clause.term-tests-openers)
(%enable clause.term-tests-openers
         clause.term-tests-when-logic.constantp
         clause.term-tests-when-logic.variablep
         clause.term-tests-when-non-if-logic.functionp
         clause.term-tests-when-bad-args-logic.functionp
         clause.term-tests-when-if-logic.functionp
         clause.term-tests-when-logic.lambdap
         clause.term-tests-when-degenerate)

(local (%create-theory common-disables))
(local (%enable common-disables
                expensive-arithmetic-rules
                expensive-arithmetic-rules-two
                type-set-like-rules
                formula-decomposition
                expensive-term/formula-inference
                unusual-subsetp-rules
                unusual-memberp-rules
                unusual-consp-rules
                same-length-prefixes-equal-cheap
                clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                clause.term-tests-openers
                subsetp-of-cons-two
                subsetp-when-not-consp-two
                subsetp-transitive-two
                subsetp-of-app-of-app-when-subsetp-two
                subsetp-of-app-of-app-when-subsetp-one))

(%autoprove lemma-for-subsetp-of-clause.simple-tests-and-clause.term-tests
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%auto)
            (%enable default
                     clause.term-tests-openers
                     subsetp-of-cons-two
                     subsetp-when-not-consp-two
                     subsetp-transitive-two
                     subsetp-of-app-of-app-when-subsetp-two
                     subsetp-of-app-of-app-when-subsetp-one
                     unusual-consp-rules))

(%autoprove subsetp-of-clause.simple-tests-and-clause.term-tests
            (%use (%instance (%thm lemma-for-subsetp-of-clause.simple-tests-and-clause.term-tests)
                             (flag 'term))))

(%autoprove subsetp-of-clause.simple-tests-list-and-clause.term-tests-list
            (%use (%instance (%thm lemma-for-subsetp-of-clause.simple-tests-and-clause.term-tests)
                             (flag 'list))))


(%autoprove lemma-for-clause.simple-term-listp-of-clause.simple-tests
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%auto)
            (%enable default
                     clause.term-tests-openers
                     subsetp-of-cons-two
                     subsetp-when-not-consp-two
                     subsetp-transitive-two
                     subsetp-of-app-of-app-when-subsetp-two
                     subsetp-of-app-of-app-when-subsetp-one
                     unusual-consp-rules))

(%autoprove clause.simple-term-listp-of-clause.simple-tests
            (%use (%instance (%thm lemma-for-clause.simple-term-listp-of-clause.simple-tests)
                             (flag 'term))))

(%autoprove clause.simple-term-listp-of-clause.simple-tests-list
            (%use (%instance (%thm lemma-for-clause.simple-term-listp-of-clause.simple-tests)
                             (flag 'list))))


(%autoprove lemma-for-clause.simple-tests-when-clause.simple-termp
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%auto)
            (%enable default
                     clause.term-tests-openers
                     subsetp-of-cons-two
                     subsetp-when-not-consp-two
                     subsetp-transitive-two
                     subsetp-of-app-of-app-when-subsetp-two
                     subsetp-of-app-of-app-when-subsetp-one
                     unusual-consp-rules))

(%autoprove clause.simple-tests-when-clause.simple-termp
            (%use (%instance (%thm lemma-for-clause.simple-tests-when-clause.simple-termp)
                             (flag 'term))))

(%autoprove clause.simple-tests-list-when-clause.simple-term-listp
            (%use (%instance (%thm lemma-for-clause.simple-tests-when-clause.simple-termp)
                             (flag 'list))))


(%autoprove lemma-for-forcing-logic.term-listp-of-clause.simple-tests
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%auto)
            (%enable default
                     clause.term-tests-openers
                     subsetp-of-cons-two
                     subsetp-when-not-consp-two
                     subsetp-transitive-two
                     subsetp-of-app-of-app-when-subsetp-two
                     subsetp-of-app-of-app-when-subsetp-one
                     unusual-consp-rules))

(%autoprove forcing-logic.term-listp-of-clause.simple-tests
            (%use (%instance (%thm lemma-for-forcing-logic.term-listp-of-clause.simple-tests)
                             (flag 'term))))

(%autoprove forcing-logic.term-listp-of-clause.simple-tests-list
            (%use (%instance (%thm lemma-for-forcing-logic.term-listp-of-clause.simple-tests)
                             (flag 'list))))


(%autoprove lemma-for-forcing-logic.term-list-atblp-of-clause.simple-tests
            (%clause.simple-term-induction flag x)
            (%disable default forcing-true-listp-of-logic.function-args)
            (%disable default common-disables)
            (%auto)
            (%enable default
                     clause.term-tests-openers
                     subsetp-of-cons-two
                     subsetp-when-not-consp-two
                     subsetp-transitive-two
                     subsetp-of-app-of-app-when-subsetp-two
                     subsetp-of-app-of-app-when-subsetp-one
                     unusual-consp-rules))

(%autoprove forcing-logic.term-list-atblp-of-clause.simple-tests
            (%use (%instance (%thm lemma-for-forcing-logic.term-list-atblp-of-clause.simple-tests)
                             (flag 'term))))

(%autoprove forcing-logic.term-list-atblp-of-clause.simple-tests-list
            (%use (%instance (%thm lemma-for-forcing-logic.term-list-atblp-of-clause.simple-tests)
                             (flag 'list))))

