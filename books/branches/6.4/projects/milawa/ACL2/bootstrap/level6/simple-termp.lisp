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


(%autoadmit clause.flag-simple-termp)
(%autoadmit clause.simple-termp)
(%autoadmit clause.simple-term-listp)

(%autoprove definition-of-clause.simple-termp
            (%enable default clause.simple-termp clause.simple-term-listp)
            (%restrict default clause.flag-simple-termp (equal x 'x)))

(%autoprove definition-of-clause.simple-term-listp
            (%enable default clause.simple-termp clause.simple-term-listp)
            (%restrict default clause.flag-simple-termp (equal x 'x)))

(%autoprove clause.flag-simple-termp-of-term-removal
            (%enable default clause.simple-termp))

(%autoprove clause.flag-simple-termp-of-list-removal
            (%enable default clause.simple-term-listp))

(%autoprove clause.simple-termp-when-logic.variablep
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-logic.constantp
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-non-if-logic.functionp
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-bad-args-logic.functionp
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-if-logic.functionp
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-logic.lambdap
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))

(%autoprove clause.simple-termp-when-degenerate
            (%restrict default definition-of-clause.simple-termp (equal x 'x)))


(defmacro %clause.simple-term-induction (flag x)
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
             (((,flag 'term) (,x (first (logic.function-args ,x))))
              ((,flag 'term) (,x (second (logic.function-args ,x))))
              ((,flag 'term) (,x (third (logic.function-args ,x))))))
            ((and (equal ,flag 'term)
                  (logic.functionp ,x)
                  (not (and (equal (logic.function-name ,x) 'if)
                            (equal (len (logic.function-args ,x)) 3))))
             (((,flag 'list) (,x (logic.function-args ,x)))))
            ((and (equal ,flag 'term)
                  (logic.lambdap ,x))
             (((,flag 'list) (,x (logic.lambda-actuals ,x)))))
            ((and (equal ,flag 'term)
                  (not (or (logic.constantp ,x)
                           (logic.variablep ,x)
                           (logic.functionp ,x)
                           (logic.lambdap ,x))))
             nil)
            ((and (not (equal ,flag 'term))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (consp ,x))
             (((,flag 'term) (,x (car ,x)))
              ((,flag 'list) (,x (cdr ,x)))))))

(%autoprove clause.simple-term-listp-when-not-consp
            (%restrict default definition-of-clause.simple-term-listp (equal x 'x)))

(%autoprove clause.simple-term-listp-of-cons
            (%restrict default definition-of-clause.simple-term-listp (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-clause.simple-termp
            (%clause.simple-term-induction flag x))

(%autoprove booleanp-of-clause.simple-termp
            (%use (%instance (%thm lemma-for-booleanp-of-clause.simple-termp)
                             (flag 'term))))

(%autoprove booleanp-of-clause.simple-term-listp
            (%use (%instance (%thm lemma-for-booleanp-of-clause.simple-termp)
                             (flag 'list))))

(%deflist clause.simple-term-listp (x)
          (clause.simple-termp x))


(%autoprove clause.simple-term-listp-when-length-three)

(%deflist clause.simple-term-list-listp (x)
          (clause.simple-term-listp x))



(%create-theory clause.simple-termp-openers)
(%enable clause.simple-termp-openers
         clause.simple-termp-when-logic.variablep
         clause.simple-termp-when-logic.constantp
         clause.simple-termp-when-non-if-logic.functionp
         clause.simple-termp-when-bad-args-logic.functionp
         clause.simple-termp-when-if-logic.functionp
         clause.simple-termp-when-logic.lambdap
         clause.simple-termp-when-degenerate)


(%ensure-exactly-these-rules-are-missing "../../clauses/if-lifting/simple-termp")

