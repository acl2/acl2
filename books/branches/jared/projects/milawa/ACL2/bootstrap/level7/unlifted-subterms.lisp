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

(%autoadmit clause.unlifted-subterms)

(%autoprove consp-of-clause.unlifted-subterms
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-logic.constantp
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-logic.variablep
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-non-if-logic.functionp
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-bad-args-logic.functionp
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-if-logic.functionp
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-logic.lambdap
            (%restrict default clause.unlifted-subterms (equal x 'x)))

(%autoprove clause.unlifted-subterms-when-degenerate
            (%restrict default clause.unlifted-subterms (equal x 'x)))


(defmacro %clause.unlifted-subterms-induction (x)
  `(%induct (rank ,x)
            ((logic.constantp ,x) nil)
            ((logic.variablep ,x) nil)
            ((and (logic.functionp ,x)
                  (equal (logic.function-name ,x) 'if)
                  (equal (len (logic.function-args ,x)) 3))
             (((,x (first (logic.function-args ,x))))
              ((,x (second (logic.function-args ,x))))
              ((,x (third (logic.function-args ,x))))))
            ((and (logic.functionp ,x)
                  (or (not (equal (logic.function-name ,x) 'if))
                      (not (equal (len (logic.function-args ,x)) 3))))
             nil)
            ((logic.lambdap ,x)
             nil)
            ((and (not (logic.constantp ,x))
                  (not (logic.variablep ,x))
                  (not (logic.functionp ,x))
                  (not (logic.lambdap ,x)))
             nil)))

(%autoprove true-listp-of-clause.unlifted-subterms
            (%clause.unlifted-subterms-induction x))

(%autoprove forcing-logic.term-listp-of-clause.unlifted-subterms
            (%clause.unlifted-subterms-induction x))

(%autoprove clause.unlifted-subterms-when-clause.simple-termp
            (%clause.unlifted-subterms-induction x))

(%autoprove clause.simple-termp-when-memberp-of-clause.unlifted-subterms
            (%clause.unlifted-subterms-induction x)
            ;; speed hint
            (%disable default in-superset-when-in-subset-two
                      not-in-subset-when-not-in-superset-one
                      subsetp-transitive-two
                      subsetp-when-prefixp-cheap
                      subsetp-when-ordered-subsetp
                      memberp-when-memberp-of-cdr
                      clause.simple-termp-when-memberp-of-clause.simple-term-listp-alt))

(%autoprove clause.unlifted-subterms-under-iff
            (%clause.unlifted-subterms-induction x)
            ;; speed hint
            (%disable default
                      clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                      clause.unlifted-subterms-when-clause.simple-termp
                      clause.lifted-termp-when-clause.simple-termp))

(%autoprove clause.simple-term-listp-of-clause.unlifted-subterms
            (%clause.unlifted-subterms-induction x)
            (%disable default
                      clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                      clause.unlifted-subterms-when-clause.simple-termp
                      clause.lifted-termp-when-clause.simple-termp))





(%autoadmit clause.unlifted-subterms-list)

(%autoprove clause.unlifted-subterms-list-when-not-consp
            (%restrict default clause.unlifted-subterms-list (equal x 'x)))

(%autoprove clause.unlifted-subterms-list-of-cons
            (%restrict default clause.unlifted-subterms-list (equal x '(cons a x))))

(%autoprove true-listp-of-clause.unlifted-subterms-list
            (%cdr-induction x))

(%autoprove consp-of-clause.unlifted-subterms-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-listp-of-clause.unlifted-subterms-list
            (%cdr-induction x))

(%autoprove clause.unlifted-subterms-list-of-list-fix
            (%cdr-induction x))

(%autoprove clause.unlifted-subterms-list-of-app
            (%cdr-induction x))

(%autoprove clause.simple-termp-when-memberp-of-clause.unlifted-subterms-list
            (%cdr-induction x))

(%autoprove clause.unlifted-subterms-list-under-iff
            (%cdr-induction x))

(%autoprove clause.simple-term-listp-of-clause.unlifted-subterms-list
            (%cdr-induction x))


(%create-theory clause.unlifted-subterms-openers)
(%enable clause.unlifted-subterms-openers
         clause.unlifted-subterms-when-logic.constantp
         clause.unlifted-subterms-when-logic.variablep
         clause.unlifted-subterms-when-non-if-logic.functionp
         clause.unlifted-subterms-when-bad-args-logic.functionp
         clause.unlifted-subterms-when-if-logic.functionp
         clause.unlifted-subterms-when-logic.lambdap
         clause.unlifted-subterms-when-degenerate)
