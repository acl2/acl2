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
(include-book "simple-termp")
(%interactive)

(%autoadmit clause.lifted-termp)

(%autoprove clause.lifted-termp-when-logic.constantp
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-logic.variablep
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-not-if
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-bad-args-logic.functionp
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-if-logic.functionp
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-if-logic.lambdap
            (%restrict default clause.lifted-termp (equal x 'x)))

(%autoprove clause.lifted-termp-when-degenerate
            (%restrict default clause.lifted-termp (equal x 'x)))

(defmacro %clause.lifted-termp-induction (x)
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
                  (not (and (equal (logic.function-name ,x) 'if)
                            (equal (len (logic.function-args ,x)) 3))))
             nil)
            ((logic.lambdap ,x) nil)
            ((not (or (logic.constantp ,x)
                      (logic.variablep ,x)
                      (logic.functionp ,x)
                      (logic.lambdap ,x)))
             nil)))

(%autoprove clause.lifted-termp-when-clause.simple-termp
            (%clause.lifted-termp-induction x))

(%autoprove booleanp-of-clause.lifted-termp
            (%clause.lifted-termp-induction x))

(%deflist clause.lifted-term-listp (x)
          (clause.lifted-termp x))

(%ensure-exactly-these-rules-are-missing "../../clauses/if-lifting/lifted-termp")

(%create-theory clause.lifted-termp-openers)
(%enable clause.lifted-termp-openers
         clause.lifted-termp-when-logic.constantp
         clause.lifted-termp-when-logic.variablep
         clause.lifted-termp-when-not-if
         clause.lifted-termp-when-bad-args-logic.functionp
         clause.lifted-termp-when-if-logic.functionp
         clause.lifted-termp-when-if-logic.lambdap
         clause.lifted-termp-when-degenerate)
