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
(include-book "terms-2-term-vars")
(include-book "terms-2-variable-listp")
(%interactive)


(%autoadmit logic.flag-termp)
(%autoadmit logic.termp)
(%autoadmit logic.term-listp)

(defmacro %logic.term-induction (flag x)
  `(%induct (rank ,x)
            ((and (equal ,flag 'term)
                  (logic.constantp ,x))
             nil)
            ((and (equal flag 'term)
                  (logic.variablep ,x))
             nil)
            ((and (equal ,flag 'term)
                  (logic.functionp ,x))
             (((,flag 'list)
               (,x    (logic.function-args ,x)))))
            ((and (equal ,flag 'term)
                  (logic.lambdap ,x))
             (((,flag 'term)
               (,x    (logic.lambda-body ,x)))
              ((,flag 'list)
               (,x    (logic.lambda-actuals ,x)))))
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
               (,x    (car ,x)))
              ((,flag 'list)
               (,x    (cdr ,x)))))))

(%autoprove definition-of-logic.termp
            (%enable default logic.termp logic.term-listp)
            (%restrict default logic.flag-termp (equal x 'x)))

(%autoprove definition-of-logic.term-listp
            (%enable default logic.termp logic.term-listp)
            (%restrict default logic.flag-termp (equal x 'x)))

(%autoprove logic.termp-when-not-consp-cheap
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.termp-when-logic.variablep
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.termp-when-logic.constantp
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.term-listp-when-not-consp
            (%restrict default definition-of-logic.term-listp (equal x 'x)))

(%autoprove logic.term-listp-of-cons
            (%restrict default definition-of-logic.term-listp (equal x '(cons a x))))

(%autoprove booleanp-of-logic.term-listp
            (%cdr-induction x))

(%autoprove booleanp-of-logic.termp
            (%restrict default definition-of-logic.termp (equal x 'x)))


(%deflist logic.term-listp (x)
          (logic.termp x))

(%autoprove first-under-iff-when-logic.term-listp-with-len-free)

(%autoprove second-under-iff-when-logic.term-listp-with-len-free)

(%autoprove third-under-iff-when-logic.term-listp-with-len-free)
