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
(include-book "terms")
(%interactive)

(%autoadmit logic.flag-count-variable-occurrences)
(%autoadmit logic.count-variable-occurrences)
(%autoadmit logic.count-variable-occurrences-list)
(%autoadmit logic.slow-count-variable-occurrences)

(defmacro %logic.flag-count-variable-occurrences-induction (flag x acc)
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
               (,x    (logic.function-args ,x))
               (,acc  ,acc))))
            ((and (equal ,flag 'term)
                  (logic.lambdap ,x))
             (((,flag 'list)
               (,x    (logic.lambda-actuals ,x))
               (,acc  ,acc))))
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
               (acc ,acc))
              ((,flag 'list)
               (,x (cdr ,x))
               (,acc (logic.flag-count-variable-occurrences 'term (car ,x) ,acc)))))))

(%autoprove forcing-natp-of-logic.flag-count-variable-occurrences
            (%logic.flag-count-variable-occurrences-induction flag x acc)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default logic.flag-count-variable-occurrences (equal x 'x)))

(%autoprove lemma-logic.flag-count-variable-occurrences-removal
            (%logic.flag-count-variable-occurrences-induction flag x acc)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default logic.flag-count-variable-occurrences (equal x 'x))
            (%restrict default logic.slow-count-variable-occurrences (equal x 'x))
            (%auto)
            (%fertilize (logic.flag-count-variable-occurrences 'term x1 acc)
                        (+ acc (logic.slow-count-variable-occurrences 'term x1))))

(%autoprove definition-of-logic.count-variable-occurrences
            (%restrict default logic.slow-count-variable-occurrences (equal x 'x))
            (%enable default
                     logic.count-variable-occurrences
                     logic.count-variable-occurrences-list
                     lemma-logic.flag-count-variable-occurrences-removal
                     ))

(%autoprove definition-of-logic.count-variable-occurrences-list
            (%restrict default logic.slow-count-variable-occurrences (equal x 'x))
            (%enable default
                     logic.count-variable-occurrences
                     logic.count-variable-occurrences-list
                     lemma-logic.flag-count-variable-occurrences-removal))

(%autoprove logic.flag-count-variable-occurrences-removal
            (%restrict default logic.slow-count-variable-occurrences (equal x 'x))
            (%enable default
                     logic.count-variable-occurrences
                     logic.count-variable-occurrences-list
                     lemma-logic.flag-count-variable-occurrences-removal))

(%autoprove logic.count-variables-occurrences-list-when-not-consp
            (%restrict default definition-of-logic.count-variable-occurrences-list (equal x 'x)))

(%autoprove logic.count-variables-occurrences-list-of-cons
            (%restrict default definition-of-logic.count-variable-occurrences-list (equal x '(cons a x))))


(%autoprove lemma-for-natp-of-logic.count-variable-occurrences
            (%logic.term-induction flag x)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default definition-of-logic.count-variable-occurrences (equal x 'x)))

(%autoprove natp-of-logic.count-variable-occurrences
            (%use (%instance (%thm lemma-for-natp-of-logic.count-variable-occurrences)
                             (flag 'term))))

(%autoprove natp-of-logic.count-variable-occurrences-list
            (%use (%instance (%thm lemma-for-natp-of-logic.count-variable-occurrences)
                             (flag 'list))))

(%autoprove logic.count-variable-occurrences-when-logic.constantp
            (%restrict default definition-of-logic.count-variable-occurrences (equal x 'x)))

(%autoprove logic.count-variable-occurrences-when-logic.variablep
            (%restrict default definition-of-logic.count-variable-occurrences (equal x 'x)))
