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
(include-book "terms-1")
(%interactive)



(%autoadmit logic.flag-term-vars)
(%autoadmit logic.slow-term-vars)
(%autoadmit logic.term-vars)
(%autoadmit logic.term-list-vars)

(defmacro %logic.flag-term-vars-induction (flag x acc)
  `(%induct (rank ,x)
            ((and (equal ,flag 'term)
                  (or (logic.constantp ,x)
                      (logic.variablep ,x)
                      (not (consp ,x))))
             nil)
            ((and (equal ,flag 'term)
                  (not (logic.constantp ,x))
                  (not (logic.variablep ,x))
                  (consp ,x))
             (((,flag 'list)
               (,x    (cdr ,x))
               (,acc  ,acc))))
            ((and (not (equal ,flag 'term))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (consp ,x))
             (((,flag 'term)
               (,x    (car ,x))
               (,acc  (logic.flag-term-vars 'list (cdr ,x) ,acc)))
              ((,flag 'list)
               (,x    (cdr ,x))
               (,acc  ,acc))))))



(%autoprove true-listp-of-logic.flag-term-vars
            (%restrict default logic.flag-term-vars (equal x 'x))
            (%logic.flag-term-vars-induction flag x acc)
            ;; big gains by avoiding urewrite for some reason
            (%auto :strategy (cleanup split crewrite elim)))

(encapsulate
 ()
 (%autoprove lemma-for-definition-of-logic.term-vars
             (%logic.flag-term-vars-induction flag x acc)
             (%restrict default logic.flag-term-vars (equal x 'x))
             (%restrict default logic.slow-term-vars (equal x 'x))
             (%auto :strategy (cleanup split crewrite elim)))

 (local (%enable default lemma-for-definition-of-logic.term-vars))

 (%autoprove definition-of-logic.term-vars
             (%enable default logic.term-vars logic.term-list-vars)
             (%restrict default logic.slow-term-vars (equal x 'x)))

 (%autoprove definition-of-logic.term-list-vars
             (%enable default logic.term-vars logic.term-list-vars)
             (%restrict default logic.slow-term-vars (equal x 'x)))

 (%autoprove logic.flag-term-vars-of-term-removal
             (%enable default logic.term-vars)
             (%restrict default logic.slow-term-vars (equal x 'x)))

 (%autoprove logic.flag-term-vars-of-list-removal
             (%enable default logic.term-list-vars)
             (%restrict default logic.slow-term-vars (equal x 'x))))

