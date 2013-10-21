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
(include-book "base-evaluator")
(include-book "substitute-formula")
(%interactive)


(%autoadmit logic.flag-appealp)
(%autoadmit logic.appealp)
(%autoadmit logic.appeal-listp)

(%autoadmit logic.appeal)
(%autoadmit logic.method)
(%autoadmit logic.conclusion)
(%autoadmit logic.subproofs)
(%autoadmit logic.extras)

(%autoprove definition-of-logic.appealp
            (%enable default logic.appealp logic.appeal-listp)
            (%restrict default logic.flag-appealp (equal x 'x)))

(%autoprove definition-of-logic.appeal-listp
            (%enable default logic.appealp logic.appeal-listp)
            (%restrict default logic.flag-appealp (equal x 'x)))

(defmacro %logic.appeal-induction (flag x)
  ;; weird that this has 'list instead of 'proof??
  `(%induct (two-nats-measure (rank ,x) (if (equal ,flag 'proof) '1 '0))
            ((equal ,flag 'proof)
             (((,x    (logic.subproofs ,x))
               (,flag 'list))))
            ((and (not (equal ,flag 'proof))
                  (consp ,x))
             (((,x    (car ,x))
               (,flag 'proof))
              ((,x    (cdr ,x))
               (,flag 'list))))
            ((and (not (equal ,flag 'proof))
                  (not (consp ,x)))
             nil)))

(defsection lemma-for-booleanp-of-logic.appealp
  (%prove (%rule lemma-for-booleanp-of-logic.appealp
                 :lhs (if (equal flag 'proof)
                          (booleanp (logic.appealp x))
                        (booleanp (logic.appeal-listp x)))
                 :rhs t))
  (%logic.appeal-induction flag x)
  (local (%restrict default definition-of-logic.appealp (equal x 'x)))
  (local (%restrict default definition-of-logic.appeal-listp (equal x 'x)))
  (local (%enable default logic.subproofs))
  (%auto)
  (%qed))

(%autoprove booleanp-of-logic.appealp
            (%use (%instance (%thm lemma-for-booleanp-of-logic.appealp) (flag 'proof))))

(%autoprove booleanp-of-logic.appeal-listp
            (%use (%instance (%thm lemma-for-booleanp-of-logic.appealp) (flag 'list))))

(%autoprove logic.appeal-listp-when-not-consp
            (%restrict default definition-of-logic.appeal-listp (equal x 'x)))

(%autoprove logic.appeal-listp-of-cons
            (%restrict default definition-of-logic.appeal-listp (equal x '(cons a x))))

(%deflist logic.appeal-listp (x)
          (logic.appealp x))


(%autoprove logic.appealp-of-nth-when-logic.appeal-listp)

(%autoprove logic.appealp-of-second-when-logic.appeal-listp)

(%autoprove forcing-logic.appeal-listp-of-firstn)

(%autoprove forcing-logic.appeal-listp-of-restn)



(%autoprove logic.method-of-logic.appeal
            (%enable default logic.appeal logic.method))

(%autoprove logic.conclusion-of-logic.appeal
            (%enable default logic.appeal logic.conclusion))

(%autoprove logic.subproofs-of-logic.appeal
            (%enable default logic.appeal logic.subproofs))

(%autoprove logic.extras-of-logic.appeal
            (%enable default logic.appeal logic.extras))

(%autoprove logic.appeal-under-iff
            (%enable default logic.appeal))

(%autoprove forcing-logic.appealp-of-logic.appeal
            (%enable default logic.appeal)
            (%restrict default definition-of-logic.appealp
                       (or (equal x '(CONS METHOD (CONS CONCLUSION 'NIL)))
                           (equal x '(CONS METHOD (CONS CONCLUSION (CONS SUBPROOFS 'NIL))))
                           (equal x '(CONS METHOD (CONS CONCLUSION (CONS SUBPROOFS (CONS EXTRAS 'NIL))))))))


(%autoprove forcing-symbolp-of-logic.method
            (%enable default logic.method)
            (%restrict default definition-of-logic.appealp (equal x 'x)))

(%autoprove forcing-logic.formulap-of-logic.conclusion
            (%enable default logic.conclusion)
            (%restrict default definition-of-logic.appealp (equal x 'x)))

(%autoprove forcing-true-listp-of-logic.subproofs
            (%enable default logic.subproofs)
            (%restrict default definition-of-logic.appealp (equal x 'x)))

(%autoprove forcing-logic.appeal-listp-of-logic.subproofs
            (%enable default logic.subproofs)
            (%restrict default definition-of-logic.appealp (equal x 'x)))


(%autoprove rank-of-logic.subproofs
            (%enable default logic.subproofs)
            (%restrict default definition-of-logic.appealp (equal x 'x)))

(%autoprove rank-of-logic.subproofs-weak
            (%enable default logic.subproofs))

(%autoprove rank-of-logic.subproofs-strong-via-consp
            (%enable default logic.subproofs))

(%autoprove rank-of-first-of-logic.subproofs
            (%disable default rank-of-logic.subproofs)
            (%use (%instance (%thm rank-of-logic.subproofs))))

(%autoprove rank-of-second-of-logic.subproofs
            (%disable default rank-of-logic.subproofs)
            (%use (%instance (%thm rank-of-logic.subproofs))))

