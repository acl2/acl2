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
(include-book "formulas")
(%interactive)


(defthm forcing-equal-of-logic.por-list-rewrite-alt
  ;; BOZO add this to the acl2 model
  (implies (and (force (equal (len x) (len y)))
                (force (logic.formula-listp x))
                (force (logic.formula-listp y)))
           (equal (equal z (logic.por-list x y))
                  (and (true-listp z)
                       (logic.formula-listp z)
                       (logic.all-disjunctionsp z)
                       (equal (list-fix x) (logic.vlhses z))
                       (equal (list-fix y) (logic.vrhses z))))))


(%autoadmit logic.por-list)

(%autoprove logic.por-list-when-not-consp-one
            (%restrict default logic.por-list (equal x 'x)))

(%autoprove logic.por-list-when-not-consp-two
            (%restrict default logic.por-list (equal x 'x)))

(%autoprove logic.por-list-of-cons-and-cons
            (%restrict default logic.por-list (equal x '(cons a x))))

(%autoprove logic.por-list-under-iff)

(%autoprove logic.por-list-of-list-fix-one
            (%cdr-cdr-induction x y))

(%autoprove logic.por-list-of-list-fix-two
            (%cdr-cdr-induction x y))

(%autoprove true-listp-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.formulap-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.formula-atblp-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove consp-of-logic.por-list)

(%autoprove car-of-logic.por-list
            ;; BOZO elim goes berserk
            (%restrict default logic.por-list (equal x 'x)))

(%autoprove cdr-of-logic.por-list)

(%autoprove len-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.por-list-of-singleton-lhs)



(%deflist logic.all-disjunctionsp (x)
          (equal (logic.fmtype x) 'por*)
          :hintsmap
          ((logic.all-disjunctionsp-of-remove-duplicates
            (%cdr-induction x)
            (%auto)
            (%use (%instance (%thm equal-when-memberp-of-logic.all-disjunctionsp)
                             (a x1)
                             (x x2))))
           (logic.all-disjunctionsp-of-subsetp-when-logic.all-disjunctionsp
            (%cdr-induction x)
            (%auto)
            (%use (%instance (%thm equal-when-memberp-of-logic.all-disjunctionsp)
                             (a x1)
                             (x y))))))

(%autoprove logic.fmtype-of-car-when-logic.all-disjunctionsp
            (%enable default equal-of-car-when-logic.all-disjunctionsp))

(%autoprove logic.fmtype-when-memberp-of-logic.all-disjunctionsp
            (%use (%instance (%thm equal-when-memberp-of-logic.all-disjunctionsp))))

(%autoprove logic.fmtype-when-memberp-of-logic.all-disjunctionsp-alt)


(%autoprove forcing-logic.all-disjunctionsp-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.all-disjunctionsp-of-logic.por-list-free)

(%autoprove logic.fmtype-of-nth-when-logic.all-disjunctionsp)




(%defprojection :list (logic.vlhses x)
                :element (logic.vlhs x)
                :nil-preservingp t)

(%autoprove forcing-logic.formula-listp-of-logic.vlhses
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-logic.vlhses
            (%cdr-induction x))

(%autoprove forcing-logic.vlhses-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.vlhses-of-logic.por-list-free)

(%autoprove logic.vlhs-of-car-when-all-equalp-of-logic.vlhses)




(%defprojection :list (logic.vrhses x)
                :element (logic.vrhs x)
                :nil-preservingp t)

(%autoprove forcing-logic.formula-listp-of-logic.vrhses
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-logic.vrhses
            (%cdr-induction x))

(%autoprove forcing-logic.vrhses-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.vrhses-of-logic.por-list-free)

(%autoprove forcing-equal-of-logic.por-list-rewrite
            (%cdr-cdr-cdr-induction x y z))

(%autoprove forcing-equal-of-logic.por-list-rewrite-alt
            (%use (%instance (%thm forcing-equal-of-logic.por-list-rewrite))))


(%ensure-exactly-these-rules-are-missing "../../logic/por-list")

