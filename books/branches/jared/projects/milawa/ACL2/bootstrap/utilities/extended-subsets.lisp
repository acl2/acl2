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
(include-book "deflist")
(include-book "cons-listp")
(include-book "remove-duplicates-list")
(%interactive)


(%autoadmit superset-of-somep)
(%autoprove superset-of-somep-when-not-consp         (%restrict default superset-of-somep (equal x 'x)))
(%autoprove superset-of-somep-of-cons                (%restrict default superset-of-somep (equal x '(cons b x))))
(%autoprove booleanp-of-superset-of-somep            (%cdr-induction x))
(%autoprove superset-of-somep-of-list-fix-one        (%cdr-induction x))
(%autoprove superset-of-somep-of-list-fix-two        (%cdr-induction x))
(%autoprove superset-of-somep-of-app                 (%cdr-induction x))
(%autoprove superset-of-somep-of-rev                 (%cdr-induction x))
(%autoprove memberp-when-not-superset-of-somep-cheap (%cdr-induction x))
(%autoprove superset-of-somep-when-obvious           (%cdr-induction x))
(%autoprove superset-of-somep-when-obvious-alt)


(%autoadmit find-subset)
(%autoprove find-subset-when-not-consp         (%restrict default find-subset (equal x 'x)))
(%autoprove find-subset-of-cons                (%restrict default find-subset (equal x '(cons b x))))
(%autoprove find-subset-of-list-fix-one        (%cdr-induction x))
(%autoprove find-subset-of-list-fix-two        (%cdr-induction x))
(%autoprove find-subset-of-rev-one             (%cdr-induction x))
(%autoprove subsetp-of-find-subset             (%cdr-induction x))
(%autoprove memberp-of-find-subset             (%cdr-induction x))
(%autoprove superset-of-somep-when-find-subset (%cdr-induction x))
(%autoprove find-subset-of-app                 (%cdr-induction x))
(%autoprove find-subset-when-subsetp-two       (%cdr-induction x))

(%autoprove superset-of-somep-when-subsetp-two
            (%disable default superset-of-somep-when-obvious superset-of-somep-when-obvious-alt)
            (%use (%instance (%thm superset-of-somep-when-obvious)
                             (a a)
                             (e (find-subset a x))
                             (x y))))

(%autoprove superset-of-somep-when-subsetp-two-alt)
(%autoprove superset-of-somep-when-superset-of-somep-of-smaller     (%cdr-induction x))
(%autoprove superset-of-somep-when-superset-of-somep-of-smaller-alt (%cdr-induction x))


(%deflist all-superset-of-somep (x ys)
          (superset-of-somep x ys))

(%autoprove all-superset-of-somep-of-list-fix-two               (%cdr-induction x))
(%autoprove all-superset-of-somep-of-cons-two                   (%cdr-induction x))
(%autoprove all-superset-of-somep-of-all-two                    (%cdr-induction x))
(%autoprove all-superset-of-somep-of-all-two-alt                (%cdr-induction x))
(%autoprove all-superset-of-somep-of-rev-two                    (%cdr-induction x))
(%autoprove all-superset-of-somep-when-subsetp-two              (%cdr-induction x))
(%autoprove all-superset-of-somep-when-subsetp-two-alt          (%cdr-induction x))
(%autoprove all-superset-of-somep-of-cons-two-when-irrelevant   (%cdr-induction x))
(%autoprove all-superset-of-somep-of-app-two-when-irrelevant    (%cdr-induction y))
(%autoprove superset-of-somep-when-all-superset-of-somep        (%cdr-induction x))
(%autoprove superset-of-somep-when-all-superset-of-somep-alt)
(%autoprove all-superset-of-somep-is-reflexive                  (%cdr-induction x))
(%autoprove all-superset-of-somep-is-transitive                 (%cdr-induction x))
(%autoprove all-superset-of-somep-of-remove-duplicates-list     (%cdr-induction x))
(%autoprove all-superset-of-somep-of-remove-duplicates-list-gen (%cdr-induction x))


(%autoadmit remove-supersets1)

(%autoprove remove-supersets1-when-not-consp                  (%restrict default remove-supersets1 (equal todo 'x)))
(%autoprove remove-supersets1-of-cons                         (%restrict default remove-supersets1 (equal todo '(cons a x))))
(%autoprove true-listp-of-remove-supersets1                   (%autoinduct remove-supersets1 x done))
(%autoprove uniquep-of-remove-supersets1                      (%autoinduct remove-supersets1 todo done))
(%autoprove all-superset-of-somep-of-remove-supersets1        (%autoinduct remove-supersets1 todo done))
(%autoprove cons-listp-when-not-superset-of-some-is-non-consp (%cdr-induction x))
(%autoprove cons-listp-of-remove-supersets1                   (%autoinduct remove-supersets1 todo done))



(%autoadmit remove-supersets)
(%autoprove true-listp-of-remove-supersets                (%enable default remove-supersets))
(%autoprove all-superset-of-somep-of-remove-supersets     (%enable default remove-supersets))
(%autoprove all-superset-of-somep-of-remove-supersets-gen (%enable default remove-supersets))
(%autoprove cons-listp-of-remove-supersets                (%enable default remove-supersets))



(%autoadmit subset-of-somep)
(%autoprove subset-of-somep-when-not-consp         (%restrict default subset-of-somep (equal x 'x)))
(%autoprove subset-of-somep-of-cons                (%restrict default subset-of-somep (equal x '(cons b x))))
(%autoprove booleanp-of-subset-of-somep            (%cdr-induction x))
(%autoprove subset-of-somep-of-list-fix-one        (%cdr-induction x))
(%autoprove subset-of-somep-of-list-fix-two        (%cdr-induction x))
(%autoprove subset-of-somep-of-app                 (%cdr-induction x))
(%autoprove subset-of-somep-of-rev                 (%cdr-induction x))
(%autoprove memberp-when-not-subset-of-somep-cheap (%cdr-induction x))
(%autoprove subset-of-somep-when-obvious           (%cdr-induction x))
(%autoprove subset-of-somep-when-obvious-alt)


(%autoadmit find-superset)

(%autoprove find-superset-when-not-consp       (%restrict default find-superset (equal x 'x)))
(%autoprove find-superset-of-cons              (%restrict default find-superset (equal x '(cons b x))))
(%autoprove find-superset-of-list-fix-one      (%cdr-induction x))
(%autoprove find-superset-of-list-fix-two      (%cdr-induction x))
(%autoprove find-superset-of-rev-one           (%cdr-induction x))
(%autoprove subsetp-of-find-superset           (%cdr-induction x))
(%autoprove memberp-of-find-superset           (%cdr-induction x))
(%autoprove subset-of-somep-when-find-superset (%cdr-induction x))
(%autoprove find-superset-when-subsetp-two     (%cdr-induction x))

(%autoprove subset-of-somep-when-subsetp-two
            (%disable default subset-of-somep-when-obvious subset-of-somep-when-obvious-alt)
            (%use (%instance (%thm subset-of-somep-when-obvious)
                             (a a)
                             (e (find-superset a x))
                             (x y))))

(%autoprove subset-of-somep-when-subsetp-two-alt)
(%autoprove subset-of-somep-when-subset-of-somep-of-smaller     (%cdr-induction x))
(%autoprove subset-of-somep-when-subset-of-somep-of-smaller-alt (%cdr-induction x))


(%deflist all-subset-of-somep (x ys)
          (subset-of-somep x ys))

(%autoprove all-subset-of-somep-of-list-fix-two               (%cdr-induction x))
(%autoprove all-subset-of-somep-of-cons-two                   (%cdr-induction x))
(%autoprove all-subset-of-somep-of-all-two                    (%cdr-induction x))
(%autoprove all-subset-of-somep-of-all-two-alt                (%cdr-induction x))
(%autoprove all-subset-of-somep-of-rev-two                    (%cdr-induction x))
(%autoprove all-subset-of-somep-when-subsetp-two              (%cdr-induction x))
(%autoprove all-subset-of-somep-when-subsetp-two-alt          (%cdr-induction x))
(%autoprove all-subset-of-somep-of-cons-two-when-irrelevant   (%cdr-induction x))
(%autoprove all-subset-of-somep-of-app-two-when-irrelevant    (%cdr-induction y))
(%autoprove subset-of-somep-when-all-subset-of-somep          (%cdr-induction x))
(%autoprove subset-of-somep-when-all-subset-of-somep-alt)
(%autoprove all-subset-of-somep-is-reflexive                  (%cdr-induction x))
(%autoprove all-subset-of-somep-is-transitive                 (%cdr-induction x))
(%autoprove all-subset-of-somep-of-remove-duplicates-list     (%cdr-induction x))
(%autoprove all-subset-of-somep-of-remove-duplicates-list-gen (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../utilities/extended-subsets")