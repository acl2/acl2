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
(include-book "trace-okp")
(%interactive)


(defsection revappend-lemmas

  (local (%disable default forcing-revappend-removal))

  (%autoprove revappend-under-iff
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove consp-of-revappend
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove memberp-of-revappend
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove subsetp-of-revappend-one
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove subsetp-of-revappend-two
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove true-listp-of-revappend
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove logic.formula-listp-of-revappend
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x)))

  (%autoprove logic.formula-list-atblp-of-revappend
              (%autoinduct revappend x acc)
              (%restrict default revappend (equal x 'x))))


(defsection fast-merge

  (%autoadmit fast-merge)

  (local (%enable default fast-merge))
  (local (%disable default forcing-revappend-removal))

  (%autoprove consp-of-fast-merge)
  (%autoprove true-listp-of-fast-merge)
  (%autoprove memberp-of-fast-merge)
  (%autoprove subsetp-of-fast-merge-one)

  (%autoprove subsetp-of-fast-merge-two
              (%disable default
                        subsetp-of-revappend-two
                        [outside]subsetp-of-revappend-two)
              (%use (%instance (%thm subsetp-of-revappend-two)
                               (x x)
                               (acc y)))
              (%restrict default revappend (equal x 'x)))

  (%autoprove logic.formula-listp-of-fast-merge)
  (%autoprove logic.formula-list-atblp-of-fast-merge)
  (%autoprove fast-merge-when-not-consp-left)
  (%autoprove fast-merge-with-nil-left)
  (%autoprove fast-merge-when-not-consp-right)
  (%autoprove fast-merge-with-nil-right))




(%autoadmit rw.flag-collect-forced-goals)

(%autoprove true-listp-of-rw.flag-collect-forced-goals
            (%autoinduct rw.flag-collect-forced-goals)
            (%restrict default rw.flag-collect-forced-goals (equal x 'x)))

(%autoadmit rw.collect-forced-goals)
(%autoadmit rw.collect-forced-goals-list)

(%autoprove definition-of-rw.collect-forced-goals
            (%enable default
                     rw.collect-forced-goals
                     rw.collect-forced-goals-list)
            (%restrict default rw.flag-collect-forced-goals (equal x 'x)))

(%autoprove definition-of-rw.collect-forced-goals-list
            (%enable default
                     rw.collect-forced-goals
                     rw.collect-forced-goals-list)
            (%restrict default rw.flag-collect-forced-goals (equal x 'x)))

(%autoprove rw.flag-collect-forced-goals-of-term
            (%enable default rw.collect-forced-goals))

(%autoprove rw.flag-collect-forced-goals-of-list
            (%enable default rw.collect-forced-goals-list))



(%autoprove rw.collect-forced-goals-list-when-not-consp
            (%restrict default definition-of-rw.collect-forced-goals-list (equal x 'x)))

(%autoprove rw.collect-forced-goals-list-of-cons
            (%restrict default definition-of-rw.collect-forced-goals-list (equal x '(cons a x))))








(%autoprove lemma-for-true-listp-of-rw.collect-forced-goals
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.collect-forced-goals (equal x 'x)))

(%autoprove true-listp-of-rw.collect-forced-goals
            (%use (%instance (%thm lemma-for-true-listp-of-rw.collect-forced-goals)
                             (flag 'term))))

(%autoprove true-listp-of-rw.collect-forced-goals-list
            (%use (%instance (%thm lemma-for-true-listp-of-rw.collect-forced-goals)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.formula-listp-of-rw.collect-forced-goals
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.collect-forced-goals (equal x 'x)))

(%autoprove forcing-logic.formula-listp-of-rw.collect-forced-goals
            (%use (%instance (%thm lemma-for-forcing-logic.formula-listp-of-rw.collect-forced-goals)
                             (flag 'term))))

(%autoprove forcing-logic.formula-listp-of-rw.collect-forced-goals-list
            (%use (%instance (%thm lemma-for-forcing-logic.formula-listp-of-rw.collect-forced-goals)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.formula-list-atblp-of-rw.collect-forced-goals
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.collect-forced-goals (equal x 'x)))

(%autoprove forcing-logic.formula-list-atblp-of-rw.collect-forced-goals
            (%use (%instance (%thm lemma-for-forcing-logic.formula-list-atblp-of-rw.collect-forced-goals)
                             (flag 'term))))

(%autoprove forcing-logic.formula-list-atblp-of-rw.collect-forced-goals-list
            (%use (%instance (%thm lemma-for-forcing-logic.formula-list-atblp-of-rw.collect-forced-goals)
                             (flag 'list))))





(%autoprove memberp-of-rw.trace-conclusion-formula-in-rw.collect-forced-goals
            (%restrict default definition-of-rw.collect-forced-goals (equal x 'x)))

(%autoprove forcing-subsetp-of-rw.collect-forced-goals-list-of-subtraces
            (%restrict default definition-of-rw.collect-forced-goals (equal x 'x))
            (%restrict default definition-of-rw.trace-okp (equal x 'x))
            (%enable default
                     rw.trace-step-okp
                     rw.force-tracep))






(%autoadmit rw.collect-forced-goals-list-list)

(%autoprove rw.collect-forced-goals-list-list-when-not-consp
            (%restrict default rw.collect-forced-goals-list-list (equal x 'x)))

(%autoprove rw.collect-forced-goals-list-list-of-cons
            (%restrict default rw.collect-forced-goals-list-list (equal x '(cons a x))))

(%autoprove true-listp-of-rw.collect-forced-goals-list-list
            (%cdr-induction x))

(%autoprove forcing-rw.formula-listp-of-rw.collect-forced-goals-list-list
            (%cdr-induction x))



(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/collect-forced-goals")