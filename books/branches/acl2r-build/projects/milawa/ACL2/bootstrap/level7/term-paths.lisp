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
(include-book "term-tests")
(%interactive)


;; (clause.term-paths x)
;;
;; We walk down the term and create lists of all the if expressions we
;; encounter along the way.  I.e., these paths show you each set of choices you
;; would need to make in order to get to every tip of a term.

(%autoadmit clause.flag-term-paths)
(%autoadmit clause.term-paths)
(%autoadmit clause.term-paths-list)

(%autoprove definition-of-clause.term-paths
            (%restrict default clause.flag-term-paths (equal x 'x))
            (%enable default clause.term-paths clause.term-paths-list))

(%autoprove definition-of-clause.term-paths-list
            (%restrict default clause.flag-term-paths (equal x 'x))
            (%enable default clause.term-paths clause.term-paths-list))

(%autoprove clause.flag-term-paths-of-term-removal
            (%enable default clause.term-paths))

(%autoprove clause.flag-term-paths-of-list-removal
            (%enable default clause.term-paths-list))



(%autoprove clause.term-paths-when-logic.constantp
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-logic.variablep
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-non-if-logic.functionp
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-bad-args-logic.functionp
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-if-logic.functionp
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-logic.lambdap
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-degenerate
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-list-when-not-consp
            (%restrict default definition-of-clause.term-paths-list (equal x 'x)))

(%autoprove clause.term-paths-list-of-cons
            (%restrict default definition-of-clause.term-paths-list (equal x '(cons a x))))

(%autoprove clause.term-paths-list-when-len-three)




(%create-theory clause.term-paths-openers)
(%enable clause.term-paths-openers
         clause.term-paths-when-logic.constantp
         clause.term-paths-when-logic.variablep
         clause.term-paths-when-non-if-logic.functionp
         clause.term-paths-when-bad-args-logic.functionp
         clause.term-paths-when-if-logic.functionp
         clause.term-paths-when-logic.lambdap
         clause.term-paths-when-degenerate
         clause.term-paths-list-when-not-consp
         clause.term-paths-list-of-cons
         clause.term-paths-list-when-len-three)



(%autoprove lemma-for-clause.term-paths-when-clause.simple-termp
            (%clause.simple-term-induction flag x))

(%autoprove clause.term-paths-when-clause.simple-termp
            (%use (%instance (%thm lemma-for-clause.term-paths-when-clause.simple-termp)
                             (flag 'term))))

(%autoprove clause.term-paths-list-when-clause.simple-term-listp
            (%use (%instance (%thm lemma-for-clause.term-paths-when-clause.simple-termp)
                             (flag 'list))))



(local (%create-theory common-disables))
(local (%enable common-disables
                expensive-arithmetic-rules
                expensive-arithmetic-rules-two
                type-set-like-rules
                formula-decomposition
                expensive-term/formula-inference
                unusual-subsetp-rules
                unusual-memberp-rules
                unusual-consp-rules
                usual-consp-rules
                same-length-prefixes-equal-cheap
                clause.term-paths-openers
                subsetp-when-not-consp-two
                subsetp-when-not-consp
                app-when-not-consp-two
                app-when-not-consp
                logic.term-list-listp-when-not-consp
                clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                logic.term-listp-when-subset-of-somep-alt
                logic.term-list-listp-when-all-superset-of-somep-alt))

(%autoprove lemma-for-forcing-logic.term-list-listp-of-clause.term-paths
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%auto)
            (%enable default
                     clause.term-paths-openers
                     unusual-consp-rules))

(%autoprove forcing-logic.term-list-listp-of-clause.term-paths
            (%use (%instance (%thm lemma-for-forcing-logic.term-list-listp-of-clause.term-paths)
                             (flag 'term))))

(%autoprove forcing-logic.term-list-listp-of-clause.term-paths-list
            (%use (%instance (%thm lemma-for-forcing-logic.term-list-listp-of-clause.term-paths)
                             (flag 'list))))




(%autoprove lemma-for-forcing-consp-of-clause.term-paths
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%auto)
            (%enable default
                     clause.term-paths-openers
                     unusual-consp-rules))

(%autoprove forcing-consp-of-clause.term-paths
            (%use (%instance (%thm lemma-for-forcing-consp-of-clause.term-paths)
                             (flag 'term))))

(%autoprove forcing-consp-of-clause.term-paths-list
            (%use (%instance (%thm lemma-for-forcing-consp-of-clause.term-paths)
                             (flag 'list))))



(%autoprove disjoint-from-nonep-of-clause.term-paths-when-memberp
            (%cdr-induction x)
            (%disable default common-disables))


(%autoprove lemma-for-disjoint-from-nonep-of-clause.simple-tests-and-clause.term-paths
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%auto)
            (%enable default
                     clause.term-paths-openers
                     unusual-consp-rules))

(%autoprove disjoint-from-nonep-of-clause.simple-tests-and-clause.term-paths
            (%use (%instance (%thm lemma-for-disjoint-from-nonep-of-clause.simple-tests-and-clause.term-paths)
                             (flag 'term))))

(%autoprove disjoint-from-nonep-of-clause.simple-tests-list-and-clause.term-paths-list
            (%use (%instance (%thm lemma-for-disjoint-from-nonep-of-clause.simple-tests-and-clause.term-paths)
                             (flag 'list))))

