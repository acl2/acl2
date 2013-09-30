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
(include-book "casesplit")
(include-book "term-paths")
(include-book "unlifted-subterms")
(include-book "depth-1")
(%interactive)


;; BOZO I think this could be split up a lot better.  Lots of this doesn't seem
;; to need deepest.


(%autoadmit clause.deepest)

(%autoprove clause.deepest-when-not-consp
            (%restrict default clause.deepest (equal x 'x)))

(%autoprove clause.deepest-of-cons
            (%restrict default clause.deepest (equal x '(cons a x))))

(%autoprove clause.deepest-of-list-fix
            (%cdr-induction x))

(%autoprove clause.deepest-of-app
            ;; BOZO ugly acl2 proof enables clause.deepest instead of using cdr-induction.
            (%cdr-induction x))

(%autoprove memberp-of-clause.deepest
            (%cdr-induction x))

(%autoprove positiveness-of-clause.depth-of-clause.deepest
            (%cdr-induction x))

(%autoprove clause.deepest-weakly-deeper-than-any-member
            (%cdr-induction x))





(%autoprove clause.depth-list-redefinition
            (%cdr-induction x)
            (%forcingp nil))


(local (%create-theory common-disables))
(local (%enable common-disables
                expensive-arithmetic-rules
                expensive-arithmetic-rules-two
                type-set-like-rules
                formula-decomposition
                expensive-term/formula-inference
                unusual-consp-rules
                same-length-prefixes-equal-cheap
                clause.term-tests-openers
                clause.term-paths-openers
                clause.lifted-termp-openers
                clause.simple-termp-openers
                clause.unlifted-subterms-openers
                clause.factor-openers
                app-when-not-consp-two
                forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                clause.depth-list-when-not-consp
                clause.depth-list-when-clause.simple-term-listp
                clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                clause.simple-termp-of-car-when-clause.simple-term-listp
                clause.depth-when-clause.simple-termp
                clause.unlifted-subterms-when-clause.simple-termp))

(%autoprove clause.unlifted-subterms-weakly-decreases-clause.depth
            (%clause.unlifted-subterms-induction x)
            (%disable default common-disables)
            (%restrict default clause.unlifted-subterms (equal x 'x))
            (%restrict default definition-of-clause.depth (equal x 'x))
            (%auto)
            (%enable default
                     trichotomy-of-<
                     antisymmetry-of-<
                     expensive-arithmetic-rules-two
                     expensive-term/formula-inference
                     unusual-consp-rules))

(%autoprove forcing-clause.simple-termp-of-clause.deepest
            (%cdr-induction x))

(%autoprove lemma-for-clause.factor-when-irrelevant-tests
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%disable default
                      disjointp-when-subsetp-of-other-one
                      disjointp-when-subsetp-of-other-two
                      disjointp-when-subsetp-of-disjointp-four
                      disjointp-when-subsetp-of-disjointp-three
                      disjointp-when-subsetp-of-disjointp-two
                      disjointp-when-subsetp-of-disjointp-one)
            (%enable default
                     clause.term-tests-openers
                     clause.factor-openers)
            (%auto)
            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference
                     unusual-consp-rules))

(%autoprove clause.factor-when-irrelevant-tests
            (%use (%instance (%thm lemma-for-clause.factor-when-irrelevant-tests)
                             (flag 'term))))

(%autoprove clause.factor-list-when-irrelevant-tests
            (%use (%instance (%thm lemma-for-clause.factor-when-irrelevant-tests)
                             (flag 'list))))



(%autoprove lemma-for-clause.depth-of-clause.factor-weak
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%restrict default definition-of-clause.depth (equal x 'x))
            (%auto)
            (%enable default
                     clause.simple-termp-openers
                     clause.factor-openers)
            (%auto)
            (%enable default
                     antisymmetry-of-<
                     expensive-arithmetic-rules-two
                     expensive-term/formula-inference
                     unusual-consp-rules)
            (%disable default
                      clause.simple-termp-openers
                      clause.factor-openers
                      one-plus-trick
                      less-when-zp-left-cheap
                      clause.factor-openers
                      squeeze-law-one
                      squeeze-law-two
                      squeeze-law-three))

(%autoprove clause.depth-of-clause.factor-weak
            (%use (%instance (%thm lemma-for-clause.depth-of-clause.factor-weak) (flag 'term))))

(%autoprove clause.depth-of-clause.factor-list-weak
            (%use (%instance (%thm lemma-for-clause.depth-of-clause.factor-weak) (flag 'list))))


(%autoprove lemma-2-for-clause.depth-of-clause.factor-strong
            (%disable default ;; speed hack
                      type-set-like-rules
                      squeeze-law-two
                      same-length-prefixes-equal-cheap
                      clause.depth-when-clause.simple-termp
                      clause.factor-when-irrelevant-tests)
            (%use (%instance (%thm |a <= b, b <= c --> a < 1+c|)
                             (a (clause.depth (clause.factor a assignment)))
                             (b (clause.depth a))
                             (c (clause.depth b)))))


(%autoprove lemma-for-clause.depth-of-clause.factor-strong
            ;; BOZO expensive terrible proof
            (%clause.simple-term-induction flag x)
            (%auto :strategy (cleanup split urewrite))
            (%restrict default definition-of-clause.depth (equal x 'x))
            (%cheapen default
                      disjoint-from-nonep-of-subsetp-when-disjoint-from-nonep
                      disjointp-when-memberp-of-disjoint-from-nonep
                      disjointp-when-subsetp-of-other-two
                      disjointp-when-subsetp-of-other-one
                      disjointp-when-subsetp-of-disjointp-four
                      clause.factor-when-irrelevant-tests
                      clause.factor-list-when-irrelevant-tests
                      clause.simple-termp-when-memberp-of-clause.simple-term-listp
                      clause.depth-when-clause.simple-termp
                      clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                      clause.simple-termp-of-car-when-clause.simple-term-listp)
            (%disable default
                      type-set-like-rules
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      same-length-prefixes-equal-cheap
                      subsetp-when-prefixp-cheap
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      logic.formulap-when-logic.termp
                      logic.termp-when-logic.formulap)
            (%crewrite default)
            (%auto :strategy (cleanup split urewrite))
            (%enable default
                     lemma-2-for-clause.depth-of-clause.factor-strong)
            (%crewrite default)
            (%enable default
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     type-set-like-rules))

(%autoprove clause.depth-of-clause.factor-strong
            (%use (%instance (%thm lemma-for-clause.depth-of-clause.factor-strong)
                             (flag 'term))))

(%autoprove clause.depth-list-of-clause.factor-list-strong
            (%use (%instance (%thm lemma-for-clause.depth-of-clause.factor-strong)
                             (flag 'list))))



(%autoprove clause.depth-list-of-clause.unlifted-subterms-of-clause.casesplit
            (%clause.cases-induction cases assignment)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      same-length-prefixes-equal-cheap
                      type-set-like-rules
                      expensive-term/formula-inference
                      formula-decomposition
                      unusual-consp-rules)
            (%cheapen default
                      clause.depth-when-clause.simple-termp
                      clause.depth-list-when-clause.simple-term-listp
                      clause.simple-termp-when-memberp-of-clause.simple-term-listp
                      clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                      clause.simple-termp-of-car-when-clause.simple-term-listp))

(%autoprove lemma-for-clause.casesplit-strongly-reduces-clause.depth
            (%disable default
                      clause.unlifted-subterms-weakly-decreases-clause.depth
                      [outside]clause.unlifted-subterms-weakly-decreases-clause.depth
                      expensive-arithmetic-rules
                      type-set-like-rules)
            (%cheapen default
                      clause.depth-when-clause.simple-termp
                      clause.depth-list-when-clause.simple-term-listp
                      clause.simple-termp-when-memberp-of-clause.simple-term-listp
                      clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                      clause.simple-termp-of-car-when-clause.simple-term-listp)
            (%use (%instance (%thm clause.unlifted-subterms-weakly-decreases-clause.depth)
                             (x (clause.factor x assignment)))))

(%autoprove clause.casesplit-strongly-reduces-clause.depth
            (%clause.cases-induction cases assignment)
            (%disable default
                      type-set-like-rules
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      same-length-prefixes-equal-cheap
                      formula-decomposition
                      expensive-term/formula-inference
                      unusual-consp-rules)
            (%cheapen default
                      clause.depth-when-clause.simple-termp
                      clause.depth-list-when-clause.simple-term-listp
                      clause.simple-termp-when-memberp-of-clause.simple-term-listp
                      clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                      clause.simple-termp-of-car-when-clause.simple-term-listp)
            (%enable default lemma-for-clause.casesplit-strongly-reduces-clause.depth))

