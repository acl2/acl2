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
(include-book "depth-2-deepest")
(%interactive)

(%autoadmit clause.special-assignment)

(%autoprove clause.special-assignment-when-not-consp
            (%restrict default clause.special-assignment (equal assignments 'assignments)))

(%autoprove clause.special-assignment-of-cons
            (%restrict default clause.special-assignment (equal assignments '(cons a assignments))))

(%autoprove memberp-of-clause.special-assignment
            (%cdr-induction assignments))

(%autoprove forcing-logic.termp-of-clause.deepest
            (%cdr-induction x))

(%autoprove clause.special-assignment-of-clause.multifactor
            (%cdr-induction assignments)
            (%enable default clause.depth-list-redefinition)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      same-length-prefixes-equal-cheap)
            (%cheapen default
                      clause.depth-when-clause.simple-termp
                      clause.depth-list-when-clause.simple-term-listp
                      clause.simple-termp-when-memberp-of-clause.simple-term-listp
                      clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                      clause.simple-termp-of-car-when-clause.simple-term-listp)
            (%auto)
            (%enable default
                     expensive-arithmetic-rules-two
                     expensive-arithmetic-rules
                     type-set-like-rules))



(%autoadmit clause.deepest-after-factoring)

(%autoprove clause.deepest-after-factoring-when-not-consp
            (%restrict default clause.deepest-after-factoring (equal x 'x)))

(%autoprove clause.deepest-after-factoring-of-cons
            (%restrict default clause.deepest-after-factoring (equal x '(cons a x))))

(%autoprove forcing-logic.termp-of-clause.deepest-after-factoring
            (%cdr-induction x))

(%autoprove memberp-of-clause.deepest-after-factoring
            (%cdr-induction x))

(%autoprove clause.deepest-of-clause.factor-list
            (%cdr-induction x)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules))

(%autoprove disjoint-from-nonep-of-clause.term-paths-of-clause.deepest-after-factoring
            (%disable default disjoint-from-nonep-of-clause.term-paths-when-memberp)
            (%use (%instance (%thm disjoint-from-nonep-of-clause.term-paths-when-memberp)
                             (a (clause.deepest-after-factoring x assignment))
                             (x x))))


(%ensure-exactly-these-rules-are-missing "../../clauses/if-lifting/depth")
