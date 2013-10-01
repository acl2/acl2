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
(include-book "depth-3-special")
(%interactive)

(%autoprove lemma-for-consp-of-clause.simple-tests
            (%clause.simple-term-induction flag x)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules))

(%autoprove consp-of-clause.simple-tests
            (%use (%instance (%thm lemma-for-consp-of-clause.simple-tests)
                             (flag 'term))))

(%autoprove consp-of-clause.simple-tests-list
            (%use (%instance (%thm lemma-for-consp-of-clause.simple-tests)
                             (flag 'list))))


(%autoprove lemma-for-clause.simple-tests-when-not-clause.simple-termp-under-iff
            (%clause.simple-term-induction flag x)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules))

(%autoprove clause.simple-tests-when-not-clause.simple-termp-under-iff
            (%use (%instance (%thm lemma-for-clause.simple-tests-when-not-clause.simple-termp-under-iff)
                             (flag 'term))))

(%autoprove clause.simple-tests-list-when-not-clause.simple-term-listp-under-iff
            (%use (%instance (%thm lemma-for-clause.simple-tests-when-not-clause.simple-termp-under-iff)
                             (flag 'list))))



(%autoprove forcing-logic.term-listp-of-firstn)

(%autoprove forcing-logic.term-list-atblp-of-firstn)





(%autoadmit clause.limlift-term1)

(%autoprove forcing-logic.termp-of-car-of-clause.limlift-term1
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove forcing-natp-of-cdr-of-clause.limlift-term1
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-car-of-clause.lift1
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove car-of-clause.lift1-when-clause.lifted-termp
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove cdr-of-clause.lift1-when-clause.lifted-termp
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove cdr-of-clause.limlift-term1-never-increases
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove cdr-of-clause.limlift-term1-stays-at-zero
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove cdr-of-clause.limlift-term1-usually-decreases
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))





(%autoadmit clause.limlift-term)

(%autoprove forcing-logic.termp-of-clause.limlift-term
            (%autoinduct clause.limlift-term x k)
            (%restrict default clause.limlift-term (equal k 'k)))

(%autoprove forcing-logic.term-atblp-of-clause.limlift-term
            (%autoinduct clause.limlift-term x k)
            (%restrict default clause.limlift-term (equal k 'k)))

(%autoprove clause.limlift-term-when-clause.simple-termp
            (%autoinduct clause.limlift-term x k)
            (%restrict default clause.limlift-term (equal k 'k)))



(%defprojection :list (clause.limlift-term-list x k)
                :element (clause.limlift-term x k))

(%autoprove forcing-logic.term-listp-of-clause.limlift-term-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-clause.limlift-term-list
            (%cdr-induction x))

(%autoprove clause.limlift-term-list-when-clause.simple-term-listp
            (%cdr-induction x))



(%defprojection :list (clause.limlift-term-list-list x k)
                :element (clause.limlift-term-list x k))

(%autoprove forcing-logic.term-list-listp-of-clause.limlift-term-list-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-clause.limlift-term-list-list
            (%cdr-induction x))

(%autoprove clause.limlift-term-list-list-when-clause.simple-term-list-listp
            (%cdr-induction x))

(%autoprove cons-listp-of-clause.limlift-term-list-list
            (%cdr-induction x))
