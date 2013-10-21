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
(include-book "limlift")
(include-book "casesplit-bldr")
(%interactive)

(%autoadmit clause.limlift-term1-bldr)

(%autoprove cdr-of-clause.limlift-term1-bldr
            (%autoinduct clause.limlift-term1-bldr x k)
            (%restrict default clause.limlift-term1-bldr (equal x 'x))
            (%restrict default clause.limlift-term1 (equal x 'x)))


(defthm lemma-for-forcing-logic.appealp-of-car-of-clause.limlift-term1-bldr
  ;; BOZO it's local
  (implies (logic.termp x)
           (and (logic.appealp (car (clause.limlift-term1-bldr x k)))
                (equal (logic.conclusion (car (clause.limlift-term1-bldr x k)))
                       (logic.pequal x (car (clause.limlift-term1 x k))))))
  :rule-classes nil)

(%autoprove lemma-for-forcing-logic.appealp-of-car-of-clause.limlift-term1-bldr
            (%autoinduct clause.limlift-term1-bldr x k)
            (%restrict default clause.limlift-term1-bldr (equal x 'x))
            (%restrict default clause.limlift-term1 (equal x 'x))
            (%disable default
                      clause.simple-termp-openers
                      clause.lifted-termp-openers
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      same-length-prefixes-equal-cheap
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      logic.termp-when-logic.formulap))

(%autoprove forcing-logic.appealp-of-car-of-clause.limlift-term1-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-car-of-clause.limlift-term1-bldr)
                             (flag 'term))))

(%autoprove forcing-logic.conclusion-of-car-of-clause.limlift-term1-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-car-of-clause.limlift-term1-bldr)
                             (flag 'list))))

(%autoprove forcing-logic.proofp-of-car-of-clause.limlift-term1-bldr
            (%autoinduct clause.limlift-term1-bldr x k)
            (%restrict default clause.limlift-term1-bldr (equal x 'x))
            (%restrict default clause.limlift-term1 (equal x 'x))
            (%disable default
                      clause.simple-termp-openers
                      clause.lifted-termp-openers
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      same-length-prefixes-equal-cheap
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      logic.termp-when-logic.formulap))



(%autoadmit clause.limlift-term-bldr)

(defthm lemma-for-forcing-logic.appealp-of-clause.limlift-term-bldr
  ;; BOZO local in the file.
  (implies (logic.termp x)
           (and (logic.appealp (clause.limlift-term-bldr x k))
                (equal (logic.conclusion (clause.limlift-term-bldr x k))
                       (logic.pequal x (clause.limlift-term x k)))))
  :rule-classes nil)

(%autoprove lemma-for-forcing-logic.appealp-of-clause.limlift-term-bldr
            (%autoinduct clause.limlift-term x k)
            (%restrict default clause.limlift-term (equal x 'x))
            (%restrict default clause.limlift-term-bldr (equal x 'x)))

(%autoprove forcing-logic.appealp-of-clause.limlift-term-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.limlift-term-bldr))))

(%autoprove forcing-logic.conclusion-of-clause.limlift-term-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.limlift-term-bldr))))

(%autoprove forcing-logic.proofp-of-clause.limlift-term-bldr
            (%autoinduct clause.limlift-term x k)
            (%restrict default clause.limlift-term (equal x 'x))
            (%restrict default clause.limlift-term-bldr (equal x 'x)))



(%defprojection :list (clause.limlift-term-list-bldr x k)
                :element (clause.limlift-term-bldr x k))

(%autoprove forcing-logic.appeal-listp-of-clause.limlift-term-list-bldr
            (%cdr-induction x))

(%autoprove forcing-logic.strip-conclusions-of-clause.limlift-term-list-bldr
            (%cdr-induction x))

(%autoprove forcing-logic.proof-listp-of-clause.limlift-term-list-bldr
            (%cdr-induction x))



(%autoadmit clause.limlift-clauses-bldr)

(%autoprove forcing-logic.appeal-listp-of-clause.limlift-clauses-bldr
            (%autoinduct clause.limlift-clauses-bldr)
            (%restrict default clause.limlift-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-clause.limlift-clauses-bldr
            (%autoinduct clause.limlift-clauses-bldr)
            (%restrict default clause.limlift-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-clause.limlift-clauses-bldr
            (%autoinduct clause.limlift-clauses-bldr)
            (%restrict default clause.limlift-clauses-bldr (equal x 'x)))

