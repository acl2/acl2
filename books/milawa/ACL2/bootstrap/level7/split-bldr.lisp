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
(include-book "split")
(include-book "lift-bldr")
(include-book "limlift-bldr")
(%interactive)


(%autoadmit clause.split-bldr)

(%autoprove forcing-logic.appealp-of-clause.split-bldr
            (%enable default clause.split clause.split-bldr build.rev-disjunction))

(%autoprove forcing-logic.conclusion-of-clause.split-bldr
            (%enable default clause.split clause.split-bldr build.rev-disjunction))

(%autoprove forcing-logic.proofp-of-clause.split-bldr
            (%enable default clause.split clause.split-bldr build.rev-disjunction))


(%deflist logic.appeal-list-listp (x)
          (logic.appeal-listp x))

(%defprojection :list (logic.strip-conclusions-list x)
                :element (logic.strip-conclusions x))

(encapsulate
 ()
 (local (%disable default redefinition-of-clause.clause-list-formulas
                  [OUTSIDE]REDEFINITION-OF-CLAUSE.CLAUSE-LIST-FORMULAS))
 (%defprojection :list (clause.clause-list-list-formulas x)
                 :element (clause.clause-list-formulas x)))

(%deflist logic.proof-list-listp (x axioms thms atbl)
  (logic.proof-listp x axioms thms atbl))


(%autoadmit clause.split-list-bldr)

(%autoprove forcing-logic.appeal-listp-of-clause.split-list-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.split-list (equal x 'x))
            (%restrict default clause.split-list-bldr (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-clause.split-list-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.split-list (equal x 'x))
            (%restrict default clause.split-list-bldr (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-clause.split-list-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.split-list (equal x 'x))
            (%restrict default clause.split-list-bldr (equal x 'x))
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules
                      memberp-when-memberp-of-cdr))



(%autoadmit clause.split-bldr-okp)

(%autoadmit clause.split-bldr-high)

(encapsulate
 ()
 (local (%enable default clause.split-bldr-okp))
 (%autoprove booleanp-of-clause.split-bldr-okp)
 (%autoprove clause.split-bldr-okp-of-logic.appeal-identity)
 (%autoprove lemma-1-for-soundness-of-clause.split-bldr-okp)
 (%autoprove lemma-2-for-soundness-of-clause.split-bldr-okp)
 (%autoprove forcing-soundness-of-clause.split-bldr-okp
             (%enable default
                      lemma-1-for-soundness-of-clause.split-bldr-okp
                      lemma-2-for-soundness-of-clause.split-bldr-okp)
             (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                              (x (clause.split-bldr (first (logic.extras x))
                                                    (second (logic.extras x))
                                                    (third (logic.extras x))
                                                    (fourth (logic.extras x))
                                                    (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                                 axioms thms atbl)))))))
