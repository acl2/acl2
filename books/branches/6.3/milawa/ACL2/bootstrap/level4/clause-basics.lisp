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
(include-book "pequal-list")
(%interactive)

(local (%enable default
                bust-up-logic.function-args-expensive
                bust-up-cdr-of-logic.function-args-expensive
                bust-up-cdr-of-cdr-of-logic.function-args-expensive))

(%autoadmit clause.clause-formula)

(%autoprove redefinition-of-clause.clause-formula
            (%cdr-induction x)
            (%restrict default clause.clause-formula (equal x 'x))
            (%forcingp nil))

(%autoadmit clause.clause-list-formulas)

(%autoprove redefinition-of-clause.clause-list-formulas
            (%cdr-induction x)
            (%restrict default clause.clause-list-formulas (equal x 'x)))

(%autoadmit clause.negative-termp)

(%autoprove booleanp-of-clause.negative-termp
            (%enable default clause.negative-termp)
            (%forcingp nil))

(%autoprove clause.negative-termp-of-logic.function-of-not
            (%enable default clause.negative-termp)
            (%forcingp nil))

(%autoprove logic.functionp-when-clause.negative-termp
            (%enable default clause.negative-termp))

(%enable expensive-term/formula-inference
         logic.functionp-when-clause.negative-termp)



(%autoadmit clause.negative-term-guts)

(%autoprove forcing-logic.termp-of-clause.negative-term-guts
            (%enable default clause.negative-termp clause.negative-term-guts))

(%autoprove forcing-logic.term-atblp-of-clause.negative-term-guts
            (%enable default clause.negative-termp clause.negative-term-guts))

(%autoprove clause.negative-term-guts-of-logic.function-of-not
            (%enable default clause.negative-term-guts))

(%autoprove rank-of-clause.negative-term-guts-when-clause.negative-termp
            (%enable default
                     clause.negative-term-guts
                     clause.negative-termp
                     logic.function-args))

(%autoprove rank-of-clause.negative-term-guts-of-clause.negative-term-guts
            (%disable default rank-of-clause.negative-term-guts-when-clause.negative-termp)
            (%use (%instance (%thm rank-of-clause.negative-term-guts-when-clause.negative-termp)
                             (x (clause.negative-term-guts x))))
            (%use (%instance (%thm rank-of-clause.negative-term-guts-when-clause.negative-termp))))



(%autoadmit clause.term-guts)

(%autoprove forcing-logic.termp-of-clause.term-guts
            (%enable default clause.term-guts))

(%autoprove forcing-logic.term-atblp-of-clause.term-guts
            (%enable default clause.term-guts))



(%defprojection :list (clause.term-list-guts x)
                :element (clause.term-guts x)
                :nil-preservingp t)

(%autoprove forcing-logic.term-listp-of-clause.term-list-guts
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-clause.term-list-guts
            (%cdr-induction x))



(%autoadmit definition-of-not)
(%noexec definition-of-not)

(%defderiv clause.substitute-iff-into-literal-bldr)

(encapsulate
 ()
 ;; previously 1.7 BN
 (local (%max-proof-size 1000000000))
 (%defderiv clause.disjoined-substitute-iff-into-literal-bldr))


(%deftheorem clause.theorem-standardize-equal-x-nil)
(%deftheorem clause.theorem-standardize-equal-nil-x)
(%deftheorem clause.theorem-standardize-iff-x-nil)
(%deftheorem clause.theorem-standardize-iff-nil-x)


(defsection clause.standardize-negative-term-bldr
  (%autoadmit clause.standardize-negative-term-bldr)
  (local (%enable default
                  clause.standardize-negative-term-bldr
                  clause.negative-termp
                  clause.negative-term-guts
                  definition-of-not
                  clause.theorem-standardize-equal-nil-x
                  clause.theorem-standardize-equal-x-nil
                  clause.theorem-standardize-iff-nil-x
                  clause.theorem-standardize-iff-x-nil))
  (%autoprove forcing-logic.appealp-of-clause.standardize-negative-term-bldr)
  (%autoprove forcing-logic.conclusion-of-clause.standardize-negative-term-bldr)
  (%autoprove forcing-logic.proofp-of-clause.standardize-negative-term-bldr))

(defsection clause.standardize-negative-term-bldr-okp
  (%autoadmit clause.standardize-negative-term-bldr-okp)
  (local (%enable default clause.standardize-negative-term-bldr-okp))
  (%autoprove booleanp-of-clause.standardize-negative-term-bldr-okp)
  (%autoprove clause.standardize-negative-term-bldr-okp-of-logic.appeal-identity)
  (%autoprove lemma-1-for-soundness-of-clause.standardize-negative-term-bldr-okp)
  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free))
  (%autoprove lemma-2-for-soundness-of-clause.standardize-negative-term-bldr-okp)
  (%autoprove forcing-soundness-of-clause.standardize-negative-term-bldr-okp
              (%enable default
                       lemma-1-for-soundness-of-clause.standardize-negative-term-bldr-okp
                       lemma-2-for-soundness-of-clause.standardize-negative-term-bldr-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (clause.standardize-negative-term-bldr (logic.=lhs (logic.conclusion x))))))))

(defsection clause.standardize-double-negative-term-bldr
  (%autoadmit clause.standardize-double-negative-term-bldr)
  (local (%enable default clause.standardize-double-negative-term-bldr))
  (%autoprove forcing-logic.appealp-of-clause.standardize-double-negative-term-bldr)
  (%autoprove forcing-logic.conclusion-of-clause.standardize-double-negative-term-bldr)
  (%autoprove forcing-logic.proofp-of-clause.standardize-double-negative-term-bldr))

(defsection clause.standardize-double-negative-term-bldr-okp
  (%autoadmit clause.standardize-double-negative-term-bldr-okp)
  (local (%enable default clause.standardize-double-negative-term-bldr-okp))
  (%autoprove booleanp-of-clause.standardize-double-negative-term-bldr-okp)
  (%autoprove clause.standardize-double-negative-term-bldr-okp-of-logic.appeal-identity)
  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free))
  (%autoprove lemma-1-for-soundness-of-clause.standardize-double-negative-term-bldr-okp)
  (%autoprove lemma-2-for-soundness-of-clause.standardize-double-negative-term-bldr-okp)
  (%autoprove forcing-soundness-of-clause.standardize-double-negative-term-bldr-okp
              (%enable default
                       lemma-1-for-soundness-of-clause.standardize-double-negative-term-bldr-okp
                       lemma-2-for-soundness-of-clause.standardize-double-negative-term-bldr-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (clause.standardize-double-negative-term-bldr (logic.=lhs (logic.conclusion x))))))))





