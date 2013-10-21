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
(include-book "clause-basics")
(%interactive)

(local (%enable default
                bust-up-logic.function-args-expensive
                bust-up-cdr-of-logic.function-args-expensive
                bust-up-cdr-of-cdr-of-logic.function-args-expensive))

(defsection clause.obvious-termp
  (%autoadmit clause.obvious-termp)
  (%autoprove booleanp-of-clause.obvious-termp
              (%enable default clause.obvious-termp)))

(defsection clause.obvious-term-bldr
  (%autoadmit clause.obvious-term-bldr)
  (local (%enable default
                  clause.obvious-term-bldr
                  clause.obvious-termp
                  clause.negative-termp
                  clause.negative-term-guts
                  logic.term-formula
                  theorem-if-redux-nil
                  definition-of-not))
  (%autoprove clause.obvious-term-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-clause.obvious-term-bldr)
  (%autoprove forcing-logic.conclusion-of-clause.obvious-term-bldr)
  (%autoprove forcing-logic.proofp-of-clause.obvious-term-bldr
              (%disable default forcing-lookup-of-logic.function-name-free)))

(defsection clause.find-obvious-term
  (%autoadmit clause.find-obvious-term)
  (%autoprove clause.find-obvious-term-when-not-consp
              (%restrict default clause.find-obvious-term (equal x 'x)))
  (%autoprove clause.find-obvious-term-of-cons
              (%restrict default clause.find-obvious-term (equal x '(cons a x))))
  (%autoprove clause.find-obvious-term-of-list-fix
              (%cdr-induction x))
  (%autoprove clause.find-obvious-term-of-app
              (%cdr-induction x))
  (%autoprove clause.find-obvious-term-of-rev-under-iff
              (%cdr-induction x))
  (%autoprove forcing-memberp-of-clause.find-obvious-term
              (%cdr-induction x))
  (%autoprove logic.termp-of-clause.find-obvious-term
              (%cdr-induction x))
  (%autoprove clause.obvious-termp-of-clause.find-obvious-term
              (%cdr-induction x)))

(defsection clause.remove-obvious-clauses
  (%autoadmit clause.remove-obvious-clauses)
  (%autoprove clause.remove-obvious-clauses-when-not-consp
              (%restrict default clause.remove-obvious-clauses (equal x 'x)))
  (%autoprove clause.remove-obvious-clauses-of-cons
              (%restrict default clause.remove-obvious-clauses (equal x '(cons a x))))
  (%autoprove true-listp-of-clause.remove-obvious-clauses
              (%cdr-induction x))
  (%autoprove clause.remove-obvious-clauses-of-list-fix
              (%cdr-induction x))
  (%autoprove clause.remove-obvious-clauses-of-app
              (%cdr-induction x))
  (%autoprove rev-of-clause.remove-obvious-clauses
              (%cdr-induction x))
  (%autoprove clause.remove-obvious-clauses-of-rev)
  (%autoprove subsetp-of-clause.remove-obvious-clauses
              (%cdr-induction x))
  (%autoprove forcing-logic.term-list-listp-of-clause.remove-obvious-clauses
              (%cdr-induction x))
  (%autoprove forcing-logic.term-list-list-atblp-of-clause.remove-obvious-clauses
              (%cdr-induction x))
  (%autoprove cons-listp-of-clause.remove-obvious-clauses
              (%cdr-induction x))
  (%autoprove all-superset-of-somep-of-clause.remove-obvious-clauses
              (%cdr-induction x)))

(defsection clause.remove-obvious-clauses-bldr
  (%autoadmit clause.remove-obvious-clauses-bldr)
  (local (%restrict default clause.remove-obvious-clauses-bldr (equal x 'x)))
  (%autoprove forcing-logic.appeal-listp-of-clause.remove-obvious-clauses-bldr
              (%autoinduct clause.remove-obvious-clauses-bldr))
  (%autoprove forcing-logic.strip-conclusions-of-clause.remove-obvious-clauses-bldr
              (%autoinduct clause.remove-obvious-clauses-bldr))
  (%autoprove forcing-logic.proof-listp-of-clause.remove-obvious-clauses-bldr
              (%autoinduct clause.remove-obvious-clauses-bldr)))

(defsection clause.obvious-term-bldr-okp
  (%autoadmit clause.obvious-term-bldr-okp)
  (local (%enable default clause.obvious-term-bldr-okp logic.term-formula))
  (%autoprove booleanp-of-clause.obvious-term-bldr-okp)
  (%autoprove clause.obvious-term-bldr-okp-of-logic.appeal-identity)
  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free))
  (%autoprove lemma-1-for-soundness-of-clause.obvious-term-bldr-okp)
  (%autoprove lemma-2-for-soundness-of-clause.obvious-term-bldr-okp)
  (%autoprove forcing-soundness-of-clause.obvious-term-bldr-okp
              (%use (%instance (%thm lemma-1-for-soundness-of-clause.obvious-term-bldr-okp)))
              (%use (%instance (%thm lemma-2-for-soundness-of-clause.obvious-term-bldr-okp)))
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (clause.obvious-term-bldr (logic.=lhs (logic.~arg (logic.conclusion x)))))))
              (%forcingp nil)))

