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


(%autoadmit rw.force-modep)

(%autoprove booleanp-of-rw.force-modep
            (%enable default rw.force-modep))

(%defaggregate rw.hyp
  (term fmode limitp limit)
  :require ((logic.termp-of-rw.hyp->term     (logic.termp term))
            (rw.force-modep-of-rw.hyp->fmode (rw.force-modep fmode))
            (booleanp-of-rw.hyp->limitp      (booleanp limitp))
            (natp-of-rw.hyp->limit           (natp limit))))

(%deflist rw.hyp-listp (x)
  (rw.hypp x))



(%autoadmit rw.hyp-atblp)
(%autoprove booleanp-of-rw.hyp-atblp
            (%enable default rw.hyp-atblp))
(%autoprove forcing-logic.term-atblp-of-rw.hyp
            (%enable default rw.hyp-atblp))
(%autoprove rw.hyp-atblp-of-rw.hyp
            (%enable default rw.hyp-atblp))
(%autoprove rw.hyp-atblp-of-nil
            (%enable default rw.hyp-atblp))

(%deflist rw.hyp-list-atblp (x atbl)
  (rw.hyp-atblp x atbl))


(%defprojection :list (rw.hyp-list-terms x)
                :element (rw.hyp->term x))
(%autoprove forcing-logic.term-listp-of-rw.hyp-list-terms
            (%cdr-induction x))
(%autoprove forcing-logic.term-list-atblp-of-rw.hyp-list-terms
            (%cdr-induction x))


(%defaggregate rw.rule
  (name type hyps equiv lhs rhs syntax crithyps)
  :require ((symbolp-of-rw.rule->name                (symbolp name))
            (symbolp-of-rw.rule->type                (symbolp type))
            (rw.hyp-listp-of-rw.rule->hyps           (rw.hyp-listp hyps))
            (logic.function-namep-of-rw.rule->equiv  (logic.function-namep equiv))
            (logic.termp-of-rw.rule->lhs             (logic.termp lhs))
            (logic.termp-of-rw.rule->rhs             (logic.termp rhs))
            (logic.term-listp-of-rw.rule->syntax     (logic.term-listp syntax))
            (subsetp-of-rw.rule->crithyps            (logic.term-listp crithyps))))

(%deflist rw.rule-listp (x)
  (rw.rulep x))

(%deflist rw.rule-list-listp (x)
  (rw.rule-listp x))

(%autoprove forcing-rw.rule-listp-of-simple-flatten
            (%cdr-induction x))


(%autoadmit rw.rule-atblp)

(%autoprove rw.rule-atblp-of-nil
            (%enable default rw.rule-atblp))
(%autoprove booleanp-of-rw.rule-atblp
            (%enable default rw.rule-atblp))
(%autoprove forcing-rw.hyp-list-atblp-of-rw.rule->hyps
            (%enable default rw.rule-atblp))
(%autoprove forcing-logic.term-atblp-of-rw.rule->lhs
            (%enable default rw.rule-atblp))
(%autoprove forcing-logic.term-atblp-of-rw.rule->rhs
            (%enable default rw.rule-atblp))
(%autoprove forcing-logic.term-list-atblp-of-rw.rule->crithyps
            (%enable default rw.rule-atblp))
(%autoprove forcing-lookup-of-rw.rule-equiv
            (%forcingp nil)
            (%enable default rw.rule-atblp))
(%autoprove forcing-rw.rule-atblp-of-rw.rule
            (%enable default rw.rule-atblp))


(%deflist rw.rule-list-atblp (x atbl)
  (rw.rule-atblp x atbl))

(%deflist rw.rule-list-list-atblp (x atbl)
  (rw.rule-list-atblp x atbl))



(%autoadmit rw.rule-clause)
(%autoprove consp-of-rw.rule-clause
            (%enable default rw.rule-clause))
(%autoprove forcing-logic.term-listp-of-rw.rule-clause
            (%enable default rw.rule-clause))
(%autoprove forcing-logic.term-list-atbp-of-rw.rule-clause
            (%enable default rw.rule-clause))
(%autoprove forcing-rw.rule-clause-when-no-hyps
            (%forcingp nil)
            (%enable default rw.rule-clause))


(%defprojection :list (rw.rule-list-clauses x)
                :element (rw.rule-clause x))
(%autoprove cons-listp-of-rw.rule-list-clauses
            (%cdr-induction x))
(%autoprove forcing-logic.term-list-listp-of-rw.rule-list-clauses
            (%cdr-induction x))
(%autoprove forcing-logic.term-list-list-atbp-of-rw.rule-list-clauses
            (%cdr-induction x))


(%defprojection :list (rw.rule-list-lhses x)
                :element (rw.rule->lhs x))
(%autoprove forcing-logic.term-listp-of-rw.rule-list-lhses
            (%cdr-induction x))
(%autoprove forcing-logic.term-list-atblp-of-rw.rule-list-lhses
            (%cdr-induction x))


(%defprojection :list (rw.rule-list-names x)
                :element (rw.rule->name x))
(%autoprove forcing-symbol-listp-of-rw.rule-list-names
            (%cdr-induction x))


(%autoadmit rw.rule-env-okp)
(%autoprove booleanp-of-rw.rule-env-okp
            (%enable default rw.rule-env-okp))


(%deflist rw.rule-list-env-okp (x thms)
  (rw.rule-env-okp x thms))

(%deflist rw.rule-list-list-env-okp (x thms)
  (rw.rule-list-env-okp x thms))




(%autoadmit rw.rule-list-lookup)

(%autoprove rw.rule-list-lookup-when-not-consp
            (%restrict default rw.rule-list-lookup (equal rules 'rules)))

(%autoprove rw.rule-list-lookup-of-cons
            (%restrict default rw.rule-list-lookup (equal rules '(cons rule rules))))

(%autoprove rw.rulep-of-rw.rule-list-lookup
            (%cdr-induction rules))

(%autoprove rw.rule-atblp-of-rw.rule-list-lookup
            (%cdr-induction rules))

(%autoprove rw.rule-env-okp-of-rw.rule-list-lookup
            (%cdr-induction rules))

(%autoprove rw.rule-list-atblp-of-cdr-of-lookup
            (%cdr-induction map))

(%autoprove rw.rule-list-env-okp-of-cdr-of-lookup
            (%cdr-induction map))


(%ensure-exactly-these-rules-are-missing "../../rewrite/rulep")

