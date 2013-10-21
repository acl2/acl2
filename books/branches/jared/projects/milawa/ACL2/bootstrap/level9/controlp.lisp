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
(include-book "theoryp")
(include-book "assmctrl")
(include-book "syntax-evaluator")
(%interactive)


(%defaggregate rw.control
  (noexec forcingp betamode theory defs depth assmctrl)
  :require ((logic.function-symbol-listp-of-rw.control->noexec  (logic.function-symbol-listp noexec))
            (booleanp-of-rw.control->forcingp                   (booleanp forcingp))
            (symbolp-of-rw.control->betamode                    (symbolp betamode))
            (rw.theoryp-of-rw.control->theory                   (rw.theoryp theory))
            (definition-listp-of-rw.control->defs               (definition-listp defs))
            (natp-of-rw.control->depth                          (natp depth))
            (rw.assmctrlp-of-rw.control->assmctrl               (rw.assmctrlp assmctrl))))


(defsection rw.control-atblp
  (%autoadmit rw.control-atblp)
  (local (%enable default rw.control-atblp))
  (%autoprove booleanp-of-rw.control-atblp)
  (%autoprove forcing-rw.control-atblp-of-rw.control)
  (%autoprove forcing-rw.theory-atblp-of-rw.control->theory)
  (%autoprove forcing-logic.formula-list-atblp-of-rw.control->defs))


(defsection rw.control-env-okp
  (%autoadmit rw.control-env-okp)
  (local (%enable default rw.control-env-okp))
  (%autoprove booleanp-of-rw.control-env-okp)
  (%autoprove forcing-rw.control-env-okp-of-rw.control)
  (%autoprove forcing-rw.theory-env-okp-of-rw.control->theory)
  (%autoprove forcing-subsetp-of-rw.control-defs-and-axioms))


(defsection rw.grounding-sigma-fragment
  (%autoadmit rw.grounding-sigma-fragment)
  (%autoprove rw.grounding-sigma-fragment-when-not-consp
              (%restrict default rw.grounding-sigma-fragment (equal x 'x)))
  (%autoprove rw.grounding-sigma-fragment-of-cons
              (%restrict default rw.grounding-sigma-fragment (equal x '(cons a x))))
  (%autoprove forcing-logic.sigmap-of-rw.grounding-sigma-fragment
              (%cdr-induction x))
  (%autoprove logic.sigma-atblp-of-rw.grounding-sigma-fragment
              (%cdr-induction x))
  (%autoprove logic.ground-listp-of-range-of-rw.grounding-sigma-fragment
              (%cdr-induction x))
  (%autoprove domain-of-rw.grounding-sigma-fragment
              (%cdr-induction x))
  (%autoprove rw.grounding-sigma-fragment-of-list-fix
              (%cdr-induction x))
  (%autoprove true-listp-of-rw.grounding-sigma-fragment
              (%cdr-induction x))
  (%autoprove rw.grounding-sigma-fragment-of-app
              (%cdr-induction x))
  (%autoprove rw.grounding-sigma-fragment-of-rev
              (%cdr-induction x))
  (%autoprove rev-of-rw.grounding-sigma-fragment
              (%cdr-induction x)))


(%autoadmit rw.aux-extend-grounding-sigma)

(%autoprove forcing-rw.aux-extend-grounding-sigma-removal
            (%autoinduct rw.aux-extend-grounding-sigma)
            (%restrict default rw.aux-extend-grounding-sigma (equal vars 'vars)))


(defsection rw.extend-grounding-sigma
  (%autoadmit rw.extend-grounding-sigma)
  (local (%enable default rw.extend-grounding-sigma))
  (local (%disable default
                   rw.grounding-sigma-fragment-when-not-consp
                   difference-when-not-consp
                   rev-when-not-consp
                   difference-when-subsetp))
  (%autoprove forcing-logic.sigmap-of-rw.extend-grounding-sigma)
  (%autoprove forcing-logic.sigma-atblp-of-rw.extend-grounding-sigma)
  (%autoprove forcing-logic.ground-listp-of-range-of-rw.extend-grounding-sigma)
  (%autoprove subsetp-of-logic.term-vars-and-domain-of-rw.extend-grounding-sigma
              (%enable default domain-of-rev [outside]domain-of-rev)
              (%disable default rev-of-domain [outside]rev-of-domain)))


(%autoadmit rw.aux-rule-syntax-okp)
(%autoadmit rw.rule-syntax-okp)

(%autoprove booleanp-of-rw.aux-rule-syntax-okp
            (%autoinduct rw.aux-rule-syntax-okp name terms partial-grounding-sigma defs depth)
            (%restrict default rw.aux-rule-syntax-okp (equal restrictions 'terms)))

(%autoprove booleanp-of-rw.rule-syntax-okp
            (%enable default rw.rule-syntax-okp))


(%ensure-exactly-these-rules-are-missing "../../rewrite/controlp")

