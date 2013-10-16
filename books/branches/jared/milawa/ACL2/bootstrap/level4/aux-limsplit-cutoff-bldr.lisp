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



(%autoadmit clause.aux-limsplit-cutoff-bldr)

(%autoprove clause.aux-limsplit-cutoff-bldr-under-iff
            (%autoinduct clause.aux-limsplit-cutoff-bldr)
            (%restrict default clause.aux-limsplit-cutoff-bldr (equal as 'as)))

(%autoprove forcing-logic.appealp-of-clause.aux-limsplit-cutoff-bldr
            (%autoinduct clause.aux-limsplit-cutoff-bldr)
            (%restrict default clause.aux-limsplit-cutoff-bldr (equal as 'as)))

(%autoprove lemma-for-forcing-logic.conclusion-of-clause.aux-limsplit-cutoff-bldr
            (%cdr-induction a)
            (%forcingp nil))

(%autoprove forcing-logic.conclusion-of-clause.aux-limsplit-cutoff-bldr
            (%autoinduct clause.aux-limsplit-cutoff-bldr)
            (%restrict default clause.aux-limsplit-cutoff-bldr (equal as 'as))
            (%enable default lemma-for-forcing-logic.conclusion-of-clause.aux-limsplit-cutoff-bldr)
            (%disable default ;; these seem to be causing loops
                      forcing-logic.vlhs-of-logic.disjoin-formulas-free
                      forcing-logic.vrhs-of-logic.disjoin-formulas-free)
            (%auto :strategy (cleanup split urewrite crewrite dist)) ;; suppress elim
            (%enable default ;; that's weird.  i seem to need them now.
                     forcing-logic.vlhs-of-logic.disjoin-formulas-free
                     forcing-logic.vrhs-of-logic.disjoin-formulas-free))

(%autoprove forcing-logic.proofp-of-clause.aux-limsplit-cutoff-bldr
            (%autoinduct clause.aux-limsplit-cutoff-bldr)
            (%restrict default clause.aux-limsplit-cutoff-bldr (equal as 'as)))




(%autoadmit clause.limsplit-cutoff-bldr)

(%autoprove forcing-logic.appealp-of-clause.limsplit-cutoff-bldr
            (%enable default
                     clause.limsplit-cutoff-bldr
                     build.rev-disjunction))

(%autoprove forcing-logic.conclusion-of-clause.limsplit-cutoff-bldr
            (%enable default
                     clause.limsplit-cutoff-bldr
                     build.rev-disjunction))

(%autoprove forcing-logic.proofp-of-clause.limsplit-cutoff-bldr
            (%enable default
                     clause.limsplit-cutoff-bldr
                     build.rev-disjunction))




(%autoadmit clause.aux-split-goal)

(%autoprove clause.aux-split-goal-when-not-consp-of-todo
            (%enable default clause.aux-split-goal))



(%autoadmit clause.limsplit-cutoff-bldr-nice)

(%autoprove forcing-logic.appealp-of-clause.limsplit-cutoff-bldr-nice
            (%enable default clause.limsplit-cutoff-bldr-nice))

(%autoprove forcing-logic.conclusion-of-clause.limsplit-cutoff-bldr-nice
            (%enable default
                     clause.limsplit-cutoff-bldr-nice
                     clause.aux-split-goal))

(%autoprove forcing-logic.proofp-of-clause.limsplit-cutoff-bldr-nice
            (%enable default clause.limsplit-cutoff-bldr-nice))






(%autoadmit clause.limsplit-cutoff-bldr-nice-okp)

(%autoadmit clause.limsplit-cutoff-bldr-nice-high)

(encapsulate
 ()
 (local (%enable default
                 clause.limsplit-cutoff-bldr-nice-okp
                 clause.limsplit-cutoff-bldr-nice-high))

 (%autoprove booleanp-of-clause.limsplit-cutoff-bldr-nice-okp)

 (%autoprove clause.limsplit-cutoff-bldr-nice-okp-of-logic.appeal-identity)

 (%autoprove lemma-1-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp)

 (%autoprove lemma-2-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp)

 (%autoprove forcing-soundness-of-clause.limsplit-cutoff-bldr-nice-okp
             (%enable default
                      lemma-1-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp
                      lemma-2-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp)
             (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                              (x (clause.limsplit-cutoff-bldr-nice (first (logic.extras x))
                                                                   (second (logic.extras x))
                                                                   (logic.provable-witness (logic.conclusion (first (logic.subproofs x)))
                                                                                           axioms thms atbl)))))))


