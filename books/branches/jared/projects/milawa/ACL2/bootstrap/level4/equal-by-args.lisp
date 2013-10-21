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


(%autoadmit build.pequal-from-equal-list)

(%autoprove len-of-build.pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.appeal-listp-of-build.pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-build.pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-build.pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.pequal-from-equal-list (equal x 'x)))





(%autoadmit build.disjoined-pequal-from-equal-list)

(%autoprove len-of-build.disjoined-pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.disjoined-pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.appeal-listp-of-build.disjoined-pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.disjoined-pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-build.disjoined-pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.disjoined-pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-build.disjoined-pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.disjoined-pequal-from-equal-list (equal x 'x)))




(%autoadmit build.equal-by-args)

(encapsulate
 ()
 (local (%enable default build.equal-by-args axiom-equal-when-same))
 (%autoprove build.equal-by-args-under-iff)
 (%autoprove forcing-logic.appealp-of-build.equal-by-args)
 (%autoprove forcing-logic.conclusion-of-build.equal-by-args)
 (%autoprove forcing-logic.proofp-of-build.equal-by-args))



(%autoadmit build.disjoined-equal-by-args)

(encapsulate
 ()
 (local (%enable default build.disjoined-equal-by-args axiom-equal-when-same))
 (%autoprove build.disjoined-equal-by-args-under-iff)
 (%autoprove forcing-logic.appealp-of-build.disjoined-equal-by-args)
 (%autoprove forcing-logic.conclusion-of-build.disjoined-equal-by-args)
 (%autoprove forcing-logic.proofp-of-build.disjoined-equal-by-args))




(%autoadmit build.equal-by-args-aux-okp)

(%autoprove build.equal-by-args-aux-okp-removal
            (%autoinduct build.equal-by-args-aux-okp)
            (%splitlimit 8)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default build.equal-by-args-aux-okp (equal proofs 'proofs)))

(%autoadmit build.equal-by-args-okp)

(%autoprove booleanp-of-build.equal-by-args-aux-okp
            (%autoinduct build.equal-by-args-aux-okp)
            (%splitlimit 8)
            (%restrict default build.equal-by-args-aux-okp (equal proofs 'proofs)))

(%autoprove booleanp-of-build.equal-by-args-okp
            (%enable default build.equal-by-args-okp))

(%autoprove build.equal-by-args-okp-of-logic.appeal-identity
            (%enable default build.equal-by-args-okp))

(%autoprove lemma-1-for-soundness-of-build.equal-by-args-okp
            (%enable default build.equal-by-args-okp))

(%autoprove lemma-2-for-soundness-of-build.equal-by-args-okp
            (%enable default build.equal-by-args-okp))

(%autoprove lemma-3-for-soundness-of-build.equal-by-args-okp
            (%enable default build.equal-by-args-okp))

(%autoprove forcing-soundness-of-build.equal-by-args-okp
            (%enable default
                     lemma-1-for-soundness-of-build.equal-by-args-okp
                     lemma-2-for-soundness-of-build.equal-by-args-okp
                     lemma-3-for-soundness-of-build.equal-by-args-okp)
            (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                             (x (build.equal-by-args (logic.function-name (first (logic.function-args (logic.=lhs (logic.conclusion x)))))
                                                     (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                                  axioms thms atbl))))))




(%autoadmit build.disjoined-equal-by-args-aux-okp)

(%autoprove build.disjoined-equal-by-args-aux-okp-removal
            (%autoinduct build.disjoined-equal-by-args-aux-okp)
            (%splitlimit 8)
            (%disable default
                      trichotomy-of-<
                      antisymmetry-of-<
                      not-equal-when-less
                      not-equal-when-less-two
                      logic.termp-when-logic.formulap
                      logic.formulap-when-logic.termp
                      same-length-prefixes-equal-cheap
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots)
            (%disable default logic.vlhs-of-logic.conclusion-of-car-when-all-equalp)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default build.disjoined-equal-by-args-aux-okp (equal proofs 'proofs)))

(%autoadmit build.disjoined-equal-by-args-okp)

(%autoprove booleanp-of-build.disjoined-equal-by-args-aux-okp
            (%autoinduct build.disjoined-equal-by-args-aux-okp)
            (%splitlimit 8)
            (%restrict default build.disjoined-equal-by-args-aux-okp (equal proofs 'proofs)))

(%autoprove booleanp-of-build.disjoined-equal-by-args-okp
            (%enable default build.disjoined-equal-by-args-okp))

(%autoprove build.disjoined-equal-by-args-okp-of-logic.appeal-identity
            (%enable default build.disjoined-equal-by-args-okp))

(%autoprove lemma-1-for-soundness-of-build.disjoined-equal-by-args-okp
            (%enable default build.disjoined-equal-by-args-okp)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots))

(%autoprove lemma-2-for-soundness-of-build.disjoined-equal-by-args-okp
            (%enable default build.disjoined-equal-by-args-okp)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots))

(%autoprove lemma-3-for-soundness-of-build.disjoined-equal-by-args-okp
            (%enable default build.disjoined-equal-by-args-okp)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots))

(%autoprove forcing-soundness-of-build.disjoined-equal-by-args-okp
            (%enable default
                     lemma-1-for-soundness-of-build.disjoined-equal-by-args-okp
                     lemma-2-for-soundness-of-build.disjoined-equal-by-args-okp
                     lemma-3-for-soundness-of-build.disjoined-equal-by-args-okp)
            (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                             (x (build.disjoined-equal-by-args
                                 (logic.function-name (first (logic.function-args (logic.=lhs (logic.vrhs (logic.conclusion x))))))
                                 (logic.vlhs (logic.conclusion x))
                                 (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                              axioms thms atbl))))))
