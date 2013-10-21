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
(include-book "prop")
(include-book "pequal")
(include-book "equal")
(include-book "iff")
(include-book "if")
(include-book "not")
(include-book "disjoined-update-clause-bldr")
(%interactive)


(%autoadmit level3.step-okp)

(encapsulate
 ()
 (local (%enable default level3.step-okp))
 (%autoprove soundness-of-level3.step-okp)
 ;; BOZO we might want this to be when level2-step-okp instead
 (%autoprove level3.step-okp-when-level2.step-okp
             (%enable default level2.step-okp logic.appeal-step-okp)
             (%auto :strategy (cleanup split urewrite)))
 (%autoprove level3.step-okp-when-not-consp
             (%enable default logic.method)))

(encapsulate
 ()
 (local (%disable default forcing-true-listp-of-logic.subproofs))
 (%autoadmit level3.flag-proofp-aux))

(%autoadmit level3.proofp-aux)
(%autoadmit level3.proof-listp-aux)
(%autoprove definition-of-level3.proofp-aux
            (%enable default level3.proofp-aux level3.proof-listp-aux)
            (%restrict default level3.flag-proofp-aux (equal x 'x)))
(%autoprove definition-of-level3.proof-listp-aux
            (%enable default level3.proofp-aux level3.proof-listp-aux)
            (%restrict default level3.flag-proofp-aux (equal x 'x)))


(%autoprove level3.proofp-aux-when-not-consp      (%restrict default definition-of-level3.proofp-aux (equal x 'x)))
(%autoprove level3.proof-listp-aux-when-not-consp (%restrict default definition-of-level3.proof-listp-aux (equal x 'x)))
(%autoprove level3.proof-listp-aux-of-cons        (%restrict default definition-of-level3.proof-listp-aux (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-level3.proofp-aux
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level3.proofp-aux (equal x 'x)))

(%autoprove booleanp-of-level3.proofp-aux      (%use (%instance (%thm lemma-for-booleanp-of-level3.proofp-aux) (flag 'proof))))
(%autoprove booleanp-of-level3.proof-listp-aux (%use (%instance (%thm lemma-for-booleanp-of-level3.proofp-aux) (flag 'list))))


(%deflist level3.proof-listp-aux (x axioms thms atbl)
          (level3.proofp-aux x axioms thms atbl))


(%autoprove lemma-for-logic.provablep-when-level3.proofp-aux
             (%logic.appeal-induction flag x)
             (%disable default forcing-true-listp-of-logic.subproofs)
             ;; Using the urewrite here cleans up tons of simple clauses, reducing the proof size
             ;; from 1.7B to 188M
             (%auto :strategy (cleanup urewrite split))
             (%auto)
             (%restrict default definition-of-level3.proofp-aux (equal x 'x)))

(%autoprove logic.provablep-when-level3.proofp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level3.proofp-aux) (flag 'proof))))

(%autoprove logic.provable-listp-when-level3.proof-listp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level3.proofp-aux) (flag 'list))))



(%autoprove lemma-for-level3.proofp-aux-when-logic.proofp
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level3.proofp-aux (equal x 'x))
            (%restrict default definition-of-logic.proofp (equal x 'x)))

(%autoprove level3.proofp-aux-when-logic.proofp
            (%use (%instance (%thm lemma-for-level3.proofp-aux-when-logic.proofp) (flag 'proof))))

(%autoprove level3.proof-listp-aux-when-logic.proof-listp
            (%use (%instance (%thm lemma-for-level3.proofp-aux-when-logic.proofp) (flag 'list))))

(%autoprove forcing-level3.proofp-aux-of-logic.provable-witness
            (%enable default level3.proofp-aux-when-logic.proofp))



(%autoadmit level3.proofp)
(%autoprove booleanp-of-level3.proofp
            (%enable default level3.proofp))
(%autoprove logic.provablep-when-level3.proofp
            (%enable default level3.proofp))


(defsection level3-transition
  (%install-new-proofp level3.proofp)
  (%auto)
  (%qed-install))




;; Propositional rules
(%switch-builder build.modus-ponens-list                         build.modus-ponens-list-high)
(%switch-builder build.disjoined-modus-ponens-list               build.disjoined-modus-ponens-list-high)
(%switch-builder build.generic-subset                            build.generic-subset-high)
(%switch-builder build.disjoined-subset                          build.generic-subset-high)
(%switch-builder build.multi-expansion                           build.multi-expansion-high)
(%switch-builder build.multi-or-expansion                        build.multi-or-expansion-high)
(%switch-builder build.rev-disjunction                           build.rev-disjunction-high)
(%switch-builder build.ordered-subset                            build.ordered-subset-high)
(%switch-builder build.disjoined-rev-disjunction                 build.disjoined-rev-disjunction-high)
(%switch-builder build.multi-assoc-expansion                     build.multi-assoc-expansion-high)
(%switch-builder clause.aux-disjoined-update-clause-twiddle      clause.aux-disjoined-update-clause-twiddle-high)

;; Pequal rules
(%switch-builder build.reflexivity                               build.reflexivity-high)
(%switch-builder build.commute-pequal                            build.commute-pequal-high)
(%switch-builder build.disjoined-commute-pequal                  build.disjoined-commute-pequal-high)
(%switch-builder build.commute-not-pequal                        build.commute-not-pequal-high)
(%switch-builder build.disjoined-commute-not-pequal              build.disjoined-commute-not-pequal-high)
(%switch-builder build.substitute-into-not-pequal                build.substitute-into-not-pequal-high)
(%switch-builder build.disjoined-substitute-into-not-pequal      build.disjoined-substitute-into-not-pequal-high)
(%switch-builder build.transitivity-of-pequal                    build.transitivity-of-pequal-high)
(%switch-builder build.disjoined-transitivity-of-pequal          build.disjoined-transitivity-of-pequal-high)
(%switch-builder build.not-nil-from-t                            build.not-nil-from-t-high)
(%switch-builder build.disjoined-not-nil-from-t                  build.disjoined-not-nil-from-t-high)
(%switch-builder build.not-t-from-nil                            build.not-t-from-nil-high)
(%switch-builder build.disjoined-not-t-from-nil                  build.disjoined-not-t-from-nil-high)

;; Equal rules
(%switch-builder build.equal-reflexivity                         build.equal-reflexivity-high)
(%switch-builder build.equal-t-from-not-nil                      build.equal-t-from-not-nil-high)
(%switch-builder build.disjoined-equal-t-from-not-nil            build.disjoined-equal-t-from-not-nil-high)
(%switch-builder build.equal-nil-from-not-t                      build.equal-nil-from-not-t-high)
(%switch-builder build.disjoined-equal-nil-from-not-t            build.disjoined-equal-nil-from-not-t-high)
(%switch-builder build.pequal-from-equal                         build.pequal-from-equal-high)
(%switch-builder build.disjoined-pequal-from-equal               build.disjoined-pequal-from-equal-high)
(%switch-builder build.not-equal-from-not-pequal                 build.not-equal-from-not-pequal-high)
(%switch-builder build.disjoined-not-equal-from-not-pequal       build.disjoined-not-equal-from-not-pequal-high)
(%switch-builder build.commute-equal                             build.commute-equal-high)
(%switch-builder build.disjoined-commute-equal                   build.disjoined-commute-equal-high)
(%switch-builder build.equal-from-pequal                         build.equal-from-pequal-high)
(%switch-builder build.disjoined-equal-from-pequal               build.disjoined-equal-from-pequal-high)
(%switch-builder build.not-pequal-from-not-equal                 build.not-pequal-from-not-equal-high)
(%switch-builder build.disjoined-not-pequal-from-not-equal       build.disjoined-not-pequal-from-not-equal-high)
(%switch-builder build.transitivity-of-equal                     build.transitivity-of-equal-high)
(%switch-builder build.disjoined-transitivity-of-equal           build.disjoined-transitivity-of-equal-high)
(%switch-builder build.not-pequal-constants                      build.not-pequal-constants-high)

;; If rules
(%switch-builder build.if-when-not-nil                           build.if-when-not-nil-high)
(%switch-builder build.if-when-nil                               build.if-when-nil-high)

;; Iff rules
(%switch-builder build.iff-t-from-not-pequal-nil                 build.iff-t-from-not-pequal-nil-high)
(%switch-builder build.disjoined-iff-t-from-not-pequal-nil       build.disjoined-iff-t-from-not-pequal-nil-high)
(%switch-builder build.not-pequal-nil-from-iff-t                 build.not-pequal-nil-from-iff-t-high)
(%switch-builder build.disjoined-not-pequal-nil-from-iff-t       build.disjoined-not-pequal-nil-from-iff-t-high)
(%switch-builder build.iff-t-from-not-nil                        build.iff-t-from-not-nil-high)
(%switch-builder build.disjoined-iff-t-from-not-nil              build.disjoined-iff-t-from-not-nil-high)
(%switch-builder build.iff-reflexivity                           build.iff-reflexivity-high)
(%switch-builder build.commute-iff                               build.commute-iff-high)
(%switch-builder build.disjoined-commute-iff                     build.disjoined-commute-iff-high)
(%switch-builder build.transitivity-of-iff                       build.transitivity-of-iff-high)
(%switch-builder build.disjoined-transitivity-of-iff             build.disjoined-transitivity-of-iff-high)
(%switch-builder build.iff-from-pequal                           build.iff-from-pequal-high)
(%switch-builder build.disjoined-iff-from-pequal                 build.disjoined-iff-from-pequal-high)
(%switch-builder build.iff-from-equal                            build.iff-from-equal-high)
(%switch-builder build.disjoined-iff-from-equal                  build.disjoined-iff-from-equal-high)

;; Not rules
(%switch-builder build.disjoined-negative-lit-from-pequal-nil    build.disjoined-negative-lit-from-pequal-nil-high)
(%switch-builder build.disjoined-pequal-nil-from-negative-lit    build.disjoined-pequal-nil-from-negative-lit-high)
(%switch-builder build.disjoined-iff-when-not-nil                build.disjoined-iff-when-not-nil-high)



(%finish "level3")
(%save-events "level3.events")

;; Clear out the thmfiles table since we'll use the saved image from now on.
(ACL2::table tactic-harness 'thmfiles nil)
