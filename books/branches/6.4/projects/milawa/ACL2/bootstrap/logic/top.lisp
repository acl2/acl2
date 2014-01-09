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

(include-book "arities-okp")
(include-book "appeal-identity")
(include-book "base-evaluator")
(include-book "disjoin-formulas")
(include-book "find-proof")
(include-book "formula-size")
(include-book "formulas")
(include-book "fterm-lists")
(include-book "functional-axiom")
(include-book "groundp")
(include-book "negate-formulas")
(include-book "negate-term")
;; Stupid file, don't implement (include-book "pand")
;; Never used, probably don't care? (include-book "patmatch-formula")
(include-book "patmatch-term")
(include-book "pequal-list")
;; Stupid file, don't implement (include-book "piff")
(include-book "por-list")
(include-book "proofp")
(include-book "quote-range")
(include-book "replace-subterm")
(include-book "substitute-formula")
(include-book "substitute-term")
(include-book "subtermp")
;; Probably don't care?  (include-book "termination")
(include-book "term-formula")
(include-book "term-order")
(include-book "terms")
;; ACL2-specific, move elsewhere? (include-book "trace-proofp")
;; Probably don't care? (include-book "translate")
;; Probably don't care? (include-book "translate-sigma")



(%create-theory formula-decomposition)
(%enable formula-decomposition
         aggressive-equal-of-logic.pors
         aggressive-equal-of-logic.pnots
         aggressive-equal-of-logic.pequals
         forcing-equal-of-logic.pequal-rewrite
         forcing-equal-of-logic.pequal-rewrite-two
         forcing-equal-of-logic.por-rewrite
         forcing-equal-of-logic.por-rewrite-two
         forcing-equal-of-logic.pnot-rewrite
         forcing-equal-of-logic.pnot-rewrite-two
         forcing-equal-of-logic.pequal-list-rewrite
         forcing-equal-of-logic.pequal-list-rewrite-alt
         forcing-equal-of-logic.function-with-three-args-alt
         equal-of-logic.function-rewrite
         equal-of-logic.function-rewrite-alt
         [outside]equal-of-logic.function-and-logic.function
         equal-logic.pequal-logic.pequal-rewrite
         [outside]equal-logic.pequal-logic.pequal-rewrite
         equal-logic.por-logic.por-rewrite
         [outside]equal-logic.por-logic.por-rewrite)

(%create-theory expensive-term/formula-inference)
(%enable expensive-term/formula-inference
         logic.termp-when-logic.formulap
         logic.termp-when-invalid-maybe-expensive
         logic.formulap-when-logic.termp
         logic.constantp-when-not-consp
         logic.constantp-when-logic.variablep
         logic.constantp-when-logic.functionp
         logic.constantp-when-logic.lambdap-cheap
         logic.constantp-of-car-when-logic.constant-listp
         logic.constantp-of-second-when-logic.constant-listp
         logic.constantp-of-third-when-logic.constant-listp
         logic.constantp-of-car-when-logic.none-constantp
         logic.constantp-when-memberp-of-logic.constant-listp
         logic.constant-listp-when-not-consp
         logic.constant-listp-of-subsetp-when-logic.constant-listp
         logic.variablep-when-consp
         logic.variablep-when-logic.constantp
         logic.variablep-when-logic.functionp
         logic.variablep-when-logic.lambdap-cheap
         logic.functionp-when-not-other-stuff-cheap
         logic.functionp-when-logic.lambdap-cheap
         forcing-logic.functionp-when-logic.base-evaluablep
         forcing-logic.functionp-when-logic.base-evaluablep
         logic.lambdap-when-not-other-stuff-cheap
         logic.lambdap-when-not-anything-else-maybe-expensive
         logic.lambdap-when-consp-of-car-cheap
         logic.lambdap-when-logic.functionp-cheap
         forcing-true-listp-of-logic.function-args)

(%enable expensive-subsetp-rules
         memberp-when-logic.all-terms-larger-cheap)

(%enable unusual-memberp-rules
         memberp-when-logic.all-terms-larger-cheap)

(%enable unusual-consp-rules
         consp-when-memberp-of-logic.sigmap-alt
         consp-when-memberp-of-logic.arity-tablep-alt
         consp-when-logic.functionp-cheap
         consp-when-logic.lambdap-cheap)


(%finish "logic")
(%save-events "logic.events")

;; Clear out the thmfiles table since we'll use the saved image from now on.
(ACL2::table tactic-harness 'thmfiles nil)
