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
;;       Copyright (C) 2005-2007 by Jared Davis <jared@cs.utexas.edu>        ;;
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
(include-book "crewrite-start")
(%interactive)


;; ESSAY ON PROVING THEOREMS ABOUT CREWRITE.
;;
;; It is particularly difficult to prove theorems about crewrite because:
;;
;;   (1) the function itself is quite large and complicated, with 8
;;       mutually-recursive flags and hundreds of lines of code;
;;
;;   (2) the induction scheme is correspondingly very complex; and
;;
;;   (3) each theorem we want to prove must have eight cases of its own in
;;       order to address the various flags.
;;
;; This must be carefully managed to avoid a case explosion.  To handle this,
;; we open each proof with a "light splitting, then light rewriting" approach.
;; By "light rewriting", we mean:
;;
;;   (1) we rewrite with a cheap theory (so that rewriting is fast), and
;;
;;   (2) we do not use any splitting rules, beta reduction, or forcing (so that
;;       we don't introduce more cases).
;;
;; The net effect is that many branches of the case-splitting tree are pruned
;; early on instead of being explored.



(%rwn 1000)



(%cheapen default rw.trace-list-rhses-when-not-consp)
;(%cheapen default rw.crewrite-core-list-when-not-consp)

(%create-theory my-disables-for-extra-speed)
(%enable my-disables-for-extra-speed
         consp-when-memberp-of-logic.sigmap
         consp-when-memberp-of-logic.sigmap-alt
         consp-when-memberp-of-logic.sigma-atblp
         consp-when-memberp-of-logic.sigma-atblp-alt
         consp-when-memberp-of-logic.arity-tablep
         consp-when-memberp-of-logic.arity-tablep-alt
         ;;consp-when-memberp-of-logic.callmapp
         ;;consp-when-memberp-of-logic.callmapp-alt
         ;;consp-when-memberp-of-logic.callmap-atblp
         ;;consp-when-memberp-of-logic.callmap-atblp-alt
         consp-when-memberp-of-rw.cachemapp
         consp-when-memberp-of-rw.cachemapp-alt
         consp-when-memberp-of-none-consp
         consp-when-memberp-of-none-consp-alt
         consp-when-memberp-of-cons-listp
         consp-when-memberp-of-cons-listp-alt
         same-length-prefixes-equal-cheap
         car-when-not-consp
         cdr-when-not-consp
         consp-when-natp-cheap
         forcing-logic.groundp-of-logic.substitute
         consp-when-logic.lambdap-cheap
         consp-when-logic.functionp-cheap
         consp-when-nonempty-subset-cheap
         consp-when-memberp-cheap
         logic.substitute-when-malformed-cheap
         logic.constant-listp-when-not-consp
         subsetp-when-not-consp
         subsetp-when-not-consp-two
         cons-listp-when-not-consp
         none-consp-when-not-consp
         forcing-logic.substitute-of-empty-sigma
         not-equal-when-less
         trichotomy-of-<
         natp-of-len-free
         transitivity-of-<
         transitivity-of-<-three
         transitivity-of-<-two
         less-completion-left
         less-of-one-right)
(%disable default my-disables-for-extra-speed)

(%disable default zp min)

(%disable default
          formula-decomposition
          expensive-term/formula-inference
          expensive-arithmetic-rules
          expensive-arithmetic-rules-two
          type-set-like-rules
          unusual-consp-rules
          unusual-memberp-rules
          unusual-subsetp-rules
          same-length-prefixes-equal-cheap
          ;; ---
          lookup-when-not-consp
          rw.trace-list-rhses-when-not-consp
          forcing-logic.function-of-logic.function-name-and-logic.function-args-free)

(%disable default
          logic.substitute-when-logic.lambdap-cheap
          logic.substitute-when-logic.variablep
          logic.substitute-when-logic.constantp
          logic.substitute-when-logic.functionp-cheap
          forcing-logic.substitute-list-of-empty-sigma
          logic.substitute-list-when-not-consp
          logic.substitute-list-of-cons-gross)


;; SPECIAL THEORIES FOR THE OPENING MOVE.

(%create-theory splitters)
(%enable splitters
         ;; These are all of the rules that introduce an "if" on the
         ;; right-hand side (and hence may cause case splits).
         (gather from default (not (clause.simple-termp rhs))))
(%disable default splitters)


(%create-theory special-disables-for-fast-pruning)
(%enable special-disables-for-fast-pruning
         ;; These are rules which %profile said were useless and
         ;; expensive during the initial phase.  Disabling them helps to
         ;; speed up the rewriting.
         rw.trace-list-rhses-when-not-consp
         logic.termp-when-not-consp-cheap
         rank-when-not-consp
         rw.trace-listp-when-not-consp
         forcing-rw.assmsp-of-rw.assume-left
         logic.term-listp-when-not-consp
         ord<-when-naturals
         logic.sigmap-when-not-consp
         logic.constant-listp-of-logic.function-args-when-logic.base-evaluablep
         forcing-logic.term-listp-of-rw.trace-list-rhses
         cdr-when-true-listp-with-len-free-past-the-end
         forcing-logic.groundp-when-logic.constant-listp-of-logic.function-args
         minus-when-zp-left-cheap
         minus-when-zp-right-cheap
         minus-when-not-less
         forcing-logic.groundp-when-logic.constant-listp-of-logic.lambda-actuals
         logic.variable-listp-of-cdr-when-logic.variable-listp
         forcing-logic.termp-of-logic.substitute
         logic.variablep-of-car-when-logic.variable-listp
         rw.rule-listp-of-cdr-when-rw.rule-listp
         cdr-of-cdr-when-true-listp-with-len-free-past-the-end
         cdr-of-cdr-with-len-free-past-the-end
         logic.groundp-when-logic.constantp
         forcing-logic.function-args-of-logic.substitute
         forcing-logic.lambda-actuals-of-logic.substitute
         logic.constant-listp-of-cdr-when-logic.constant-listp
         rw.typed-rulemapp-when-not-consp
         memberp-when-not-consp ordp-when-natp
         memberp-when-memberp-of-cdr
         rw.rulep-of-car-when-rw.rule-listp
         logic.sigmap-of-car-when-logic.sigma-listp
         forcing-rw.cachep-of-rw.set-blockedp
         logic.sigma-listp-of-cdr-when-logic.sigma-listp
         )
(%disable default special-disables-for-fast-pruning)

