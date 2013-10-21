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
(include-book "crewrite-tracep")
(local (include-book "crewrite-local-settings"))
(%interactive)


(local (%max-proof-size 0))
(local (%quiet t))

(%autoprove lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core
            (%autoinduct rw.flag-crewrite)
            (%disable default
                      ;; Maybe these cause some problems.
                      forcing-lookup-of-logic.function-name
                      forcing-lookup-of-logic.function-name-free)

            (%disable default
                      ;; The theory is already really tight, but there are a few things
                      ;; we're missing, probably because we added the syntax evaluator
                      ;; later on and who knows why for consp-when-consp-of-cdr-cheap.
                      consp-when-consp-of-cdr-cheap
                      forcing-logic.functionp-when-rewrite.syntaxp-base-evaluablep
                      logic.constant-listp-of-logic.function-args-when-rewrite.syntaxp-base-evaluablep)


            ;; Phase 1.  Simplify the resulting induction goals before opening up the
            ;; definitions.

            (%forcingp nil)
            (%liftlimit 10)
            (%splitlimit 2)
            (%betamode nil)
            (%waterfall default 400)

            (%betamode t)
            (%enable default
                     splitters
                     special-disables-for-fast-pruning)

            (%waterfall default 400)


            ;; restrictions as before
            (%restrict default definition-of-rw.crewrite-core (equal x 'x))
            (%restrict default definition-of-rw.crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
            (%restrict default definition-of-rw.crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
            (%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x))

            (%disable default ;; speed hint
                      rw.crewrite-try-rules-when-not-consp
                      rw.crewrite-core-list-when-not-consp
                      rw.crewrite-relieve-hyps-when-not-consp
                      rw.crewrite-try-matches-when-not-consp
                      rw.tracep-when-memberp-of-rw.trace-listp
                      minus-when-not-less
                      minus-when-zp-right-cheap
                      minus-when-zp-left-cheap
                      logic.termp-when-not-consp-cheap
                      logic.constant-listp-of-logic.function-args-when-logic.base-evaluablep
                      forcing-logic.lambda-actuals-of-logic.substitute
                      forcing-logic.function-args-of-logic.substitute)

;; old size to beat:
;; crewrite-lhs.pcert.out:;; Proof size: 9,757,811,855 conses.
;; trying new trick:;; Proof size: 5,816,777,976 conses.
            (%betamode t)
            (%crewrite default)

            (%waterfall default 400)

            (%enable default
                     rw.crewrite-try-rules-when-not-consp
                     rw.tracep-when-memberp-of-rw.trace-listp
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     type-set-like-rules
                     unusual-consp-rules
                     unusual-memberp-rules
                     unusual-subsetp-rules
                     min
                     logic.termp-when-invalid-maybe-expensive
                     expensive-term/formula-inference
                     formula-decomposition)

            (%disable default
                      squeeze-law-one
                      squeeze-law-two
                      squeeze-law-three
                      minus-when-not-less
                      not-equal-when-less
                      |a <= b, c != 0 --> a < b+c|
                      one-plus-trick
                      |a <= b, c != 0 --> a < c+b|
                      nfix-when-zp-cheap
                      nfix-when-not-natp-cheap
                      zp-when-not-natp-cheap
                      natp-when-zp-cheap
                      |a <= b, b <= c --> a < 1+c|
                      equal-of-booleans-rewrite
                      gather-constants-from-less-of-plus
                      gather-constants-from-less-of-plus-two
                      minus-when-zp-left-cheap
                      minus-when-zp-right-cheap
                      plus-when-zp-left-cheap
                      plus-when-zp-right-cheap
                      gather-constants-from-equal-of-plus
                      equal-of-non-symbol-and-symbol-cheap
                      equal-of-non-cons-and-cons-cheap
                      equal-of-cons-and-non-cons-cheap
                      equal-of-non-nat-and-nat-cheap
                      equal-of-nat-and-non-nat-cheap
                      equal-of-symbol-and-non-symbol-cheap

                      AGGRESSIVE-EQUAL-OF-LOGIC.PNOTS
                      AGGRESSIVE-EQUAL-OF-LOGIC.PORS
                      AGGRESSIVE-EQUAL-OF-LOGIC.PEQUALS
                      LOGIC.FMTYPE-WHEN-DEFINITIONP
                      RW.CREWRITE-TRY-RULES-WHEN-NOT-CONSP
                      LOGIC.GROUNDP-WHEN-LOGIC.CONSTANTP
                      LOGIC.CONSTANTP-WHEN-LOGIC.VARIABLEP
                      RW.TRACE-LIST-RHSES-WHEN-NOT-CONSP
                      CONSP-OF-CDR-WHEN-LEN-TWO-CHEAP
                      CONSP-WHEN-NATP-CHEAP
                      LOGIC.CONSTANT-LISTP-WHEN-NOT-CONSP
                      LOGIC.LAMBDAP-WHEN-CONSP-OF-CAR-CHEAP
                      LOGIC.LAMBDAP-WHEN-NOT-OTHER-STUFF-CHEAP
                      CONSP-WHEN-NOTHING-ELSE-CHEAP
                      LOGIC.TERMP-WHEN-LOGIC.FORMULAP
                      LOGIC.FUNCTIONP-WHEN-CLAUSE.NEGATIVE-TERMP
                      FORCING-LOGIC.FUNCTIONP-WHEN-LOGIC.BASE-EVALUABLEP
                      LOGIC.TERMP-WHEN-LOGIC.CONSTANTP
                      LOGIC.TERMP-WHEN-LOGIC.VARIABLEP)

            (%waterfall default 400) ;; 272 secs

            (%car-cdr-elim)
            (%auto))


(%autoprove forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'term))))

(%autoprove forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-lhses-of-rw.cresult->data-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'list))))

(%autoprove forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'list))))

(%autoprove forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove forcing-rw.trace-list-lhses-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyps))))

(%autoprove forcing-rw.cache-lhses-okp-of-rw.hypresult->cache-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyps))))




(%autoprove forcing-rw.trace->rhs-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
            (%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x)))

(%autoprove forcing-rw.trace-list-rhses-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
            (%induct (rank x)
                     ((not (consp x))
                      nil)
                     ((consp x)
                      (((x (cdr x))
                        (cache (rw.cresult->cache (rw.crewrite-relieve-hyp assms (car x) rule[s] sigma[s] cache
                                                                           blimit rlimit anstack control)))))))
            (%enable default splitters special-disables-for-fast-pruning))




#||

;; old

(%autoprove lemma-for-forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core

            (%quiet t)

            (%autoinduct rw.flag-crewrite)
            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-lookup-of-logic.function-name-free
                      equal-of-logic.function-rewrite
                      equal-of-logic.function-rewrite-alt)

            ;; Interlaced splitting and lightweight rewriting to control case explosion

            (%betamode nil)
            (%forcingp nil)
            (%crewrite default)
            (%split :liftp t :liftlimit 1 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 1 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 1 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 1 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 1 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 3 :splitlimit 25)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 0 :splitlimit 0)
            (%quiet nil)

            (%enable default
                     splitters
                     special-disables-for-fast-pruning)
            (%betamode once)
            (%crewrite default)
            (%cleanup)
            (%split :liftp t :liftlimit 0 :splitlimit 0)

            (%crewrite default)
            (%cleanup)

            ;; This might look a little scary, but observe that no single goal is affected
            ;; by more than one of these expansions.

            (%restrict default definition-of-rw.crewrite-core (equal x 'x))
            (%restrict default definition-of-rw.crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
            (%restrict default definition-of-rw.crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
            (%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x))

            (%disable default ;; speed hint
                      rw.crewrite-try-rules-when-not-consp
                      rw.tracep-when-memberp-of-rw.trace-listp)

            (%crewrite default)

            (%auto :strategy (split cleanup crewrite))

            (%enable default
                     expensive-term/formula-inference
                     formula-decomposition
                     rw.crewrite-try-rules-when-not-consp
                     rw.tracep-when-memberp-of-rw.trace-listp
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     type-set-like-rules
                     unusual-consp-rules
                     unusual-memberp-rules
                     unusual-subsetp-rules
                     min)

            (%auto :strategy (split cleanup urewrite crewrite elim)))
||#