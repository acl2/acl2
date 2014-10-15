; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "crewrite-trace-atblp")
(local (include-book "crewrite-local-settings"))
(%interactive)

(local (%max-proof-size 0))
(local (%quiet t))

(%autoprove lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core
            (%autoinduct rw.flag-crewrite)
            (%restrict default forcing-lookup-of-logic.function-name (equal atbl 'atbl))
            (%restrict default forcing-lookup-of-logic.function-name-free (equal atbl 'atbl))

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
            (%waterfall default 400)  ;; 3214 seconds

            (%betamode t)
            (%enable default
                     splitters
                     special-disables-for-fast-pruning)

            (%waterfall default 400) ;; 1491 seconds


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

;; old size: crewrite-trace-env-okp.pcert.out:;; Proof size: 9,946,713,505 conses.
;; new trick: ;; Proof size: 6,641,263,939 conses.
            (%betamode t)
            (%crewrite default)

            (%waterfall default 400) ;; 355 seconds

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
                     logic.termp-when-invalid-maybe-expensive)

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
                      equal-of-symbol-and-non-symbol-cheap)

            (%waterfall default 400) ;; 155 seconds
            (%car-cdr-elim)
            (%auto))

(%autoprove forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'term))))

(%autoprove forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-env-okp-of-rw.cresult->data-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'list))))

(%autoprove forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'list))))

(%autoprove forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove forcing-rw.trace-list-env-okp-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyps))))

(%autoprove forcing-rw.cache-env-okp-of-rw.hypresult->cache-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyps))))







#||

Old approach

(%autoprove lemma-for-forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core

            (%autoinduct rw.flag-crewrite)

            (%restrict default forcing-lookup-of-logic.function-name (equal atbl 'atbl))
            (%restrict default forcing-lookup-of-logic.function-name-free (equal atbl 'atbl))

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