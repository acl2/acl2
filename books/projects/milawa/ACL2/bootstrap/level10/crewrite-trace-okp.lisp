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
(include-book "crewrite-iffp")
(include-book "crewrite-hypbox")
(include-book "crewrite-lhs")
(local (include-book "crewrite-local-settings"))
(%interactive)


;; An ugly hack.
;;
;; Our free-variable matching doesn't work quite like ACL2's on certain "lousy"
;; rewrite rules like forcing-rw.trace->hypbox-of-rw.cache-lookup, shown here:
;;
;; (IMPLIES (FORCE (AND (RW.CACHE-LOOKUP TERM IFFP CACHE)
;;                      (LOGIC.TERMP TERM)
;;                      (RW.CACHEP CACHE)
;;                      (BOOLEANP IFFP)
;;                      (RW.CACHE-ASSMSP CACHE ASSMS)))
;;          (EQUAL (RW.TRACE->HYPBOX (RW.CACHE-LOOKUP TERM IFFP CACHE))
;;                 (RW.ASSMS->HYPBOX ASSMS)))
;;
;; In the Milawa world, this rule is insufficient for our main theorem because
;; the "cache" position is inhabited by a complicated term of the form:
;;
;;     (RW.CRESULT->CACHE (RW.CREWRITE-CORE-LIST ... cache ...))
;;
;; This leads our free-variable matching code to search for an assumption of the
;; form:
;;
;;     (rw.cache-assmsp (RW.CRESULT->CACHE (RW.CREWRITE-CORE-LIST ... cache ...))
;;                      assms)
;;
;; But the only reasonably close assumption we have around is instead:
;;
;;     (rw.cache-assmsp cache assms)
;;
;; Which does not match.  Somehow, miraculously, in the ACL2 world this works.
;; But rather than try to fix our free variable matching code to handle such a
;; strange situation, we just prove the following, ugly rule:

(defthmd lemma-2-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core
  (implies (force (and (rw.cache-lookup term iffp1
                                        (rw.cresult->cache
                                         (rw.crewrite-core-list assms args cache iffp2 blimit rlimit anstack control)))
                       (rw.cache-assmsp cache assms)
                       (logic.termp term)
                       (logic.term-listp args)
                       (rw.cachep cache)
                       (booleanp iffp1)
                       (booleanp iffp2)
                       (rw.assmsp assms)
                       (rw.controlp control)))
           (equal (rw.trace->hypbox
                   (rw.cache-lookup term iffp1
                                    (rw.cresult->cache
                                     (rw.crewrite-core-list assms args cache iffp2 blimit rlimit anstack control))))
                  (rw.assms->hypbox assms)))
  :hints(("Goal"
          :in-theory (disable forcing-rw.trace->hypbox-of-rw.cache-lookup
                              forcing-rw.cache-assmsp-of-rw.cresult->cache-of-rw.crewrite-core-list)
          :use ((:instance forcing-rw.cache-assmsp-of-rw.cresult->cache-of-rw.crewrite-core-list
                           (x args)
                           (iffp iffp2))
                (:instance forcing-rw.trace->hypbox-of-rw.cache-lookup
                           (term term)
                           (iffp iffp1)
                           (cache (rw.cresult->cache (rw.crewrite-core-list assms args
                                                                            cache iffp2
                                                                            blimit rlimit anstack control)))
                           (assms assms))))))

(%autoprove lemma-2-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core
            (%disable default
                      forcing-rw.trace->hypbox-of-rw.cache-lookup
                      forcing-rw.cache-assmsp-of-rw.cresult->cache-of-rw.crewrite-core-list)
            (%use (%instance (%thm forcing-rw.cache-assmsp-of-rw.cresult->cache-of-rw.crewrite-core-list)
                             (x args)
                             (iffp iffp2)))
            (%use (%instance (%thm forcing-rw.trace->hypbox-of-rw.cache-lookup)
                             (term term)
                             (iffp iffp1)
                             (cache (rw.cresult->cache (rw.crewrite-core-list assms args
                                                                              cache iffp2
                                                                              blimit rlimit anstack control)))
                             (assms assms))))


(local (%max-proof-size 0))
(local (%quiet t))

(%autoprove lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core

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
            (%waterfall default 400) ;; 1657 seconds

            (%betamode t)
            (%enable default
                     splitters
                     special-disables-for-fast-pruning)

            (%waterfall default 400) ;; 1178 seconds


            ;; restrictions as before
            (%restrict default definition-of-rw.crewrite-core (equal x 'x))
            (%restrict default definition-of-rw.crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
            (%restrict default definition-of-rw.crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
            (%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x))

            (%enable default lemma-2-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)

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

;; old size: rewrite-trace-okp.pcert.out:;; Proof size: 19,636,580,041 conses.
;; new trick:  Proof size: 6,553,523,402 conses.
            (%betamode t)
            (%crewrite default)

            (%waterfall default 400) ;; 388 sec

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

            (%waterfall default 400) ;; 207 seconds
            (%car-cdr-elim)

            (%forcingp t)
            (%auto))






(%autoprove forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'term))))

(%autoprove forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-okp-of-rw.cresult->data-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'list))))

(%autoprove forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'list))))

(%autoprove forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove forcing-rw.trace-list-okp-of-rw.cresult->cache-of-rw.crewrite-relieve-hyps
            ;; BOZO bad name.  Should say hypresult->traces
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyps))))

(%autoprove forcing-rw.cache-traces-okp-of-rw.hypresult->cache-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyps))))






#||

old

(%autoprove lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core

            (%quiet t)
            (%autoinduct rw.flag-crewrite)
            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-lookup-of-logic.function-name-free
                      equal-of-logic.function-rewrite
                      equal-of-logic.function-rewrite-alt)
            (%betamode nil)
            (%forcingp nil)
            (%liftlimit 2)
            (%splitlimit 2)
            (%waterfall default 400)

            (%enable default
                     splitters
                     special-disables-for-fast-pruning)
            (%betamode once)
            (%waterfall default 400)

            (%restrict default definition-of-rw.crewrite-core (equal x 'x))
            (%restrict default definition-of-rw.crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
            (%restrict default definition-of-rw.crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
            (%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x))

            (%disable default ;; speed hint
                      rw.crewrite-try-rules-when-not-consp
                      rw.tracep-when-memberp-of-rw.trace-listp)

            (%enable default lemma-2-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)

            (%waterfall default 400)

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

            (%auto :strategy (split cleanup urewrite crewrite elim))

            (%forcingp t)
            (%auto))

||#





;; (%autoprove lemma-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core

;;             (%quiet t)

;;             (%autoinduct rw.flag-crewrite)
;;             (%disable default
;;                       forcing-lookup-of-logic.function-name
;;                       forcing-lookup-of-logic.function-name-free
;;                       equal-of-logic.function-rewrite
;;                       equal-of-logic.function-rewrite-alt)

;;             ;; Interlaced splitting and lightweight rewriting to control case explosion

;;             (%betamode nil)
;;             (%forcingp nil)
;;             (%crewrite default)
;;             (%split :liftp t :liftlimit 1 :splitlimit 25)
;;             (%crewrite default)
;;             (%cleanup)
;;             (%split :liftp t :liftlimit 1 :splitlimit 25)
;;             (%crewrite default)
;;             (%cleanup)
;;             (%split :liftp t :liftlimit 1 :splitlimit 25)
;;             (%crewrite default)
;;             (%cleanup)
;;             (%split :liftp t :liftlimit 1 :splitlimit 25)
;;             (%crewrite default)
;;             (%cleanup)
;;             (%split :liftp t :liftlimit 1 :splitlimit 25)
;;             (%crewrite default)
;;             (%cleanup)
;;             (%split :liftp t :liftlimit 1 :splitlimit 25)
;;             (%crewrite default)
;;             (%cleanup)
;;             (%split :liftp t :liftlimit 1 :splitlimit 25)
;;             (%crewrite default)
;;             (%cleanup)
;;             (%split :liftp t :liftlimit 3 :splitlimit 25)
;;             (%crewrite default)
;;             (%cleanup)
;;             (%split :liftp t :liftlimit 0 :splitlimit 0)
;;             (%quiet nil)

;;             (%enable default
;;                      splitters
;;                      special-disables-for-fast-pruning)
;;             (%betamode once)
;;             (%crewrite default)
;;             (%cleanup)
;;             (%split :liftp t :liftlimit 0 :splitlimit 0)

;;             (%crewrite default)
;;             (%cleanup)

;;             ;; This might look a little scary, but observe that no single goal is affected
;;             ;; by more than one of these expansions.

;;             (%restrict default definition-of-rw.crewrite-core (equal x 'x))
;;             (%restrict default definition-of-rw.crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
;;             (%restrict default definition-of-rw.crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
;;             (%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x))

;;             (%disable default ;; speed hint
;;                       rw.crewrite-try-rules-when-not-consp
;;                       rw.tracep-when-memberp-of-rw.trace-listp)

;;             (%enable default lemma-2-for-forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core)

;;             (%crewrite default)

;;             (%auto :strategy (split cleanup crewrite))

;;             (%enable default
;;                      expensive-term/formula-inference
;;                      formula-decomposition
;;                      rw.crewrite-try-rules-when-not-consp
;;                      rw.tracep-when-memberp-of-rw.trace-listp
;;                      expensive-arithmetic-rules
;;                      expensive-arithmetic-rules-two
;;                      type-set-like-rules
;;                      unusual-consp-rules
;;                      unusual-memberp-rules
;;                      unusual-subsetp-rules
;;                      min)

;;             (%auto :strategy (split cleanup urewrite crewrite elim)))
