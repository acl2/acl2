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
(include-book "fast-ftracep")
(local (include-book "crewrite-local-settings"))




; This is the "hardest" proof in all of Milawa.  With some speed hints and
; printing disabled, the ACL2 proof of this lemma takes around 650 seconds on
; the lhug machines.  By comparison, most proofs about the regular rewriter
; take only around 50 seconds.  So that's quite a jump.

(local (%max-proof-size 0))

(%autoprove lemma-for-rw.trace-fast-image-of-rw.crewrite-core

; The goals produced here are so large that it is disabling output results
; in a considerable speed boost.
            (%quiet t)

; At a high-level, the proof is not very complicated.  We induct upon the
; definition of the ordinary reweriter, and our fast-image functions will
; canonicalize the things it does into the fast versions.  So, we are inducting
; over the definition of flag-crewrite, which is an eight-way mutual recursion.
; And we are trying to simultaneously prove several facts about each of our
; fast-crewrite functions.  The result is a terrible, multiplicative case
; split.
;
; To handle this, we developed the %waterfall tactic, which can operate in a
; depth-first manner instead of the ordinary breadth-first way.  The basic goal
; is to completely perform all of the case splitting before we open up any of
; the rewriter functions.  We rewrite the intermediate cases to "prune" the
; tree, using a very restricted theory that does not introduce case splits and
; where beta-reduction and forcing are disallowed.

            (%autoinduct rw.flag-crewrite flag assms x rule[s] sigma[s]
                         cache iffp blimit rlimit anstack control)

            (%forcingp nil)

            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-lookup-of-logic.function-name-free)


; The waterfall operates by taking each goal and first trying to rewrite it in
; the restricted theory we have just mentioned, then once that stabilizes we
; try to split into cases.  As a result, the splitlimit and liftlimit really
; have quite an impact on how many goals the rewriter will need to consider.  I
; had very little intuition about what the proper settings were.  So, I fired
; up a bunch of the lhug machines and got to writing this chart.
;
; These results are not very scientific.  Another user who will go unnamed has
; been heavily using "my lhug machines" for the past semester, and my requests
; to gripe have not resulted in more useful 64-bit machines.  Also, due to the
; length of these experiments, I have not tried to repeat them.  At any rate,
; the table below may have some considerable error.  It's not too important
; that we get "the best answer", we just want the proof to complete in a
; reasonable amount of time.
;
; Reading the chart.
;
;    - I tried two strategies, (crewrite split) and (crewrite nolift-split
;      split).  NOLIFT indicates whether nolift-split was in the strategy
;      or not.
;
;    - L_LIMIT and S_LIMIT are the liftlimit and splitlimit used.
;
;    - TIME is the total amount of time it took to run the waterfall,
;      GC_TIME is the part of this that was spent in gc, and ALLOC is the
;      total allocation during the whole waterfall (in GB)
;
;    - Clauses #125 and #118 were a couple of fairly large goals that could
;      be used as indicators of how successful a strategy would be
;
;    - NA indicates that I killed the test rather than let it finish, after
;      having first determined that it was not competitive with other
;      approaches.
;
;  NOLIFT   L_LIMIT  S_LIMIT  TIME     GC_TIME  ALLOC  125_T  118_T
;
;  IN       2        1        6017s    235s     37.4   89s    810s      *test-2-1*
;  IN       2        2        6041s    274s     36.2   104s   864s      *test-2-2*
;  IN       2        4        6973s    410s     47.6   180s   1117s     *test-2-4*
;  IN       5        2        9268s    433s     36.1   85s    1468s     *test-5-2*
;  IN       8        2        5786s    206s     33.3   76s    602s      *test-8-2*
;  IN       10       1        6148s    224s     36.5   52s    746s      *test-10-1*
;  IN       10       2        5614s    200s     32.4   76s    608s      *test-10-2*
;  IN       10       3        6517s    264s     37.3   125s   751s      *test-10-3*
;  IN       10       5        NA       NA       NA     231s   945s      *test-10-5*
;  IN       15       2        5507s    208s     32.5   77s    617s      *test-15-2*
;  IN       20       2        5590s    233s     33.3   78s    622s      *test-20-2*
;  IN       20       10       NA       NA       NA     1639s  NA        *test-20-10*
;  IN       10       20       NA       NA       NA     NA     NA        *test-10-20*
;
;  OUT      2        2        5727s    266s     35.8   69s    536s      *test-2-2-lift*
;  OUT      2        4        6867s    365s     42.1   199s   796s      *test-2-4-lift*
;  OUT      4        2        6300s    285s     36.3   71s    490s      *test-4-2-lift*
;  OUT      10       1        7761s    394s     45.3   111s   828s      *test-10-1-lift*
;  OUT      10       2        6046s    277s     36.5   64s    468s      *test-10-2-lift*
;  OUT      10       5        6689s    279s     35.8   46s    544s      *test-10-5-lift*
;  OUT      15       2        6110s    384s     45.5   53s    539s      *test-15-2-lift*
;
; These results above were taken with
;  (%enable default rw.trace-fast-image-equivalence-lemmas)
;  (%betamode nil)
;  (%liftlimit n)
;  (%splitlimit n)
;  (%waterfall default 400)
;
; I later investigated just allowing the beta-reduction and splitting to happen all at once.
; And the result seems to be marginally faster than doing them separately, so I am just going
; with it now.

            (%liftlimit 1)
            (%splitlimit 1)

            (%betamode once)
            (%enable default
                     splitters
                     special-disables-for-fast-pruning
                     rw.trace-fast-image-equivalence-lemmas)

            (%waterfall default 400)

            (%enable default rw.fast-weakening-trace)
            (%restrict default definition-of-rw.fast-crewrite-core (equal x 'x))
            (%restrict default definition-of-rw.fast-crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
            (%restrict default definition-of-rw.fast-crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
            (%restrict default definition-of-rw.fast-crewrite-relieve-hyp (equal x 'x))
            (%restrict default definition-of-rw.crewrite-core (equal x 'x))
            (%restrict default definition-of-rw.crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
            (%restrict default definition-of-rw.crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
            (%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x))

; This crewrite is crucial for proof size.  It reduces the proof size from 240 GC to 19 GC.
            (%betamode t)
            (%crewrite default)

            (%waterfall default 400)

            (%enable default
                     expensive-term/formula-inference
                     formula-decomposition
                     rw.crewrite-try-rules-when-not-consp
                     rw.tracep-when-memberp-of-rw.trace-listp
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     type-set-like-rules
                     usual-consp-rules
                     unusual-consp-rules
                     unusual-memberp-rules
                     unusual-subsetp-rules
                     min
                     equal-of-booleans-rewrite)

            (%auto))

(%autoprove rw.trace-fast-image-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'term))))

(%autoprove rw.cache-fast-image-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'term))))

(%autoprove rw.cresult->alimitedp-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'term))))


(%autoprove rw.trace-list-fast-image-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'list))))

(%autoprove rw.cache-fast-image-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'list))))

(%autoprove rw.cresult->alimitedp-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'list))))


(%autoprove rw.crewrite-try-rule-under-iff
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove rw.trace-fast-image-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove rw.cache-fast-image-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove rw.cresult->alimitedp-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'rule))))


(%autoprove rw.crewrite-try-rules-under-iff
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove rw.trace-fast-image-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove rw.cache-fast-image-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove rw.cresult->alimitedp-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'rules))))


(%autoprove rw.crewrite-try-match-under-iff
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove rw.trace-fast-image-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove rw.cache-fast-image-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove rw.cresult->alimitedp-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'match))))


(%autoprove rw.crewrite-try-matches-under-iff
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove rw.trace-fast-image-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove rw.cache-fast-image-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove rw.cresult->alimitedp-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'matches))))


(%autoprove rw.crewrite-relieve-hyp-under-iff
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove rw.trace-fast-image-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove rw.cache-fast-image-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove rw.cresult->alimitedp-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'hyp))))


(%autoprove rw.hypresult->successp-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'hyps))))

(%autoprove rw.trace-list-fast-image-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'hyps))))

(%autoprove rw.cache-fast-image-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'hyps))))

(%autoprove rw.hypresult->alimitedp-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-rw.trace-fast-image-of-rw.crewrite-core)
                             (flag 'hyps))))
