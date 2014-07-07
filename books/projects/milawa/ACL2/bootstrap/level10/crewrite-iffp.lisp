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
(include-book "crewrite-tracep")
(local (include-book "crewrite-local-settings"))
(%interactive)


; Original size: 2.47 b
; Urewrite-focused size: 1.16 b
; With rlimit hacking: 867 m
; with crewrite-first: still 867 m

(local (%max-proof-size 0))
(local (%quiet t))

(%autoprove lemma-for-forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core

(%autoinduct rw.flag-crewrite)

(%disable default
          forcing-lookup-of-logic.function-name
          forcing-lookup-of-logic.function-name-free
          consp-when-consp-of-cdr-cheap
          forcing-logic.functionp-when-rewrite.syntaxp-base-evaluablep
          logic.constant-listp-of-logic.function-args-when-rewrite.syntaxp-base-evaluablep)

(%enable default
         rw.trace-fast-image-equivalence-lemmas
         special-disables-for-fast-pruning
         splitters)

(%urewrite default) ; 138
(%cleanup) ; 124
(%liftlimit 1)
(%splitlimit 10)
(%waterfall default 40 :strategy (split urewrite))
(%cleanup)

; Funny trick to only lightly use crewrite.  This way we get to prune some
; goals while mainly relying upon assumptions, urewrite, and split, which
; produce small proofs.

(%forcingp nil)
(%urwn 1000)
(%blimit 0)
(%rlimit 0)
(%disable-loop-debugging)
(%crewrite default)


(%restrict default definition-of-rw.crewrite-core (equal x 'x))
(%restrict default definition-of-rw.crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
(%restrict default definition-of-rw.crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
(%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x))

(%urewrite default)
(%waterfall default 40 :strategy (split urewrite))
(%cleanup)

(%disable default ;; speed hint
          minus-when-not-less
          minus-when-zp-right-cheap
          minus-when-zp-left-cheap
          logic.termp-when-not-consp-cheap
          logic.constant-listp-of-logic.function-args-when-logic.base-evaluablep
          forcing-logic.lambda-actuals-of-logic.substitute
          forcing-logic.function-args-of-logic.substitute)

(%blimit)
(%rlimit)
(%crewrite default)

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

; trying auto now instead of waterfall, since maybe we get better forcing sharing out of crewrite-all?
(%auto))


(%autoprove forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-iffps-of-rw.cresult->data-of-rw.crewrite-core-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'list))))

(%autoprove forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-try-rule
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rule))))

(%autoprove forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-try-rules
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'rules))))

(%autoprove forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-try-match
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'match))))

(%autoprove forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-try-matches
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'matches))))

(%autoprove forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyp))))

(%autoprove forcing-rw.trace-list-iffps-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core)
                             (flag 'hyps))))




#||


(local (%rwn 1000))


;; ;; I think this has increased in size because level9 isn't doing anything anymore.
;; ;; Worlds are all broken.  Maybe we can fix them, or maybe put back a urewrite that
;; ;; uses the slow urewriter anyway.




;; ;; The previous proof, below, has increased to 3 billion conses.
;; ;; seems like this is bigger because level9 is no longer actually doing anything?
;; ;; and hence this is effectively a level 8 proof?

;; (%autorule lemma-for-forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core)
;; (%quiet t)
;; (%autoinduct rw.flag-crewrite)
;; (%disable default
;;           forcing-lookup-of-logic.function-name
;;           forcing-lookup-of-logic.function-name-free)
;; (%betamode nil)
;; (%forcingp nil)
;; (%crewrite default)

;; ; Lifting a lot seems to lead to lots of goals being proven immediately.

;; (%split :liftp t :liftlimit 10 :splitlimit 5) ;; 1180 goals
;; (%crewrite default)

;; (%split :liftp t :liftlimit 10 :splitlimit 5)
;; (%cleanup) ;; 745 goals
;; (%crewrite default) ;; 469

;; (%split :liftp t :liftlimit nil :splitlimit nil) ;; 1538
;; (%crewrite default) ;; 765

;; (%betamode once)
;; (%enable default
;;          splitters
;;          special-disables-for-fast-pruning)
;; (%crewrite default)  ;; 538
;; (%split :liftp t :liftlimit nil :splitlimit nil) ;; 1754
;; (%crewrite default)
;; (%split :liftp t :liftlimit nil :splitlimit nil) ;; 996

;; (%restrict default definition-of-rw.crewrite-core (equal x 'x))
;; (%restrict default definition-of-rw.crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
;; (%restrict default definition-of-rw.crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
;; (%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x))

;; (%disable default ;; speed hint
;;                       rw.crewrite-try-rules-when-not-consp
;;                       rw.tracep-when-memberp-of-rw.trace-listp)

;; (%crewrite default)

;; (%auto :strategy (split cleanup crewrite))

;; (%enable default
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

;; (%auto :strategy (split cleanup urewrite crewrite elim))

;; (%qed)




;; ;;; --------------------





;; (%split :liftp t :liftlimit 5 :splitlimit 5)


;; (%ngoals) ;; 1406
;; (%cleanup)
;; (%ngoals) ;; 1323
;; (%crewrite default)
;; (%ngoals)
;; (%cleanup)
;; (%ngoals)
;; (%split :liftp t :liftlimit nil :splitlimit nil)
;; (%ngoals)
;; (%crewrite default)
;; (%cleanup)





;;             (%betamode once)
;;             (%crewrite default)
;;             (%cleanup)
;;             (%split :liftp t :liftlimit 0 :splitlimit 0)

;;             (%crewrite default)
;;             (%cleanup)




;; (%restrict default definition-of-rw.crewrite-core (equal x 'x))
;; (%restrict default definition-of-rw.crewrite-try-rule (equal x 'x) (equal rule[s] 'rule[s]))
;; (%restrict default definition-of-rw.crewrite-try-match (equal x 'x) (equal sigma[s] 'sigma[s]))
;; (%restrict default definition-of-rw.crewrite-relieve-hyp (equal x 'x))

;; (%disable default ;; speed hint
;;                       rw.crewrite-try-rules-when-not-consp
;;                       rw.tracep-when-memberp-of-rw.trace-listp)

;; (%crewrite default)

;; (%auto :strategy (split cleanup crewrite))

;; (%enable default
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

;; (%auto :strategy (split cleanup urewrite crewrite elim)))



;; old

(%autoprove lemma-for-forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core
            (%autoinduct rw.flag-crewrite)
            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-lookup-of-logic.function-name-free)

            ;; Interlaced splitting and lightweight rewriting to control case explosion
            (%quiet t)
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