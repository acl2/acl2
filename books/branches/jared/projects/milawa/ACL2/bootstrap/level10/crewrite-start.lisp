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
(%interactive)

(%rwn 1000)
(%urwn 1000)

(local (%max-proof-size 0))

(%autoadmit four-nats-measure)

(%autoprove ordp-of-four-nats-measure
            (%enable default four-nats-measure)
            (%restrict default ordp
                       (memberp x '((CONS (CONS '3 (+ '1 A))
                                          (CONS (CONS '2 (+ '1 B))
                                                (CONS (CONS '1 (+ '1 C)) (NFIX D))))
                                    (CONS (CONS '2 (+ '1 B))
                                          (CONS (CONS '1 (+ '1 C)) (NFIX D)))
                                    (CONS (CONS '1 (+ '1 C)) (NFIX D))))))

(%autoprove ord<-of-four-nats-measure
            (%enable default four-nats-measure)
            (%restrict default ord<
                       (memberp x '((CONS (CONS '3 (+ '1 A1))
                                          (CONS (CONS '2 (+ '1 B1))
                                                (CONS (CONS '1 (+ '1 C1)) (NFIX D1))))
                                    (CONS (CONS '2 (+ '1 B1))
                                          (CONS (CONS '1 (+ '1 C1)) (NFIX D1)))
                                    (CONS (CONS '1 (+ '1 C1)) (NFIX D1))))))


(defsection rw.cresult
  (%autoadmit rw.cresult)
  (%autoadmit rw.cresult->data)
  (%autoadmit rw.cresult->cache)
  (%autoadmit rw.cresult->alimitedp)

  (local (%enable default
                  rw.cresult
                  rw.cresult->data
                  rw.cresult->cache
                  rw.cresult->alimitedp))

  (%autoprove rw.cresult-under-iff)
  (%autoprove rw.cresult->data-of-rw.cresult)
  (%autoprove rw.cresult->cache-of-rw.cresult)
  (%autoprove rw.cresult->alimitedp-of-rw.cresult))


(defsection rw.hypresult
  (%autoadmit rw.hypresult)
  (%autoadmit rw.hypresult->successp)
  (%autoadmit rw.hypresult->traces)
  (%autoadmit rw.hypresult->cache)
  (%autoadmit rw.hypresult->alimitedp)

  (local (%enable default
                  rw.hypresult
                  rw.hypresult->successp
                  rw.hypresult->traces
                  rw.hypresult->cache
                  rw.hypresult->alimitedp))

  (%autoprove rw.hypresult-under-iff)
  (%autoprove rw.hypresult->successp-of-rw.hypresult)
  (%autoprove rw.hypresult->traces-of-rw.hypresult)
  (%autoprove rw.hypresult->cache-of-rw.hypresult)
  (%autoprove rw.hypresult->alimitedp-of-rw.hypresult))



(%autoadmit rw.flag-crewrite)



(defsection elimination-of-irrelevant-arguments

  (local (%forcingp nil))
  (local (%betamode nil))

  (%autoprove rw.flag-crewrite-of-term-reduction
              (%restrict default rw.flag-crewrite (and (equal flag ''term) (equal x 'x))))

  (%autoprove rw.flag-crewrite-of-list-reduction
              (%restrict default rw.flag-crewrite (and (equal flag ''list) (equal x 'x))))

  (%autoprove rw.flag-crewrite-of-rule-reduction
              (%restrict default rw.flag-crewrite (and (equal flag ''rule) (equal x 'x))))

  (%autoprove rw.flag-crewrite-of-rules-reduction
              (%restrict default rw.flag-crewrite (and (equal flag ''rules) (equal x 'x))))

  (%autoprove rw.flag-crewrite-of-hyp-reduction
              (%restrict default rw.flag-crewrite (and (equal flag ''hyp) (equal x 'x))))

  (%autoprove rw.flag-crewrite-of-hyps-reduction
              (%restrict default rw.flag-crewrite (and (equal flag ''hyps) (equal x 'x)))))



(defsection flag-function-wrappers

  (%autoadmit rw.crewrite-core)
  (%autoadmit rw.crewrite-core-list)
  (%autoadmit rw.crewrite-try-rule)
  (%autoadmit rw.crewrite-try-rules)
  (%autoadmit rw.crewrite-try-match)
  (%autoadmit rw.crewrite-try-matches)
  (%autoadmit rw.crewrite-relieve-hyp)
  (%autoadmit rw.crewrite-relieve-hyps)

  (local (%forcingp nil))
  (local (%enable default
                  rw.crewrite-core
                  rw.crewrite-core-list
                  rw.crewrite-try-rule
                  rw.crewrite-try-rules
                  rw.crewrite-try-match
                  rw.crewrite-try-matches
                  rw.crewrite-relieve-hyp
                  rw.crewrite-relieve-hyps))

  (%autoprove rw.flag-crewrite-of-term
              (%use (%thm rw.flag-crewrite-of-term-reduction)))

  (%autoprove rw.flag-crewrite-of-list
              (%use (%thm rw.flag-crewrite-of-list-reduction)))

  (%autoprove rw.flag-crewrite-of-rule
              (%use (%thm rw.flag-crewrite-of-rule-reduction)))

  (%autoprove rw.flag-crewrite-of-rules
              (%use (%thm rw.flag-crewrite-of-rules-reduction)))

  (%autoprove rw.flag-crewrite-of-match)
  (%autoprove rw.flag-crewrite-of-matches)

  (%autoprove rw.flag-crewrite-of-hyp
              (%use (%thm rw.flag-crewrite-of-hyp-reduction)))

  (%autoprove rw.flag-crewrite-of-hyps
              (%use (%thm rw.flag-crewrite-of-hyps-reduction))))




(%autoprove equal-with-quoted-list-of-nil)

(defsection proper-definitions-for-flag-wrappers
  (local (%forcingp nil))
  (local (%rwn 2000))
  (local (%disable default
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
                   forcing-logic.function-of-logic.function-name-and-logic.function-args-free))

  (%autoprove definition-of-rw.crewrite-core
              (%use (%instance (%thm rw.flag-crewrite) (flag 'term)))
              (%betamode nil)
              (%auto)
              (%betamode once))

  (%autoprove definition-of-rw.crewrite-core-list
              (%use (%instance (%thm rw.flag-crewrite) (flag 'list)))
              (%betamode nil)
              (%auto)
              (%betamode once))

  (%autoprove definition-of-rw.crewrite-try-rule
              (%use (%instance (%thm rw.flag-crewrite) (flag 'rule)))
              (%betamode nil)
              (%auto)
              (%betamode once))

  (%autoprove definition-of-rw.crewrite-try-rules
              (%use (%instance (%thm rw.flag-crewrite) (flag 'rules)))
              (%betamode nil)
              (%auto)
              (%betamode once))

  (%autoprove definition-of-rw.crewrite-try-match
              (%use (%instance (%thm rw.flag-crewrite) (flag 'match)))
              (%betamode nil)
              (%auto)
              (%betamode once))

  (%autoprove definition-of-rw.crewrite-try-matches
              (%use (%instance (%thm rw.flag-crewrite) (flag 'matches)))
              (%betamode nil)
              (%auto)
              (%betamode once))

  (%autoprove definition-of-rw.crewrite-relieve-hyp
              (%use (%instance (%thm rw.flag-crewrite) (flag 'hyp)))
              (%betamode nil)
              (%auto)
              (%betamode once))

  (%autoprove definition-of-rw.crewrite-relieve-hyps
              (%use (%instance (%thm rw.flag-crewrite) (flag 'hyps)))
              (%betamode nil)
              (%auto)
              (%betamode once)))





(%autoprove rw.crewrite-core-list-when-not-consp
            (%restrict default definition-of-rw.crewrite-core-list (equal x 'x)))

(%autoprove rw.crewrite-core-list-of-cons
            (%restrict default definition-of-rw.crewrite-core-list (equal x '(cons a x))))

(%autoprove true-listp-of-rw.cresult->data-of-rw.crewrite-core-list
            (%induct (rank x)
                     ((not (consp x))
                      nil)
                     ((consp x)
                      (((x     (cdr x))
                        (cache (rw.cresult->cache
                                (rw.crewrite-core assms (car x) cache iffp blimit rlimit anstack control))))))))

(%autoprove len-of-rw.cresult->data-of-rw.crewrite-core-list$
            (%induct (rank x)
                     ((not (consp x))
                      nil)
                     ((consp x)
                      (((x     (cdr x))
                        (cache (rw.cresult->cache
                                (rw.crewrite-core assms (car x) cache iffp blimit rlimit anstack control))))))))




(%autoprove rw.crewrite-try-rules-when-not-consp
            (%restrict default definition-of-rw.crewrite-try-rules (equal rule[s] 'rule[s])))

(%autoprove rw.crewrite-try-rules-of-cons
            (%restrict default definition-of-rw.crewrite-try-rules (equal rule[s] '(cons rule rules))))



(%autoprove rw.crewrite-try-matches-when-not-consp
            (%restrict default definition-of-rw.crewrite-try-matches (equal sigma[s] 'sigma[s])))

(%autoprove rw.crewrite-try-matches-of-cons
            (%restrict default definition-of-rw.crewrite-try-matches (equal sigma[s] '(cons sigma sigmas))))



(%autoprove rw.crewrite-relieve-hyps-when-not-consp
            (%restrict default definition-of-rw.crewrite-relieve-hyps (equal x 'x)))

(%autoprove rw.crewrite-relieve-hyps-of-cons
            (%restrict default definition-of-rw.crewrite-relieve-hyps (equal x '(cons a x))))

(%autoprove booleanp-of-rw.hypresult->successp-of-rw.crewrite-relieve-hyps
            (%use (%thm definition-of-rw.crewrite-relieve-hyps)))



(%autoprove zp-of-one-plus)

