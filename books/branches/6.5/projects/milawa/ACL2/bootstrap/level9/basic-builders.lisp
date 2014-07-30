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
(include-book "controlp")
(%interactive)


(%autoprove booleanp-of-rw.trace->iffp)

(local (%disable default forcing-booleanp-of-rw.trace->iffp))
(local (%enable default booleanp-of-rw.trace->iffp))


(defsection rw.fail-trace

  (%autoadmit rw.fail-trace)

  (local (%enable default rw.fail-trace))

  (%autoprove rw.trace->method-of-rw.fail-trace)
  (%autoprove rw.trace->hypbox-of-rw.fail-trace)
  (%autoprove rw.trace->lhs-of-rw.fail-trace)
  (%autoprove rw.trace->rhs-of-rw.fail-trace)
  (%autoprove rw.trace->iffp-of-rw.fail-trace)
  (%autoprove rw.trace->subtraces-of-rw.fail-trace)
  (%autoprove rw.trace->extras-of-rw.fail-trace)
  (%autoprove forcing-rw.tracep-of-rw.fail-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.fail-trace)

  (local (%disable default rw.fail-trace))

  (%autoprove rw.fail-tracep-of-rw.fail-trace
              (%enable default rw.fail-tracep))

  (%autoprove rw.trace-step-okp-of-rw.fail-trace
              (%enable default rw.trace-step-okp))

  (%autoprove rw.trace-step-env-okp-of-rw.fail-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-okp-of-rw.fail-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.fail-trace hypbox term iffp))))

  (%autoprove forcing-rw.trace-env-okp-of-rw.fail-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.fail-trace hypbox term iffp))))

  (%autoprove rw.collect-forced-goals-of-rw.fail-trace
              (%restrict default definition-of-rw.collect-forced-goals (equal x '(rw.fail-trace hypbox term iffp)))))



(defsection rw.transitivity-trace

  (%autoadmit rw.transitivity-trace)

  (local (%enable default rw.transitivity-trace))

  (%autoprove rw.transitivity-trace-under-iff)
  (%autoprove rw.trace->method-of-rw.transitivity-trace)
  (%autoprove rw.trace->hypbox-of-rw.transitivity-trace)
  (%autoprove rw.trace->lhs-of-rw.transitivity-trace)
  (%autoprove rw.trace->rhs-of-rw.transitivity-trace)
  (%autoprove rw.trace->iffp-of-rw.transitivity-trace)
  (%autoprove rw.trace->subtraces-of-rw.transitivity-trace)
  (%autoprove rw.trace->extras-of-rw.transitivity-trace)
  (%autoprove forcing-rw.tracep-of-rw.transitivity-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.transitivity-trace)

  (local (%disable default rw.transitivity-trace))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.transitivity-trace
              (%enable default rw.transitivity-tracep rw.trace-step-okp))

  (%autoprove forcing-rw.trace-okp-of-rw.transitivity-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.transitivity-trace x y)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.transitivity-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.transitivity-trace
              (%enable default rw.transitivity-tracep rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.transitivity-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.transitivity-trace x y)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.transitivity-trace))

  (%autoprove rw.collect-forced-goals-of-rw.transitivity-trace
              (%enable default definition-of-rw.collect-forced-goals)))




(defsection rw.equiv-by-args-trace

  (%autoadmit rw.equiv-by-args-trace)

  (local (%enable default rw.equiv-by-args-trace))

  (%autoprove lemma-rw.trace->method-of-rw.equiv-by-args-trace)
  (%autoprove forcing-rw.trace->hypbox-of-rw.equiv-by-args-trace)
  (%autoprove forcing-rw.trace->lhs-of-rw.equiv-by-args-trace)
  (%autoprove forcing-rw.trace->rhs-of-rw.equiv-by-args-trace)
  (%autoprove rw.trace->iffp-of-rw.equiv-by-args-trace)
  (%autoprove rw.trace->subtraces-of-rw.equiv-by-args-trace)
  (%autoprove rw.trace->extras-of-rw.equiv-by-args-trace)
  (%autoprove forcing-rw.tracep-of-rw.equiv-by-args-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.equiv-by-args-trace)

  (local (%disable default rw.equiv-by-args-trace))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.equiv-by-args-trace
              (%enable default rw.equiv-by-args-tracep rw.trace-step-okp))

  (%autoprove forcing-rw.trace-okp-of-rw.equiv-by-args-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.equiv-by-args-trace hypbox f iffp traces)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.equiv-by-args-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.equiv-by-args-trace
              (%enable default rw.equiv-by-args-tracep rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.equiv-by-args-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.equiv-by-args-trace hypbox f iffp traces)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.equiv-by-args-trace))

  (%autoprove rw.collect-forced-goals-of-rw.equiv-by-args-trace
              (%enable default definition-of-rw.collect-forced-goals)))



(defsection rw.lambda-equiv-by-args-trace

  (%autoadmit rw.lambda-equiv-by-args-trace)

  (local (%enable default rw.lambda-equiv-by-args-trace))

  (%autoprove rw.trace->method-of-rw.lambda-equiv-by-args-trace)
  (%autoprove rw.trace->hypbox-of-rw.lambda-equiv-by-args-trace)
  (%autoprove rw.trace->lhs-of-rw.lambda-equiv-by-args-trace)
  (%autoprove rw.trace->rhs-of-rw.lambda-equiv-by-args-trace)
  (%autoprove rw.trace->iffp-of-rw.lambda-equiv-by-args-trace)
  (%autoprove rw.trace->subtraces-of-rw.lambda-equiv-by-args-trace)
  (%autoprove rw.trace->extras-of-rw.lambda-equiv-by-args-trace)
  (%autoprove forcing-rw.tracep-of-rw.lambda-equiv-by-args-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.lambda-equiv-by-args-trace)

  (local (%disable default rw.lambda-equiv-by-args-trace))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.lambda-equiv-by-args-trace
              (%enable default rw.trace-step-okp rw.lambda-equiv-by-args-tracep))

  (%autoprove forcing-rw.trace-okp-of-rw.lambda-equiv-by-args-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.lambda-equiv-by-args-trace hypbox formals body iffp traces)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.lambda-equiv-by-args-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.lambda-equiv-by-args-trace
              (%enable default rw.trace-step-env-okp rw.lambda-equiv-by-args-tracep))

  (%autoprove forcing-rw.trace-env-okp-of-rw.lambda-equiv-by-args-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.lambda-equiv-by-args-trace hypbox formals body iffp traces)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.lambda-equiv-by-args-trace))

  (%autoprove rw.collect-forced-goals-of-rw.lambda-equiv-by-args-trace
              (%enable default definition-of-rw.collect-forced-goals)))



(defsection rw.beta-reduction-trace

  (%autoadmit rw.beta-reduction-trace)

  (local (%enable default rw.beta-reduction-trace))

  (%autoprove rw.trace->method-of-rw.beta-reduction-trace)
  (%autoprove rw.trace->hypbox-of-rw.beta-reduction-trace)
  (%autoprove rw.trace->lhs-of-rw.beta-reduction-trace)
  (%autoprove rw.trace->rhs-of-rw.beta-reduction-trace)
  (%autoprove rw.trace->iffp-of-rw.beta-reduction-trace)
  (%autoprove rw.trace->subtraces-of-rw.beta-reduction-trace)
  (%autoprove rw.trace->extras-of-rw.beta-reduction-trace)
  (%autoprove forcing-rw.tracep-of-rw.beta-reduction-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.beta-reduction-trace)

  (local (%disable default rw.beta-reduction-trace))

  (%autoprove lemma-forcing-rw.beta-reduction-tracep-of-rw.beta-reduction-trace
              (%enable default rw.beta-reduction-tracep))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.beta-reduction-trace
              (%enable default rw.trace-step-okp lemma-forcing-rw.beta-reduction-tracep-of-rw.beta-reduction-trace))

  (%autoprove forcing-rw.trace-okp-of-rw.beta-reduction-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.beta-reduction-trace hypbox term iffp)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.beta-reduction-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.beta-reduction-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.beta-reduction-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.beta-reduction-trace hypbox term iffp)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.beta-reduction-trace))

  (%autoprove rw.collect-forced-goals-of-rw.beta-reduction-trace
              (%enable default definition-of-rw.collect-forced-goals)))



(defsection rw.try-ground-simplify

  (%autoadmit rw.try-ground-simplify)

  (local (%enable default rw.try-ground-simplify))

  (%autoprove rw.trace->method-of-rw.try-ground-simplify)
  (%autoprove rw.trace->hypbox-of-rw.try-ground-simplify)
  (%autoprove forcing-rw.trace->lhs-of-rw.try-ground-simplify)
  (%autoprove forcing-rw.trace->iffp-of-rw.try-ground-simplify)
  (%autoprove rw.trace->subtraces-of-rw.try-ground-simplify)
  (%autoprove forcing-rw.trace->extras-of-rw.try-ground-simplify)
  (%autoprove lemma-forcing-logic.constantp-of-rw.trace->rhs)
  (%autoprove forcing-rw.tracep-of-rw.try-ground-simplify)
  (%autoprove forcing-rw.trace-atblp-of-rw.try-ground-simplify)
  (%autoprove lemma-forcing-rw.ground-tracep-of-rw.try-ground-simplify
              (%enable default rw.ground-tracep))

  (local (%disable default rw.try-ground-simplify))
  (local (%enable default
                  lemma-forcing-logic.constantp-of-rw.trace->rhs
                  lemma-forcing-rw.ground-tracep-of-rw.try-ground-simplify))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.try-ground-simplify
              (%enable default rw.trace-step-okp))

  (%autoprove forcing-rw.trace-okp-of-rw.try-ground-simplify
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.try-ground-simplify hypbox x iffp control)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.try-ground-simplify))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.try-ground-simplify
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.try-ground-simplify
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.try-ground-simplify hypbox x iffp control)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.try-ground-simplify))

  (%autoprove forcing-rw.collect-forced-goals-of-rw.try-ground-simplify
              (%enable default definition-of-rw.collect-forced-goals)))



(defsection rw.if-specialcase-nil-trace

  (%autoadmit rw.if-specialcase-nil-trace)

  (local (%enable default rw.if-specialcase-nil-trace))

  (%autoprove rw.trace->method-of-rw.if-specialcase-nil-trace)
  (%autoprove rw.trace->hypbox-of-rw.if-specialcase-nil-trace)
  (%autoprove rw.trace->lhs-of-rw.if-specialcase-nil-trace)
  (%autoprove rw.trace->rhs-of-rw.if-specialcase-nil-trace)
  (%autoprove rw.trace->iffp-of-rw.if-specialcase-nil-trace)
  (%autoprove rw.trace->subtraces-of-rw.if-specialcase-nil-trace)
  (%autoprove rw.trace->extras-of-rw.if-specialcase-nil-trace)
  (%autoprove forcing-rw.tracep-of-rw.if-specialcase-nil-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.if-specialcase-nil-trace)

  (local (%disable default rw.if-specialcase-nil-trace))

  (%autoprove lemma-forcing-rw.if-specialcase-nil-tracep-of-rw.if-specialcase-nil-trace
              (%enable default rw.if-specialcase-nil-tracep))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.if-specialcase-nil-trace
              (%enable default rw.trace-step-okp lemma-forcing-rw.if-specialcase-nil-tracep-of-rw.if-specialcase-nil-trace))

  (%autoprove forcing-rw.trace-okp-of-rw.if-specialcase-nil-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.if-specialcase-nil-trace x y b1)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.if-specialcase-nil-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.if-specialcase-nil-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.if-specialcase-nil-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.if-specialcase-nil-trace x y b1)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.if-specialcase-nil-trace))

  (%autoprove rw.collect-forced-goals-of-rw.if-specialcase-nil-trace
              (%enable default definition-of-rw.collect-forced-goals)))



(defsection rw.if-specialcase-t-trace

  (%autoadmit rw.if-specialcase-t-trace)

  (local (%enable default rw.if-specialcase-t-trace))

  (%autoprove rw.trace->method-of-rw.if-specialcase-t-trace)
  (%autoprove rw.trace->hypbox-of-rw.if-specialcase-t-trace)
  (%autoprove rw.trace->lhs-of-rw.if-specialcase-t-trace)
  (%autoprove rw.trace->rhs-of-rw.if-specialcase-t-trace)
  (%autoprove rw.trace->iffp-of-rw.if-specialcase-t-trace)
  (%autoprove rw.trace->subtraces-of-rw.if-specialcase-t-trace)
  (%autoprove rw.trace->extras-of-rw.if-specialcase-t-trace)
  (%autoprove forcing-rw.tracep-of-rw.if-specialcase-t-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.if-specialcase-t-trace)

  (local (%disable default rw.if-specialcase-t-trace))

  (%autoprove lemma-forcing-rw.if-specialcase-t-tracep-of-rw.if-specialcase-t-trace
              (%enable default rw.if-specialcase-t-tracep))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.if-specialcase-t-trace
              (%enable default rw.trace-step-okp lemma-forcing-rw.if-specialcase-t-tracep-of-rw.if-specialcase-t-trace))

  (%autoprove forcing-rw.trace-okp-of-rw.if-specialcase-t-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.if-specialcase-t-trace x y c1)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.if-specialcase-t-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.if-specialcase-t-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.if-specialcase-t-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.if-specialcase-t-trace x y c1)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.if-specialcase-t-trace))

  (%autoprove rw.collect-forced-goals-of-rw.if-specialcase-t-trace
              (%enable default definition-of-rw.collect-forced-goals)))



(defsection rw.not-trace

  (%autoadmit rw.not-trace)

  (local (%enable default rw.not-trace))

  (%autoprove rw.trace->method-of-rw.not-trace)
  (%autoprove rw.trace->hypbox-of-rw.not-trace)
  (%autoprove rw.trace->lhs-of-rw.not-trace)
  (%autoprove lemma-rw.trace->rhs-of-rw.not-trace)
  (%autoprove forcing-rw.trace->iffp-of-rw.not-trace)
  (%autoprove rw.trace->subtraces-of-rw.not-trace)
  (%autoprove rw.trace->extras-of-rw.not-trace)
  (%autoprove forcing-rw.tracep-of-rw.not-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.not-trace)

  (local (%disable default rw.not-trace))
  (local (%enable default lemma-rw.trace->rhs-of-rw.not-trace))

  (%autoprove lemma-forcing-rw.not-tracep-of-rw.not-trace
              (%enable default rw.not-tracep)
              (%splitlimit 10))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.not-trace
              (%enable default rw.trace-step-okp lemma-forcing-rw.not-tracep-of-rw.not-trace))

  (%autoprove forcing-rw.trace-okp-of-rw.not-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.not-trace x iffp)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.not-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.not-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.not-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.not-trace x iffp)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.not-trace))

  (%autoprove rw.collect-forced-goals-of-rw.not-trace
              (%enable default definition-of-rw.collect-forced-goals)))


(defsection rw.negative-if-trace

  (%autoadmit rw.negative-if-trace)

  (local (%enable default rw.negative-if-trace))

  (%autoprove rw.trace->method-of-rw.negative-if-trace)
  (%autoprove rw.trace->hypbox-of-rw.negative-if-trace)
  (%autoprove rw.trace->lhs-of-rw.negative-if-trace)
  (%autoprove rw.trace->rhs-of-rw.negative-if-trace)
  (%autoprove rw.trace->iffp-of-rw.negative-if-trace)
  (%autoprove rw.trace->subtraces-of-rw.negative-if-trace)
  (%autoprove rw.trace->extras-of-rw.negative-if-trace)
  (%autoprove forcing-rw.tracep-of-rw.negative-if-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.negative-if-trace)

  (local (%disable default rw.negative-if-trace))

  (%autoprove lemma-forcing-rw.negative-if-tracep-of-rw.negative-if-trace
              (%enable default rw.negative-if-tracep))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.negative-if-trace
              (%enable default rw.trace-step-okp lemma-forcing-rw.negative-if-tracep-of-rw.negative-if-trace))

  (%autoprove forcing-rw.trace-okp-of-rw.negative-if-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.negative-if-trace x iffp hypbox)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.negative-if-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.negative-if-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.negative-if-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.negative-if-trace x iffp hypbox)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.negative-if-trace))

  (%autoprove rw.collect-forced-goals-of-rw.negative-if-trace
              (%enable default definition-of-rw.collect-forced-goals)))



(defsection rw.maybe-extend-trace
  (%autoadmit rw.maybe-extend-trace)
  (local (%enable default rw.maybe-extend-trace))
  (%autoprove forcing-rw.tracep-of-rw.maybe-extend-trace)
  (%autoprove forcing-rw.trace-okp-of-rw.maybe-extend-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.maybe-extend-trace)
  (%autoprove forcing-rw.trace-env-okp-of-rw.maybe-extend-trace)
  (%autoprove forcing-rw.trace->iffp-of-rw.maybe-extend-trace)
  (%autoprove forcing-rw.trace->assms-of-rw.maybe-extend-trace)
  (%autoprove forcing-rw.trace->lhs-of-rw.maybe-extend-trace))



(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/basic-builders")