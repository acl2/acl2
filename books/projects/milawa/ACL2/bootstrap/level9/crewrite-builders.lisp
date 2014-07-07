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
(include-book "basic-builders")
(include-book "assms-top")
(%interactive)


(local (%enable default booleanp-of-rw.trace->iffp))
(local (%disable default forcing-booleanp-of-rw.trace->iffp))


(defsection rw.crewrite-if-specialcase-same-trace

  (%autoadmit rw.crewrite-if-specialcase-same-trace)

  (local (%enable default rw.crewrite-if-specialcase-same-trace))

  (%autoprove lemma-rw.trace->method-of-rw.crewrite-if-specialcase-same-trace)
  (%autoprove rw.trace->hypbox-of-rw.crewrite-if-specialcase-same-trace)
  (%autoprove rw.trace->lhs-of-rw.crewrite-if-specialcase-same-trace)
  (%autoprove rw.trace->rhs-of-rw.crewrite-if-specialcase-same-trace)
  (%autoprove forcing-rw.trace->iffp-of-rw.crewrite-if-specialcase-same-trace)
  (%autoprove lemma-rw.trace->subtraces-of-rw.crewrite-if-specialcase-same-trace)
  (%autoprove lemma-rw.trace->extras-of-rw.crewrite-if-specialcase-same-trace)
  (%autoprove forcing-rw.tracep-of-rw.crewrite-if-specialcase-same-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.crewrite-if-specialcase-same-trace)

  (local (%disable default rw.crewrite-if-specialcase-same-trace))
  (local (%enable default
                  lemma-rw.trace->method-of-rw.crewrite-if-specialcase-same-trace
                  lemma-rw.trace->subtraces-of-rw.crewrite-if-specialcase-same-trace
                  lemma-rw.trace->extras-of-rw.crewrite-if-specialcase-same-trace))

  (%autoprove lemma-forcing-rw.crewrite-if-specialcase-same-tracep-of-rw.crewrite-if-specialcase-same-trace
              (%enable default rw.crewrite-if-specialcase-same-tracep))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.crewrite-if-specialcase-same-trace
              (%enable default
                       lemma-forcing-rw.crewrite-if-specialcase-same-tracep-of-rw.crewrite-if-specialcase-same-trace
                       rw.trace-step-okp))

  (%autoprove forcing-rw.trace-okp-of-rw.crewrite-if-specialcase-same-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.crewrite-if-specialcase-same-trace x y z)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.crewrite-if-specialcase-same-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-if-specialcase-same-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.crewrite-if-specialcase-same-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.crewrite-if-specialcase-same-trace x y z)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-if-specialcase-same-trace))

  (%autoprove rw.collect-forced-goals-of-rw.crewrite-if-specialcase-same-trace
              (%restrict default definition-of-rw.collect-forced-goals
                         (equal x '(RW.CREWRITE-IF-SPECIALCASE-SAME-TRACE X Y Z)))))



(defsection rw.crewrite-if-generalcase-trace

  (%autoadmit rw.crewrite-if-generalcase-trace)

  (local (%enable default rw.crewrite-if-generalcase-trace))
  (local (%splitlimit 10))

  (%autoprove rw.trace->method-of-rw.crewrite-if-generalcase-trace)
  (%autoprove rw.trace->hypbox-of-rw.crewrite-if-generalcase-trace)
  (%autoprove rw.trace->lhs-of-rw.crewrite-if-generalcase-trace)
  (%autoprove rw.trace->rhs-of-rw.crewrite-if-generalcase-trace)
  (%autoprove forcing-rw.trace->iffp-of-rw.crewrite-if-generalcase-trace)
  (%autoprove rw.trace->subtraces-of-rw.crewrite-if-generalcase-trace)
  (%autoprove rw.trace->extras-of-rw.crewrite-if-generalcase-trace)
  (%autoprove forcing-rw.tracep-of-rw.crewrite-if-generalcase-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.crewrite-if-generalcase-trace)

  (local (%disable default rw.crewrite-if-generalcase-trace))

  (%autoprove lemma-forcing-rw.crewrite-if-generalcase-tracep-of-rw.crewrite-if-generalcase-trace
              (%enable default rw.crewrite-if-generalcase-tracep))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.crewrite-if-generalcase-trace
              (%enable default
                       lemma-forcing-rw.crewrite-if-generalcase-tracep-of-rw.crewrite-if-generalcase-trace
                       rw.trace-step-okp))

  (%autoprove forcing-rw.trace-okp-of-rw.crewrite-if-generalcase-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.crewrite-if-generalcase-trace x y z)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.crewrite-if-generalcase-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-if-generalcase-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.crewrite-if-generalcase-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.crewrite-if-generalcase-trace x y z)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-if-generalcase-trace))

  (%autoprove rw.collect-forced-goals-of-rw.crewrite-if-generalcase-trace
              (%restrict default definition-of-rw.collect-forced-goals
                         (equal x '(rw.crewrite-if-generalcase-trace x y z)))))



(defsection rw.assumptions-trace

  (%autoadmit rw.assumptions-trace)

  (local (%enable default rw.assumptions-trace))
  (local (%splitlimit 10))

  (%autoprove lemma-rw.trace->method-of-rw.assumptions-trace)
  (%autoprove rw.trace->assms-of-rw.assumptions-trace)
  (%autoprove rw.trace->lhs-of-rw.assumptions-trace)
  (%autoprove lemma-rw.trace->rhs-of-rw.assumptions-trace)
  (%autoprove rw.trace->iffp-of-rw.assumptions-trace)
  (%autoprove lemma-rw.trace->subtraces-of-rw.assumptions-trace)
  (%autoprove lemma-rw.trace->extras-of-rw.assumptions-trace)
  (%autoprove forcing-rw.tracep-of-rw.assumptions-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.assumptions-trace)
  (%autoprove lemma-rw.eqtracep-of-rw.eqtrace->extras-of-rw.assumptions-trace)

  (local (%disable default rw.assumptions-trace))
  (local (%enable default
                  lemma-rw.trace->method-of-rw.assumptions-trace
                  lemma-rw.trace->rhs-of-rw.assumptions-trace
                  lemma-rw.trace->subtraces-of-rw.assumptions-trace
                  lemma-rw.trace->extras-of-rw.assumptions-trace
                  lemma-rw.eqtracep-of-rw.eqtrace->extras-of-rw.assumptions-trace))

  (%autoprove lemma-forcing-rw.assumptions-tracep-of-rw.assumptions-trace
              (%enable default rw.assumptions-tracep rw.assumptions-trace))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.assumptions-trace
              (%enable default rw.trace-step-okp lemma-forcing-rw.assumptions-tracep-of-rw.assumptions-trace))

  (%autoprove forcing-rw.trace-okp-of-rw.assumptions-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.assumptions-trace assms lhs iffp)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.assumptions-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.assumptions-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.assumptions-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.assumptions-trace assms lhs iffp)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.assumptions-trace))

  (%autoprove rw.collect-forced-goals-of-rw.assumptions-trace
              (%restrict default definition-of-rw.collect-forced-goals
                         (equal x '(rw.assumptions-trace assms lhs iffp)))
              (%forcingp nil)
              (%auto)
              (%enable default rw.assumptions-trace)))





(defsection rw.crewrite-rule-trace

  (%autoadmit rw.crewrite-rule-trace)

  (local (%enable default rw.crewrite-rule-trace))

  (%autoprove rw.crewrite-rule-trace-under-iff)
  (%autoprove lemma-rw.trace->method-of-rw.crewrite-rule-trace)
  (%autoprove rw.trace->hypbox-of-rw.crewrite-rule-trace)
  (%autoprove rw.trace->lhs-of-rw.crewrite-rule-trace)
  (%autoprove rw.trace->rhs-of-rw.crewrite-rule-trace)
  (%autoprove forcing-rw.trace->iffp-of-rw.crewrite-rule-trace)
  (%autoprove lemma-rw.trace->subtraces-of-rw.crewrite-rule-trace)
  (%autoprove lemma-rw.trace->extras-of-rw.crewrite-rule-trace)
  (%autoprove forcing-rw.tracep-of-rw.crewrite-rule-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.crewrite-rule-trace)

  (local (%disable default rw.crewrite-rule-trace))
  (local (%enable default
                  lemma-rw.trace->method-of-rw.crewrite-rule-trace
                  lemma-rw.trace->subtraces-of-rw.crewrite-rule-trace
                  lemma-rw.trace->extras-of-rw.crewrite-rule-trace))

  (%autoprove lemma-forcing-rw.crewrite-rule-tracep-of-rw.crewrite-rule-trace
              (%enable default rw.crewrite-rule-tracep))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.crewrite-rule-trace
              (%enable default
                       rw.trace-step-okp
                       lemma-forcing-rw.crewrite-rule-tracep-of-rw.crewrite-rule-trace))

  (%autoprove forcing-rw.trace-okp-of-rw.crewrite-rule-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.crewrite-rule-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-rule-trace
              (%enable default
                       rw.trace-step-env-okp
                       rw.crewrite-rule-trace-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.crewrite-rule-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.crewrite-rule-trace))

  (%autoprove rw.collect-forced-goals-of-rw.crewrite-rule-trace
              (%restrict default definition-of-rw.collect-forced-goals
                         (equal x '(RW.CREWRITE-RULE-TRACE HYPBOX LHS RULE SIGMA IFFP TRACES)))))



(defsection rw.force-trace

  (%autoadmit rw.force-trace)

  (local (%enable default rw.force-trace))

  (%autoprove rw.force-trace-under-iff)
  (%autoprove lemma-rw.trace->method-of-rw.force-trace)
  (%autoprove rw.trace->hypbox-of-rw.force-trace)
  (%autoprove rw.trace->lhs-of-rw.force-trace)
  (%autoprove rw.trace->rhs-of-rw.force-trace)
  (%autoprove forcing-rw.trace->iffp-of-rw.force-trace)
  (%autoprove lemma-rw.trace->subtraces-of-rw.force-trace)
  (%autoprove lemma-rw.trace->extras-of-rw.force-trace)
  (%autoprove forcing-rw.tracep-of-rw.force-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.force-trace)

  (local (%disable default rw.force-trace))
  (local (%enable default
                  lemma-rw.trace->method-of-rw.force-trace
                  lemma-rw.trace->subtraces-of-rw.force-trace
                  lemma-rw.trace->extras-of-rw.force-trace))

  (%autoprove lemma-forcing-rw.force-tracep-of-rw.force-trace
              (%enable default rw.force-tracep))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.force-trace
              (%enable default
                       rw.trace-step-okp
                       lemma-forcing-rw.force-tracep-of-rw.force-trace))

  (%autoprove forcing-rw.trace-okp-of-rw.force-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.force-trace hypbox lhs)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.force-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.force-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.force-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.force-trace hypbox lhs)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.force-trace))

  (%autoprove rw.collect-forced-goals-of-rw.force-trace
              (%restrict default definition-of-rw.collect-forced-goals
                         (equal x '(rw.force-trace hypbox lhs)))))





(defsection rw.weakening-trace

  (%autoadmit rw.weakening-trace)

  (local (%enable default rw.weakening-trace))

  (%autoprove rw.weakening-trace-under-iff)
  (%autoprove lemma-rw.trace->method-of-rw.weakening-trace)
  (%autoprove rw.trace->hypbox-of-rw.weakening-trace)
  (%autoprove rw.trace->lhs-of-rw.weakening-trace)
  (%autoprove rw.trace->rhs-of-rw.weakening-trace)
  (%autoprove forcing-rw.trace->iffp-of-rw.weakening-trace)
  (%autoprove lemma-rw.trace->subtraces-of-rw.weakening-trace)
  (%autoprove lemma-rw.trace->extras-of-rw.weakening-trace)
  (%autoprove forcing-rw.tracep-of-rw.weakening-trace)
  (%autoprove forcing-rw.trace-atblp-of-rw.weakening-trace)

  (local (%disable default rw.weakening-trace))
  (local (%enable default
                  lemma-rw.trace->method-of-rw.weakening-trace
                  lemma-rw.trace->subtraces-of-rw.weakening-trace
                  lemma-rw.trace->extras-of-rw.weakening-trace))

  (%autoprove lemma-forcing-rw.weakening-tracep-of-rw.weakening-trace
              (%enable default rw.weakening-tracep))

  (%autoprove lemma-forcing-rw.trace-step-okp-of-rw.weakening-trace
              (%enable default
                       rw.trace-step-okp
                       lemma-forcing-rw.weakening-tracep-of-rw.weakening-trace))

  (%autoprove forcing-rw.trace-okp-of-rw.weakening-trace
              (%restrict default definition-of-rw.trace-okp (equal x '(rw.weakening-trace hypbox trace)))
              (%enable default lemma-forcing-rw.trace-step-okp-of-rw.weakening-trace))

  (%autoprove lemma-forcing-rw.trace-step-env-okp-of-rw.weakening-trace
              (%enable default rw.trace-step-env-okp))

  (%autoprove forcing-rw.trace-env-okp-of-rw.weakening-trace
              (%restrict default definition-of-rw.trace-env-okp (equal x '(rw.weakening-trace hypbox trace)))
              (%enable default lemma-forcing-rw.trace-step-env-okp-of-rw.weakening-trace))

  (%autoprove rw.collect-forced-goals-of-rw.weakening-trace
              (%restrict default definition-of-rw.collect-forced-goals
                         (equal x '(rw.weakening-trace hypbox trace)))))



(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/crewrite-builders")

