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
(include-book "urewrite-builders")
(include-book "crewrite-builders")
(include-book "fast-assms")
(%interactive)

(%autoprove lookup-of-rev-when-uniquep-of-domain
            (%cdr-induction x))

(%autoprove lemma-for-logic.substitute-of-rev-when-unique
            (%logic.term-induction flag x))

(%autoprove logic.substitute-of-rev-when-unique
            (%use (%instance (%thm lemma-for-logic.substitute-of-rev-when-unique)
                             (flag 'term))))

(%autoprove logic.substitute-list-of-rev-when-unique
            (%use (%instance (%thm lemma-for-logic.substitute-of-rev-when-unique)
                             (flag 'list))))




(%defaggregate rw.ftrace
  (rhs fgoals)
  :require ((logic.termp-of-rw.ftrace->rhs            (logic.termp rhs))
            (logic.formula-listp-of-rw.ftrace->fgoals (logic.formula-listp fgoals))
            (true-listp-of-rw.ftrace->fgoals          (true-listp fgoals))))

(%defaggregate rw.ftraces
  (rhses fgoals)
  :require ((logic.term-listp-of-rw.ftraces->rhses     (logic.term-listp rhses))
            (true-listp-of-rw.ftraces->rhses           (true-listp rhses))
            (logic.formula-listp-of-rw.ftraces->fgoals (logic.formula-listp fgoals))
            (true-listp-of-rw.ftraces->fgoals          (true-listp fgoals))))

(%autoprove equal-of-rw.ftraces-and-rw.ftraces
            (%enable default rw.ftraces))



(defsection rw.trace-fast-image
  (%autoadmit rw.trace-fast-image)
  (local (%enable default rw.trace-fast-image))
  (%autoprove rw.trace-fast-image-under-iff)
  (%autoprove rw.ftracep-of-rw.trace-fast-image)
  (%autoprove rw.ftrace->rhs-of-rw.trace-fast-image)
  (%autoprove rw.ftrace->rhs-of-rw.trace-fast-image-free)
  (%autoprove rw.ftrace->fgoals-of-rw.trace-fast-image)
  (%autoprove rw.ftrace->fgoals-of-rw.trace-fast-image-free))



(defsection rw.trace-list-fast-image
  (%autoadmit rw.trace-list-fast-image)
  (local (%enable default rw.trace-list-fast-image))
  (%autoprove rw.ftracesp-of-rw.trace-list-fast-image)
  (%autoprove rw.ftraces->rhses-of-rw.trace-list-fast-image)
  (%autoprove rw.ftraces->fgoals-of-rw.trace-list-fast-image)
  (%autoprove rw.ftraces->rhses-of-rw.trace-list-fast-image-free)
  (%autoprove rw.ftraces->fgoals-of-rw.trace-list-fast-image-free)
  (%autoprove rw.trace-list-fast-image-of-cons))



(defsection rw.fast-fail-trace
  (%autoadmit rw.fast-fail-trace)
  (local (%enable default rw.fast-fail-trace))
  (%autoprove rw.fast-fail-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-fail-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-fail-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-fail-trace)
  (%autoprove rw.trace-fast-image-of-rw.fail-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-transitivity-trace
  (%autoadmit rw.fast-transitivity-trace)
  (local (%enable default rw.fast-transitivity-trace))
  (%autoprove rw.fast-transitivity-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-transitivity-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-transitivity-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-transitivity-trace)
  (%autoprove rw.trace-fast-image-of-rw.transitivity-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-equiv-by-args-trace
  (%autoadmit rw.fast-equiv-by-args-trace)
  (local (%enable default rw.fast-equiv-by-args-trace))
  (%autoprove rw.fast-equiv-by-args-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.equiv-by-args-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-equiv-by-args-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-equiv-by-args-trace)
  (%autoprove rw.trace-fast-image-of-rw.equiv-by-args-trace
              (%enable default rw.trace-fast-image rw.trace-list-fast-image)))



(defsection rw.fast-lambda-equiv-by-args-trace
  (%autoadmit rw.fast-lambda-equiv-by-args-trace)
  (local (%enable default rw.fast-lambda-equiv-by-args-trace))
  (%autoprove rw.fast-lambda-equiv-by-args-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-lambda-equiv-by-args-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-lambda-equiv-by-args-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-lambda-equiv-by-args-trace)
  (%autoprove rw.trace-fast-image-of-rw.lambda-equiv-by-args-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-beta-reduction-trace
  (%autoadmit rw.fast-beta-reduction-trace)
  (local (%enable default rw.fast-beta-reduction-trace))
  (%autoprove rw.fast-beta-reduction-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-beta-reduction-trace)
  (%autoprove forcing-rw.ftrace->rhs-of-rw.fast-beta-reduction-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-beta-reduction-trace)
  (%autoprove rw.trace-fast-image-of-rw.beta-reduction-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-try-ground-simplify
  (%autoadmit rw.fast-try-ground-simplify)
  (local (%enable default rw.fast-try-ground-simplify))
  (%autoprove rw.ftracep-of-rw.fast-try-ground-simplify)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-try-ground-simplify)
  (%autoprove rw.trace-fast-image-of-rw.try-ground-simplify
              (%enable default
                       rw.trace-fast-image
                       rw.try-ground-simplify
                       definition-of-rw.collect-forced-goals)))



(defsection rw.fast-if-specialcase-nil-trace
  (%autoadmit rw.fast-if-specialcase-nil-trace)
  (%enable default rw.fast-if-specialcase-nil-trace)
  (%autoprove rw.fast-if-specialcase-nil-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-if-specialcase-nil-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-if-specialcase-nil-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-if-specialcase-nil-trace)
  (%autoprove rw.trace-fast-image-of-rw.if-specialcase-nil-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-if-specialcase-t-trace
  (%autoadmit rw.fast-if-specialcase-t-trace)
  (local (%enable default rw.fast-if-specialcase-t-trace))
  (%autoprove rw.fast-if-specialcase-t-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-if-specialcase-t-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-if-specialcase-t-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-if-specialcase-t-trace)
  (%autoprove rw.trace-fast-image-of-rw.if-specialcase-t-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-not-trace
  (%autoadmit rw.fast-not-trace)
  (local (%enable default rw.fast-not-trace))
  (%autoprove rw.fast-not-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-not-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-not-trace)
  (%autoprove rw.trace-fast-image-of-rw.not-trace
              (%enable default
                       rw.trace-fast-image
                       rw.not-trace
                       definition-of-rw.collect-forced-goals)))



(defsection rw.fast-negative-if-trace
  (%autoadmit rw.fast-negative-if-trace)
  (local (%enable default rw.fast-negative-if-trace))
  (%autoprove rw.fast-negative-if-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-negative-if-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-negative-if-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-negative-if-trace)
  (%autoprove rw.trace-fast-image-of-rw.negative-if-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-crewrite-if-specialcase-same-trace
  (%autoadmit rw.fast-crewrite-if-specialcase-same-trace)
  (local (%enable default rw.fast-crewrite-if-specialcase-same-trace))
  (%autoprove rw.fast-crewrite-if-specialcase-same-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-crewrite-if-specialcase-same-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-crewrite-if-specialcase-same-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-crewrite-if-specialcase-same-trace)
  (%autoprove rw.trace-fast-image-of-rw.crewrite-if-specialcase-same-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-crewrite-if-generalcase-trace
  (%autoadmit rw.fast-crewrite-if-generalcase-trace)
  (local (%enable default rw.fast-crewrite-if-generalcase-trace))
  (%autoprove rw.fast-crewrite-if-generalcase-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-crewrite-if-generalcase-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-crewrite-if-generalcase-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-crewrite-if-generalcase-trace)
  (%autoprove rw.trace-fast-image-of-rw.crewrite-if-generalcase-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-assumptions-trace
  (%autoadmit rw.fast-assumptions-trace)
  (local (%enable default rw.fast-assumptions-trace))
  (%autoprove forcing-rw.ftracep-of-rw.fast-assumptions-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-assumptions-trace)

  (%autoprove rw.trace-fast-image-of-rw.assumptions-trace
              (%enable default
                       rw.trace-fast-image
                       rw.assms-fast-image
                       rw.assumptions-trace
                       definition-of-rw.collect-forced-goals)
              (%auto)
              (%disable default forcing-logic.termp-of-rw.eqtrace->lhs)
              (%use (%instance (%thm forcing-logic.termp-of-rw.eqtrace->lhs)
                               (x (rw.try-equiv-database lhs (rw.assms->eqdatabase assms) iffp)))))

  (%autoprove lemma-for-rw.fast-assumptions-trace-of-rw.assms-fast-image
              (%enable default definition-of-rw.eqtracep rw.eqtrace->lhs))

  (%autoprove rw.fast-assumptions-trace-of-rw.assms-fast-image
              (%enable default
                       rw.assumptions-trace
                       rw.fast-assumptions-trace
                       rw.assms-fast-image
                       rw.trace-fast-image
                       definition-of-rw.collect-forced-goals
                       lemma-for-rw.fast-assumptions-trace-of-rw.assms-fast-image)))



(defsection rw.fast-crewrite-rule-trace
  (%autoadmit rw.fast-crewrite-rule-trace)
  (local (%enable default rw.fast-crewrite-rule-trace))
  (%autoprove rw.fast-crewrite-rule-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-crewrite-rule-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-crewrite-rule-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-crewrite-rule-trace)
  (%autoprove rw.trace-fast-image-of-rw.crewrite-rule-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-force-trace
  (%autoadmit rw.fast-force-trace)
  (local (%enable default rw.fast-force-trace))
  (%autoprove rw.fast-force-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-force-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-force-trace)
  (%autoprove rw.trace-fast-image-of-rw.force-trace
              (%enable default
                       rw.trace-fast-image
                       rw.trace-formula
                       rw.trace-conclusion-formula)))



(defsection rw.fast-weakening-trace
  (%autoadmit rw.fast-weakening-trace)
  (local (%enable default rw.fast-weakening-trace))
  (%autoprove rw.fast-weakening-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-weakening-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-weakening-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-weakening-trace)
  (%autoprove rw.trace-fast-image-of-rw.weakening-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-urewrite-if-specialcase-same-trace
  (%autoadmit rw.fast-urewrite-if-specialcase-same-trace)
  (local (%enable default rw.fast-urewrite-if-specialcase-same-trace))
  (%autoprove rw.fast-urewrite-if-specialcase-same-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-urewrite-if-specialcase-same-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-urewrite-if-specialcase-same-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-urewrite-if-specialcase-same-trace)
  (%autoprove rw.trace-fast-image-of-rw.urewrite-if-specialcase-same-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-urewrite-if-generalcase-trace
  (%autoadmit rw.fast-urewrite-if-generalcase-trace)
  (local (%enable default rw.fast-urewrite-if-generalcase-trace))
  (%autoprove rw.fast-urewrite-if-generalcase-trace-under-iff)
  (%autoprove forcing-rw.ftracep-of-rw.fast-urewrite-if-generalcase-trace)
  (%autoprove rw.ftrace->rhs-of-rw.fast-urewrite-if-generalcase-trace)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-urewrite-if-generalcase-trace)
  (%autoprove rw.trace-fast-image-of-rw.urewrite-if-generalcase-trace
              (%enable default rw.trace-fast-image)))



(defsection rw.fast-try-urewrite-rule
  (%autoadmit rw.fast-try-urewrite-rule)
  (local (%enable default rw.fast-try-urewrite-rule))
  (%autoprove forcing-rw.ftracep-of-rw.fast-try-urewrite-rule)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-try-urewrite-rule)
  (%autoprove rw.trace-fast-image-of-rw.try-urewrite-rule
              (%enable default
                       rw.trace-fast-image
                       rw.try-urewrite-rule
                       definition-of-rw.collect-forced-goals)))


(defsection rw.fast-try-urewrite-rule-list
  (%autoadmit rw.fast-try-urewrite-rule-list)
  (%autoprove forcing-rw.ftracep-of-rw.fast-try-urewrite-rule-list
              (%cdr-induction rules)
              (%restrict default rw.fast-try-urewrite-rule-list (equal rules 'rules)))
  (%autoprove rw.ftrace->fgoals-of-rw.fast-try-urewrite-rule-list
              ;; BOZO poorly named variable, "rule", should be called "rules"
              (%cdr-induction rule)
              (%restrict default rw.fast-try-urewrite-rule-list (equal rules 'rule)))
  (%autoprove rw.trace-fast-image-of-rw.try-urewrite-rule-list
              (%cdr-induction rules)
              (%restrict default rw.fast-try-urewrite-rule-list (equal rules 'rules))
              (%restrict default rw.try-urewrite-rule-list (equal rules 'rules))
              (%auto)
              ;; BOZO this is really ugly.  Fix up the ACL2 proof and this, too.
              (%enable default
                       rw.fast-try-urewrite-rule
                       rw.try-urewrite-rule
                       rw.trace-fast-image
                       definition-of-rw.collect-forced-goals)))



(defsection rw.fast-try-urewrite-rules
  (%autoadmit rw.fast-try-urewrite-rules)
  (local (%enable default rw.fast-try-urewrite-rules))
  (%autoprove forcing-rw.ftracep-of-rw.fast-try-urewrite-rules)
  (%autoprove rw.ftrace->fgoals-of-rw.fast-try-urewrite-rules)
  (%autoprove rw.trace-fast-image-of-rw.try-urewrite-rules
              (%enable default rw.try-urewrite-rules)))



(defsection rw.maybe-extend-fast-trace
  (%autoadmit rw.maybe-extend-fast-trace)
  (local (%enable default rw.maybe-extend-fast-trace))
  (%autoprove rw.ftracep-of-rw.maybe-extend-fast-trace)
  (%autoprove rw.trace-fast-image-of-rw.maybe-extend-trace
              (%enable default rw.maybe-extend-trace)))




(defsection rw.trace-fast-image-equivalence-lemmas

  (%autoprove equiv-lemma-rw.try-ground-simplify-under-iff
              (%enable default rw.try-ground-simplify rw.fast-try-ground-simplify))

  (%autoprove equiv-lemma-rw.trace->rhs-of-rw.try-ground-simplify
              (%enable default rw.try-ground-simplify rw.fast-try-ground-simplify))

  (%autoprove equiv-lemma-rw.try-urewrite-rule-list-under-iff
              (%cdr-induction rules)
              (%restrict default rw.try-urewrite-rule-list (equal rules 'rules))
              (%restrict default rw.fast-try-urewrite-rule-list (equal rules 'rules))
              (%auto)
              (%enable default rw.try-urewrite-rule rw.fast-try-urewrite-rule))

  (%autoprove equiv-lemma-rw.try-urewrite-rules-under-iff
              (%enable default
                       equiv-lemma-rw.try-urewrite-rule-list-under-iff
                       rw.try-urewrite-rules
                       rw.fast-try-urewrite-rules))

  (%autoprove equiv-lemma-rw.trace->rhs-of-rw.try-urewrite-rule-list
              (%cdr-induction rules)
              (%restrict default rw.try-urewrite-rule-list (equal rules 'rules))
              (%restrict default rw.fast-try-urewrite-rule-list (equal rules 'rules))
              (%auto)
              (%enable default rw.try-urewrite-rule rw.fast-try-urewrite-rule))

  (%autoprove equiv-lemma-rw.trace->rhs-of-rw.try-urewrite-rules
              (%enable default
                       equiv-lemma-rw.trace->rhs-of-rw.try-urewrite-rule-list
                       rw.try-urewrite-rules
                       rw.fast-try-urewrite-rules))

  (%autoprove equiv-lemma-rw.trace->rhs-of-rw.not-trace
              (%enable default rw.not-trace rw.fast-not-trace))

  (%autoprove equiv-lemma-rw.ftrace->rhs-of-rw.maybe-extend-fast-trace
              (%enable default rw.maybe-extend-trace rw.maybe-extend-fast-trace))

  (%autoprove equiv-lemma-rw.trace->rhs-of-rw.maybe-extend-trace
              (%enable default rw.maybe-extend-trace))

  (%autoprove equiv-lemma-rw.ftrace->rhs-of-rw.maybe-extend-fast-trace-of-rw.trace-fast-image
              (%enable default rw.maybe-extend-trace rw.maybe-extend-fast-trace))

  (%create-theory rw.trace-fast-image-equivalence-lemmas)
  (%enable rw.trace-fast-image-equivalence-lemmas
           equiv-lemma-rw.try-ground-simplify-under-iff
           equiv-lemma-rw.trace->rhs-of-rw.try-ground-simplify
           equiv-lemma-rw.try-urewrite-rule-list-under-iff
           equiv-lemma-rw.try-urewrite-rules-under-iff
           equiv-lemma-rw.trace->rhs-of-rw.try-urewrite-rule-list
           equiv-lemma-rw.trace->rhs-of-rw.try-urewrite-rules
           equiv-lemma-rw.trace->rhs-of-rw.not-trace
           equiv-lemma-rw.ftrace->rhs-of-rw.maybe-extend-fast-trace
           equiv-lemma-rw.trace->rhs-of-rw.maybe-extend-trace
           equiv-lemma-rw.ftrace->rhs-of-rw.maybe-extend-fast-trace-of-rw.trace-fast-image))



(%ensure-exactly-these-rules-are-missing "../../rewrite/fast-traces")

