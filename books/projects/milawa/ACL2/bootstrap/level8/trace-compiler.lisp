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
(include-book "collect-forced-goals")
(include-book "assumptions-compiler")
(include-book "beta-compiler")
(include-book "crewrite-if-general-compiler")
(include-book "crewrite-if-same-compiler")
(include-book "crewrite-rule-compiler")
(include-book "equiv-by-args-compiler")
(include-book "fail-compiler")
(include-book "force-compiler")
(include-book "ground-compiler")
(include-book "if-specialcase-nil-compiler")
(include-book "if-specialcase-t-compiler")
(include-book "lambda-compiler")
(include-book "negative-if-compiler")
(include-book "not-compiler")
(include-book "transitivity-compiler")
(include-book "urewrite-if-general-compiler")
(include-book "urewrite-if-same-compiler")
(include-book "urewrite-rule-compiler")
(include-book "weakening-compiler")
(include-book "trace-arities")
(%interactive)


(%autoadmit rw.compile-trace-step)

(encapsulate
 ()
 (local (%enable default
                 rw.trace-step-okp
                 rw.trace-step-env-okp
                 rw.compile-trace-step))
 (%autoprove rw.compile-trace-step-under-iff)
 (%autoprove forcing-logic.appealp-of-rw.compile-trace-step)
 (%autoprove forcing-logic.conclusion-of-rw.compile-trace-step)
 (%autoprove forcing-logic.proofp-of-rw.compile-trace-step))




(%autoadmit rw.flag-compile-trace)
(%autoadmit rw.compile-trace)
(%autoadmit rw.compile-trace-list)

(%autoprove definition-of-rw.compile-trace
            (%restrict default rw.flag-compile-trace (equal x 'x))
            (%enable default rw.compile-trace rw.compile-trace-list))

(%autoprove definition-of-rw.compile-trace-list
            (%restrict default rw.flag-compile-trace (equal x 'x))
            (%enable default rw.compile-trace rw.compile-trace-list))

(%autoprove rw.flag-compile-trace-of-term-removal
            (%enable default rw.compile-trace))

(%autoprove rw.flag-compile-trace-of-list-removal
            (%enable default rw.compile-trace-list))


(%autoprove lemma-for-forcing-logic.appealp-of-rw.compile-trace
            (%rw.trace-induction flag x)
            (%auto :strategy (cleanup split urewrite crewrite dist))
            (%restrict default definition-of-rw.compile-trace (equal x 'x))
            (%restrict default definition-of-rw.compile-trace-list (equal x 'x)))

(%autoprove forcing-logic.appealp-of-rw.compile-trace
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-rw.compile-trace)
                             (flag 'term))))

(%autoprove forcing-logic.conclusion-of-rw.compile-trace
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-rw.compile-trace)
                             (flag 'term))))

(%autoprove forcing-logic.appeal-listp-of-rw.compile-trace-list
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-rw.compile-trace)
                             (flag 'list))))

(%autoprove forcing-logic.strip-conclusions-of-rw.compile-trace-list
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-rw.compile-trace)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.proofp-of-rw.compile-trace
            (%rw.trace-induction flag x)

            ;; The case-split is too severe, but we can cut it down with some
            ;; selective urewriting.

            ;; BOZO this is pretty horrible.  It'd be nice if we could just tell
            ;; %auto to use a specific theory like temp, instead of having to mangle
            ;; default.  Also, I worry that the enabling might linearize the lookup
            ;; structure.  We should write some code to balance it.
            (%create-theory temp :copy-of default)

            (%disable default default)
            (%enable default
                     equal-of-nil-one
                     equal-of-nil-two
                     iff-of-nil-one
                     iff-of-nil-two
                     iff-of-t-left
                     iff-of-t-right
                     implies-of-self
                     implies-of-t-left
                     implies-of-t-right
                     implies-of-nil-left
                     implies-of-nil-right)
            (%auto :strategy (urewrite split))

            (%enable default temp)
            (%disable default
                      formula-decomposition
                      type-set-like-rules
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      same-length-prefixes-equal-cheap
                      expensive-term/formula-inference
                      unusual-consp-rules)

            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default definition-of-rw.compile-trace (equal x 'x))
            (%restrict default definition-of-rw.compile-trace-list (equal x 'x))
            (%auto :strategy (cleanup split urewrite crewrite))

            (%enable default
                     type-set-like-rules
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two))

(%autoprove forcing-logic.proofp-of-rw.compile-trace
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-rw.compile-trace)
                             (flag 'term))))

(%autoprove forcing-logic.proof-listp-of-rw.compile-trace
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-rw.compile-trace)
                             (flag 'list))))



(%autoadmit rw.compile-trace-okp)

(%autoprove forcing-logic.appeal-listp-of-logic.find-proofs
            (%cdr-induction formulas))

(%autoprove forcing-logic.strip-conclusions-of-logic.find-proofs
            (%cdr-induction formulas))

(%autoadmit rw.compile-trace-high)

(%autoprove rw.compile-trace-okp-of-rw.compile-trace-high
            (%enable default
                     rw.compile-trace-high
                     rw.compile-trace-okp))


(encapsulate
 ()
 (local (%enable default rw.compile-trace-okp))
 (%autoprove booleanp-of-rw.compile-trace-okp)
 (%autoprove rw.compile-trace-okp-of-logic.appeal-identity)
 (%autoprove lemma-0-for-soundness-of-rw.compile-trace-okp)
 (local (%enable default lemma-0-for-soundness-of-rw.compile-trace-okp))
 (%autoprove lemma-1-for-soundness-of-rw.compile-trace-okp
             (%forcingp nil))
 (%autoprove lemma-2-for-soundness-of-rw.compile-trace-okp)
 (%autoprove forcing-soundness-of-rw.compile-trace-okp
             (%enable default
                      lemma-1-for-soundness-of-rw.compile-trace-okp
                      lemma-2-for-soundness-of-rw.compile-trace-okp)
             (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                              (x (rw.compile-trace (logic.extras x)
                                                   defs
                                                   (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                                axioms thms atbl)))))))



(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/trace-compiler")


