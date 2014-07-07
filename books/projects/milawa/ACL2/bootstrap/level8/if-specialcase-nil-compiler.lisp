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
(include-book "trace-okp")
(%interactive)


;; BOZO this is local in clean-clauses.lisp.  Consider making this a disabled
;; rule that lives in utilities, and enabling it when we want.  Also consider
;; adding the alt-version in utilities.

(defthmd split-up-list-of-quoted-nil
  (equal (equal x '('nil))
         (and (consp x)
              (equal (car x) ''nil)
              (not (cdr x)))))

(defthmd split-up-list-of-quoted-nil-alt
  (equal (equal '('nil) x)
         (and (consp x)
              (equal (car x) ''nil)
              (not (cdr x)))))

(%autoprove split-up-list-of-quoted-nil)
(%autoprove split-up-list-of-quoted-nil-alt)

(%enable default
         split-up-list-of-quoted-nil
         split-up-list-of-quoted-nil-alt)



(local (%splitlimit 20)) ;; BOZO Consider this globally at this level

(%autoadmit rw.compile-if-specialcase-nil-trace)

(local (%enable default
                rw.if-specialcase-nil-tracep
                rw.compile-if-specialcase-nil-trace
                rw.trace-conclusion-formula
                rw.trace-formula
                equal-of-2-and-len))

(local (%disable default
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 type-set-like-rules
                 expensive-subsetp-rules
                 same-length-prefixes-equal-cheap
                 formula-decomposition
                 unusual-consp-rules
                 expensive-term/formula-inference))

(local (%disable default
                 logic.appealp-of-car-when-logic.appeal-listp
                 logic.appealp-of-second-when-logic.appeal-listp
                 logic.appealp-when-memberp-of-logic.appeal-listp
                 logic.appeal-listp-of-cdr-when-logic.appeal-listp
                 logic.proofp-when-memberp-of-logic.proof-listp
                 logic.proofp-of-car-when-logic.proof-listp
                 logic.proof-listp-of-cdr-when-logic.proof-listp
                 rw.tracep-of-car-when-rw.trace-listp
                 rw.trace-listp-of-cdr-when-rw.trace-listp
                 rw.trace-listp-when-not-consp
                 logic.appeal-listp-when-not-consp
                 logic.proofp-when-not-consp
                 logic.proof-listp-when-not-consp
                 logic.strip-conclusions-when-not-consp
                 rw.trace-list-formulas-when-not-consp
                 rw.tracep-when-memberp-of-rw.trace-listp
                 forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                 forcing-equal-of-logic.function-with-two-args-alt))

(local (%enable default
                ;; This rules were added to formula-decomposition and broke the proofs below.  We
                ;; just leave them all enabled.  It would be better to figure out which ones we
                ;; really need.  We could probably do that by profiling and experimentation.
                equal-of-logic.function-rewrite
                equal-logic.por-logic.por-rewrite
                forcing-equal-of-logic.function-with-three-args-alt
                equal-of-logic.function-rewrite-alt
                equal-logic.pequal-logic.pequal-rewrite
                [outside]equal-of-logic.function-and-logic.function
                [outside]equal-logic.pequal-logic.pequal-rewrite
                equal-logic.por-logic.por-rewrite
                [outside]equal-logic.por-logic.por-rewrite))


(%autoprove rw.compile-if-specialcase-nil-trace-under-iff)

(%autoprove logic.appealp-of-rw.compile-if-specialcase-nil-trace
            (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
            (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
            (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%forcingp nil)
            (%auto :strategy (split cleanup urewrite crewrite))
            (%enable default formula-decomposition)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pnots
                      aggressive-equal-of-logic.pors)
            (%auto :strategy (split cleanup urewrite crewrite))
            (%forcingp t))

(%autoprove logic.conclusion-of-rw.compile-if-specialcase-nil-trace
            (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
            (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
            (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%forcingp nil)
            (%auto :strategy (split cleanup urewrite crewrite))
            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pnots
                      aggressive-equal-of-logic.pors)
            (%forcingp t)
            (%crewrite default)
            (%forcingp nil)
            (%auto :strategy (split cleanup urewrite crewrite)))

(%autoprove logic.proofp-of-rw.compile-if-specialcase-nil-trace
            (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
            (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.proof-listp  (memberp x '(proofs (cdr proofs))))
            (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%forcingp nil)
            (%auto :strategy (split cleanup urewrite crewrite))
            (%enable default formula-decomposition)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pnots
                      aggressive-equal-of-logic.pors)
            (%forcingp t)
            (%crewrite default)
            (%forcingp nil)
            (%auto :strategy (split cleanup urewrite crewrite)))

