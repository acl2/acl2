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
(include-book "terms")
(%interactive)


(%deflist logic.all-functionsp (x)
          (logic.functionp x))

(%defprojection :list (logic.strip-function-names x)
                :element (logic.function-name x)
                :nil-preservingp t)

(%autoprove forcing-logic.function-symbol-listp-of-logic.strip-function-names
            (%cdr-induction x))


(%defprojection :list (logic.strip-function-args x)
                :element (logic.function-args x)
                :nil-preservingp t)

(%autoprove forcing-logic.term-list-listp-of-logic.strip-function-args
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-logic.strip-function-args
            (%cdr-induction x))

(%autoprove forcing-true-list-listp-of-logic.strip-function-args
            (%cdr-induction x))

(%autoprove logic.term-listp-of-strip-firsts-when-all-lens-2
            (%cdr-induction x))

(%autoprove logic.term-listp-of-strip-seconds-when-all-lens-2
            (%cdr-induction x))

(%autoprove logic.term-list-atblp-of-strip-firsts-when-all-lens-2
            (%cdr-induction x))

(%autoprove logic.term-list-atblp-of-strip-seconds-when-all-lens-2
            (%cdr-induction x))




(%defprojection
 ;; Interestingly this doesn't need the hint we used in ACL2, which was to disable
 ;; the rule equal-of-logic.function-rewrite.
 :list (logic.function-list name x)
 :element (logic.function name x))

(%autoprove forcing-logic.term-listp-of-logic.function-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-logic.function-list
            (%cdr-induction x))

(%autoprove forcing-logic.all-functionsp-of-logic.function-list
            (%cdr-induction x))

(%autoprove forcing-logic.strip-function-names-of-logic.function-list
            (%cdr-induction x))

(%autoprove forcing-logic.strip-function-args-of-logic.function-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-listp-list-of-list2-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.term-list-atblp-list-of-list2-list
            (%cdr-cdr-induction x y))

(%ensure-exactly-these-rules-are-missing "../../logic/fterm-lists")

