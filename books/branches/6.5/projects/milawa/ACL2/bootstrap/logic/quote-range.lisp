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
(include-book "groundp")
(%interactive)


(%autoadmit logic.quote-range)
(%autoprove logic.quote-range-when-not-consp                           (%restrict default logic.quote-range (equal x 'x)))
(%autoprove logic.quote-range-of-cons                                  (%restrict default logic.quote-range (equal x '(cons a x))))
(%autoprove true-listp-of-logic.quote-range                            (%cdr-induction x))
(%autoprove logic.quote-range-of-list-fix                              (%cdr-induction x))
(%autoprove len-of-logic.quote-range                                   (%cdr-induction x))
(%autoprove logic.quote-range-of-app                                   (%cdr-induction x))
(%autoprove forcing-logic.sigmap-of-logic.quote-range                  (%cdr-induction x))
(%autoprove forcing-logic.sigma-atblp-of-logic.quote-range             (%cdr-induction sigma))
(%autoprove forcing-logic.constant-listp-of-range-of-logic.quote-range (%cdr-induction x))
(%autoprove forcing-logic.ground-listp-of-range-of-logic.quote-range)
(%autoprove forcing-domain-of-logic.quote-range                        (%cdr-induction x))

(%ensure-exactly-these-rules-are-missing "../../logic/quote-range")

