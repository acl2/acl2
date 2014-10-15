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
(include-book "substitute-term-1")
(%interactive)


(%autoprove lemma-for-forcing-logic.term-atblp-of-logic.substitute
            (%logic.term-induction flag x)
            (%auto)
            ;; BOZO yuck, why is this broken and how can we fix it?
            ;; Hey, is this one of those rules that we were supposed to
            ;; force both hyps on, but didn't?  I think we complained
            ;; about a couple back in terms.lisp.  Go check!
            (%use (%thm forcing-logic.term-atblp-of-logic.lambda-body)))

(%autoprove forcing-logic.term-atblp-of-logic.substitute
            (%use (%instance (%thm lemma-for-forcing-logic.term-atblp-of-logic.substitute) (flag 'term))))

(%autoprove forcing-logic.term-list-atblp-of-logic.substitute-list
            (%use (%instance (%thm lemma-for-forcing-logic.term-atblp-of-logic.substitute) (flag 'list))))

