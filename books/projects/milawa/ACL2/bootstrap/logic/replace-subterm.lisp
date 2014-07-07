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
(include-book "substitute-term")
(%interactive)


(%autoadmit logic.flag-replace-subterm)
(%autoadmit logic.replace-subterm)
(%autoadmit logic.replace-subterm-list)

(%autoprove definition-of-logic.replace-subterm
            (%restrict default logic.flag-replace-subterm (or (equal x 'x) (equal x 'old)))
            (%enable default logic.replace-subterm logic.replace-subterm-list)
            ;; Causes a rlimit loop
            (%disable default forcing-logic.function-of-logic.function-name-and-logic.function-args-free))

(%autoprove definition-of-logic.replace-subterm-list
            (%restrict default logic.flag-replace-subterm (equal x 'x))
            (%enable default logic.replace-subterm logic.replace-subterm-list))

(%autoprove logic.flag-replace-subterm-of-term-removal
            (%enable default logic.replace-subterm))

(%autoprove logic.flag-replace-subterm-of-list-removal
            (%enable default logic.replace-subterm-list))

(%autoprove logic.replace-subterm-list-when-not-consp
            (%restrict default definition-of-logic.replace-subterm-list (equal x 'x)))

(%autoprove logic.replace-subterm-list-of-cons
            (%restrict default definition-of-logic.replace-subterm-list (equal x '(cons a x))))

(%defprojection :list (logic.replace-subterm-list x old new)
                :element (logic.replace-subterm x old new))



(%autoprove lemma-for-forcing-logic.termp-of-logic.replace-subterm
            (%logic.term-induction flag x)
            (%auto)
            (%restrict default definition-of-logic.replace-subterm (equal x 'x)))

(%autoprove forcing-logic.termp-of-logic.replace-subterm
            (%use (%instance (%thm lemma-for-forcing-logic.termp-of-logic.replace-subterm)
                             (flag 'term))))

(%autoprove forcing-logic.term-listp-of-logic.replace-subterm-list
            (%use (%instance (%thm lemma-for-forcing-logic.termp-of-logic.replace-subterm)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.term-atblp-of-logic.replace-subterm
            (%logic.term-induction flag x)
            (%auto)
            (%restrict default definition-of-logic.replace-subterm (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-logic.replace-subterm
            (%use (%instance (%thm lemma-for-forcing-logic.term-atblp-of-logic.replace-subterm)
                             (flag 'term))))

(%autoprove forcing-logic.term-list-atblp-of-logic.replace-subterm-list
            (%use (%instance (%thm lemma-for-forcing-logic.term-atblp-of-logic.replace-subterm)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.substitute-of-logic.replace-subterm-with-fresh-variable
            (%logic.term-induction flag x)
            (%auto)
            (%restrict default definition-of-logic.replace-subterm (equal x 'x)))

(%autoprove forcing-logic.substitute-of-logic.replace-subterm-with-fresh-variable
            (%use (%instance (%thm lemma-for-forcing-logic.substitute-of-logic.replace-subterm-with-fresh-variable)
                             (flag 'term))))

(%autoprove forcing-logic.substitute-of-logic.replace-subterm-list-with-fresh-variable
            (%use (%instance (%thm lemma-for-forcing-logic.substitute-of-logic.replace-subterm-with-fresh-variable)
                             (flag 'list))))




(%defprojection :list (logic.replace-subterm-list-list x old new)
                :element (logic.replace-subterm-list x old new))

(%autoprove forcing-logic.term-list-listp-of-logic.replace-subterm-list-list                (%cdr-induction x))
(%autoprove forcing-logic.term-list-list-atblp-of-logic.replace-subterm-list-list           (%cdr-induction x))
(%autoprove cons-listp-of-logic.replace-subterm-list-list                                   (%cdr-induction x))
(%autoprove forcing-logic.substitute-of-logic.replace-subterm-list-list-with-fresh-variable (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../logic/replace-subterm")

