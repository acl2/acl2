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
(include-book "list-list-fix")
(%interactive)


(%autoadmit slow-simple-flatten)

(%autoprove slow-simple-flatten-when-not-consp
            (%restrict default slow-simple-flatten (equal x 'x)))

(%autoprove slow-simple-flatten-of-cons
            (%restrict default slow-simple-flatten (equal x '(cons a x))))

(%autoadmit fast-simple-flatten$)

(%autoadmit simple-flatten)

(%autoprove lemma-for-definition-of-simple-flatten
            (%autoinduct fast-simple-flatten$)
            (%restrict default fast-simple-flatten$ (equal x 'x)))

(%autoprove definition-of-simple-flatten
            (%enable default simple-flatten lemma-for-definition-of-simple-flatten))

(%autoprove simple-flatten-when-not-consp
            (%restrict default definition-of-simple-flatten (equal x 'x)))

(%autoprove simple-flatten-of-cons
            (%restrict default definition-of-simple-flatten (equal x '(cons a x))))

(%autoprove true-listp-of-simple-flatten
            (%cdr-induction x))

(%autoprove simple-flatten-of-list-fix
            (%cdr-induction x))

(%autoprove simple-flatten-of-app
            (%cdr-induction x))

(%autoprove simple-flatten-of-list-list-fix
            (%cdr-induction x))

(%autoprove forcing-fast-simple-flatten$-removal
            (%autoinduct fast-simple-flatten$)
            (%restrict default fast-simple-flatten$ (equal x 'x)))


(%autoadmit fast-simple-flatten-of-domain$)

(%autoprove fast-simple-flatten-of-domain$-removal
            (%autoinduct fast-simple-flatten-of-domain$)
            (%restrict default fast-simple-flatten-of-domain$ (equal x 'x)))

(%autoadmit fast-simple-flatten-of-range$)

(%autoprove fast-simple-flatten-of-range$-removal
            (%autoinduct fast-simple-flatten-of-range$)
            (%restrict default fast-simple-flatten-of-range$ (equal x 'x)))

(%ensure-exactly-these-rules-are-missing "../../utilities/simple-flatten")