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
(include-book "utilities-3")
(%interactive)


(%autoadmit nth)

(%autoprove nth-when-zp
            (%restrict default nth (equal n 'n)))

(%autoprove nth-of-nfix
            (%restrict default nfix (memberp n '(n (nfix n)))))

(%autoprove nth-of-list-fix
            (%autoinduct nth)
            (%restrict default nth (equal n 'n)))

(%autoprove nth-when-index-too-large
            (%autoinduct nth)
            (%restrict default nth (equal n 'n)))

(%autoprove nth-of-increment
            (%restrict default nth (equal n '(+ '1 n))))

(%autoprove nth-of-app
            (%autoinduct nth)
            (%restrict default nth (equal n 'n)))

(%autoprove nth-of-rev
            (%cdr-induction x)
            (%restrict default nth (memberp n '((- n (len x2)) (- (len x2) n)))))

(%autoprove memberp-of-nth
            (%autoinduct nth)
            (%restrict default nth (equal n 'n)))

;; see also utilities-4.lisp for more theorems about nth

