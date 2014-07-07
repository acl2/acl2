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
(include-book "utilities-5-prefixp")
(include-book "utilities-5-firstn")
(include-book "utilities-5-restn")
(include-book "utilities-5-first-index")
(include-book "utilities-5-mapp")
(%interactive)



(%autoprove nth-of-first-index-of-domain-and-range
            (%cdr-induction x)
            (%restrict default firstn (equal n 'n)))

(%autoprove prefixp-of-firstn
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))

(%autoprove prefixp-of-firstn-unusual
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))

(%autoprove app-of-firstn-and-restn
            (%autoinduct restn)
            (%restrict default firstn (equal n 'n))
            (%restrict default restn (equal n 'n)))

(%autoprove lemma-for-equal-of-app-with-firstn-and-restn)

(%autoprove lemma-2-for-equal-of-app-with-firstn-and-restn)

(%autoprove lemma-3-for-equal-of-app-with-firstn-and-restn)

(%autoprove lemma-4-for-equal-of-app-with-firstn-and-restn
            (%enable default lemma-3-for-equal-of-app-with-firstn-and-restn)
            (%use (%instance (%thm lemma-for-equal-of-app-with-firstn-and-restn)
                             (n (len y))
                             (x x)))
            (%use (%instance (%thm lemma-2-for-equal-of-app-with-firstn-and-restn)
                             (n (len y))
                             (y (list-fix y))))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove equal-of-app-with-firstn-and-restn
            (%enable default lemma-4-for-equal-of-app-with-firstn-and-restn)
            (%use (%instance (%thm lemma-for-equal-of-app-with-firstn-and-restn))))
