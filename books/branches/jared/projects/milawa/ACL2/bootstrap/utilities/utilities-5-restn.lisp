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
(include-book "utilities-4")
(%interactive)

(%autoadmit restn)

(%autoprove restn-of-zero
            (%restrict default restn (equal n ''0)))

(%autoprove restn-of-one
            (%restrict default restn (equal n ''1)))

(%autoprove true-listp-of-restn
            (%autoinduct restn)
            (%restrict default restn (equal n 'n)))

(%autoprove consp-of-restn
            (%autoinduct restn)
            (%restrict default restn (equal n 'n)))

(%autoprove restn-under-iff
            (%autoinduct restn)
            (%restrict default restn (equal n 'n)))

(%autoprove restn-of-list-fix
            (%autoinduct restn)
            (%restrict default restn (equal n 'n)))

(%autoprove restn-when-not-natp
            (%autoinduct restn)
            (%restrict default restn (equal n 'n)))

(%autoprove restn-of-app
            (%autoinduct restn)
            (%restrict default restn (equal n 'n)))

(%autoprove subsetp-of-restn
            (%autoinduct restn)
            (%restrict default restn (equal n 'n)))

(%autoprove restn-of-len
            (%cdr-induction x))

;; See also utilities-5.lisp for more theorems about restn
