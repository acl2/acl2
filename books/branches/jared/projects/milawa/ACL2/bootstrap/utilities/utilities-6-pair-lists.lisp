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
(include-book "utilities-5")
(%interactive)



(%autoadmit pair-lists)

(%autoprove pair-lists-when-not-consp
            (%restrict default pair-lists (equal x 'x)))

(%autoprove pair-lists-of-cons-one
            (%restrict default pair-lists (equal x '(cons a x))))

(%autoprove pair-lists-of-cons-two
            (%restrict default pair-lists (equal y '(cons a y))))

(%autoprove true-listp-of-pair-lists
            (%autoinduct pair-lists))

(%autoprove pair-lists-of-list-fix-one
            (%autoinduct pair-lists))

(%autoprove pair-lists-of-list-fix-two
            (%autoinduct pair-lists))

(%autoprove domain-of-pair-lists
            (%autoinduct pair-lists))

(%autoprove range-of-pair-lists
            (%autoinduct pair-lists domain range))

(%autoprove lookup-of-pair-lists
            (%autoinduct pair-lists keys vals))

(%autoprove lookup-of-pair-lists-of-rev)

(%autoprove lookup-of-nth-in-pair-lists-when-unique-keys
            (%induct (rank x)
                     ((or (not (consp x))
                          (not (consp y)))
                      nil)
                     ((zp n)
                      nil)
                     ((and (consp x)
                           (consp y)
                           (not (zp n)))
                      (((n (- n 1))
                        (x (cdr x))
                        (y (cdr y))))))
            ;; somehow no urewrite saves a lot of conses
            (%auto :strategy (cleanup split crewrite)))



(%autoadmit fast-pair-lists$)

(%autoprove fast-pair-lists$-when-not-consp
            (%restrict default fast-pair-lists$ (equal x 'x)))

(%autoprove fast-pair-lists$-of-cons
            (%restrict default fast-pair-lists$ (equal x '(cons a x))))

(%autoprove forcing-fast-pair-lists$-removal
            (%autoinduct fast-pair-lists$)
            (%enable default fast-pair-lists$-when-not-consp fast-pair-lists$-of-cons))
