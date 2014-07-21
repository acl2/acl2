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
(include-book "utilities")
(%interactive)


(%autoadmit ordered-subsetp)

(%autoprove ordered-subsetp-when-not-consp-one
            (%restrict default ordered-subsetp (equal y 'y)))

(%autoprove ordered-subsetp-when-not-consp-two
            (%restrict default ordered-subsetp (equal y 'y)))

(%autoprove ordered-subsetp-of-cons-and-cons
            (%restrict default ordered-subsetp (equal y '(cons b y))))

(%autoprove booleanp-of-ordered-subsetp
            (%autoinduct ordered-subsetp))

(%autoprove ordered-subsetp-of-cdr-when-ordered-subsetp
            (%induct (rank y)
                     ((or (not (consp x))
                          (not (consp y)))
                      nil)
                     ((and (consp x)
                           (consp y))
                      (((x (cdr x)) (y (cdr y)))
                       ((x x) (y (cdr y)))))))

(%autoprove ordered-subsetp-when-ordered-subsetp-of-cons
            (%use (%instance (%thm ordered-subsetp-of-cdr-when-ordered-subsetp)
                             (x (cons a x))
                             (y y))))

(%autoprove ordered-subsetp-of-cons-when-ordered-subsetp
            (%restrict default ordered-subsetp (equal y '(cons a y))))

(%autoprove ordered-subsetp-when-ordered-subsetp-of-cdr)

(%autoprove ordered-subsetp-is-reflexive
            (%cdr-induction x))

(%autoprove ordered-subsetp-is-transitive
            (%induct (+ (rank x) (+ (rank y) (rank z)))
                     ((or (not (consp x))
                          (not (consp y))
                          (not (consp z)))
                      nil)
                     ((and (consp x)
                           (consp y)
                           (consp z))
                      (((x (cdr x)) (y (cdr y)) (z (cdr z)))
                       ((x (cdr x)) (y (cdr y)) (z z))
                       ((x x) (y (cdr y)) (z (cdr z)))
                       ((x x) (y y) (z (cdr z))))))
            ;; These seem to be expensive here.  In fact this rewrite is pretty slow.
            (%disable default squeeze-law-two |a <= b, c != 0 --> a < c+b|))

(%autoprove ordered-subsetp-of-list-fix-one (%autoinduct ordered-subsetp))
(%autoprove ordered-subsetp-of-list-fix-two (%autoinduct ordered-subsetp))
(%autoprove ordered-subsetp-of-app-when-ordered-subsetp-one (%autoinduct ordered-subsetp))
(%autoprove ordered-subsetp-of-app-one)
(%autoprove ordered-subsetp-of-app-two (%cdr-induction y))
(%autoprove ordered-subsetp-of-app-when-ordered-subsetp-two)
(%autoprove subsetp-when-ordered-subsetp (%autoinduct ordered-subsetp))
(%autoprove ordered-subsetp-of-remove-duplicates (%cdr-induction x))
(%autoprove ordered-subsetp-of-remove-all (%cdr-induction x))
(%autoprove ordered-subsetp-of-difference (%cdr-induction x))

(%ensure-exactly-these-rules-are-missing "../../utilities/ordered-subsetp")