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
(include-book "utilities-4-remove-all")
(include-book "utilities-4-disjointp")
(include-book "utilities-4-uniquep")
(include-book "utilities-4-difference")
(include-book "utilities-4-remove-duplicates")
(include-book "utilities-4-tuplep")
(include-book "utilities-4-repeat")
(include-book "utilities-4-nth")
(%interactive)



;; Extra theorems for disjointp.

(%autoprove disjointp-of-remove-all-of-remove-all-when-disjointp-right)

(%autoprove disjointp-of-remove-all-when-disjointp-left)



;; Extra theorems for uniquep.

(%autoprove uniquep-of-app
            (%cdr-induction x))

(%autoprove uniquep-of-rev
            (%cdr-induction x))

(%autoprove uniquep-of-remove-all-when-uniquep
            (%cdr-induction x))



;; Extra theorems for difference.

(%autoprove uniquep-of-difference-when-uniquep
            (%cdr-induction x))

(%autoprove disjointp-of-difference-with-y
            (%cdr-induction x))

(%autoprove disjointp-of-difference-with-y-alt
            (%cdr-induction x))



;; Extra theorems for remove-duplicates.

(%autoprove uniquep-of-remove-duplicates
            (%cdr-induction x))

(%autoprove remove-duplicates-of-difference
            (%cdr-induction x))

(%autoprove remove-duplicates-when-unique
            (%cdr-induction x))

(%autoprove app-of-remove-duplicates-with-unique-and-disjoint
            (%cdr-induction x))

(%autoprove remove-duplicates-of-remove-all
            (%cdr-induction x))

(%autoprove subsetp-of-remove-all-of-remove-duplicates)


;; Extra theorems for nth.

(%autoprove equal-of-nths-when-uniquep
            ;; This proof is pretty cool.  It has really improved over time as my
            ;; tactics have gotten better.
            (%induct (rank x)
                     ((not (consp x))
                      nil)
                     ((and (consp x)
                           (or (zp m)
                               (zp n)))
                      nil)
                     ((and (consp x)
                           (not (zp m))
                           (not (zp n)))
                      (((x (cdr x))
                        (n (- n 1))
                        (m (- m 1))))))
            (%restrict default nth (or (equal n 'n) (equal n 'm) (equal n ''0) (equal n ''1))))








