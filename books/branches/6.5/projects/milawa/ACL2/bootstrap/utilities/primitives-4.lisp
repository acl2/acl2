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
(include-book "primitives-3")
(%interactive)


;; Equalities with Sums.

(%autoprove |(= a (+ a b))|
            (%enable default nfix)
            (%disable default |[OUTSIDE](< a (+ a b))|)
            (%auto)
            (%use (%thm |(< a (+ a b))|))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove |(= a (+ b a))|)

(%autoprove |lemma for (= (+ a b) (+ a c))|
            (%use (%instance (%thm |(< (+ a b) (+ a c))|) (a a) (b b) (c c)))
            (%use (%instance (%thm |(< (+ a b) (+ a c))|) (a a) (b c) (c b)))
            (%disable default |[OUTSIDE](< (+ a b) (+ a c))|)
            (%disable default |(< (+ a b) (+ a c))|))

(%autoprove |(= (+ a b) (+ a c))|
            (%enable default nfix)
            (%use (%instance (%thm |lemma for (= (+ a b) (+ a c))|)
                             (a a)
                             (b (nfix b))
                             (c (nfix c)))))

(%autoprove |(= (+ a b) (+ c a))|)
(%autoprove |(= (+ b a) (+ c a))|)
(%autoprove |(= (+ b a) (+ a c))|)

(%autoprove |(= 0 (+ a b))|
            (%use (%instance (%thm |(< (+ a b) (+ a c))|) (a b) (b 0) (c a)))
            (%disable default
                      |(< (+ a b) (+ a c))|
                      |[OUTSIDE](< (+ a b) (+ a c))|)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove |lemma for (= (+ a x b) (+ c x d))|)

(%autoprove |(= (+ a x b) (+ c x d))|
            (%use (%instance (%thm |lemma for (= (+ a x b) (+ c x d))|)
                             (e a) (b x) (c b) (d c) (f d))))

(%autoprove squeeze-law-one
            (%enable default nfix))

(%autoprove squeeze-law-two
            (%enable default nfix))

(%autoprove squeeze-law-three
            (%enable default nfix))

