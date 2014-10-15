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
(include-book "primitives-2")
(%interactive)



;; Less-Than and Addition.

(%autoprove |(< (+ a b) (+ a c))| (%use (build.axiom (axiom-less-than-of-plus-and-plus))))

(%autoprove |(< a (+ a b))|
            (%disable default
                      |(< (+ a b) (+ a c))|
                      |[OUTSIDE](< (+ a b) (+ a c))|)
            (%use (%instance (%thm |(< (+ a b) (+ a c))|) (b 0) (c b))))

(%autoprove |(< a (+ b a))|)

(%autoprove |(< (+ a b) a)|
            (%disable default
                      |(< (+ a b) (+ a c))|
                      |[OUTSIDE](< (+ a b) (+ a c))|)
            (%use (%instance (%thm |(< (+ a b) (+ a c))|) (c 0))))

(%autoprove |(< (+ b a) a)|)

(%autoprove |(< a (+ b c a))|)
(%autoprove |(< a (+ b a c))|)
(%autoprove |(< a (+ b c d a))|)
(%autoprove |(< a (+ b c a d))|)
(%autoprove |(< a (+ b c d e a))|)
(%autoprove |(< a (+ b c d a e))|)
(%autoprove |(< a (+ b c d e f a))|)
(%autoprove |(< a (+ b c d e a f))|)

(%autoprove |(< (+ a b) (+ c a))|)
(%autoprove |(< (+ b a) (+ c a))|)
(%autoprove |(< (+ b a) (+ a c))|)

(%autoprove |(< (+ a b) (+ c a d))|)
(%autoprove |(< (+ b a c) (+ d a))|)

(%autoprove |a <= b, c != 0 --> a < b+c| (%enable default zp))
(%autoprove |a <= b, c != 0 --> a < c+b|)

(%autoprove |a <= b, c != 0 --> a < c+b+d|
            ;; BOZO, why do I have to disable this?
            (%disable default [OUTSIDE]LESS-OF-ZERO-LEFT))
(%autoprove |a <= b, c != 0 --> a < c+d+b|
            (%disable default [OUTSIDE]LESS-OF-ZERO-LEFT))


(%autoprove |c < a, d <= b --> c+d < a+b|
            (%use (%instance (%thm transitivity-of-<-three) (a (+ c d)) (b (+ c b)) (c (+ a b)))))
(%autoprove |c < a, d <= b --> c+d < b+a|)

(%autoprove |c <= a, d < b --> c+d < a+b|
            (%use (%instance (%thm |c < a, d <= b --> c+d < a+b|) (c d) (a b) (d c) (b a))))
(%autoprove |c <= a, d < b --> c+d < b+a|)
(%autoprove |c <= a, d <= b --> c+d <= a+b|
            (%use (%instance (%thm transitivity-of-<-four) (a (+ c d)) (b (+ c b)) (c (+ a b)))))
(%autoprove |c <= a, d <= b --> c+d <= b+a|)

