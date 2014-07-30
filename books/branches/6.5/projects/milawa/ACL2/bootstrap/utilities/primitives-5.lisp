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
(include-book "primitives-4")
(%interactive)


;; Subtraction.

(%autoprove natp-of-minus
            (%use (build.axiom (axiom-natp-of-minus))))

(%autoprove minus-under-iff
            (local (%disable default natp-of-minus [outside]natp-of-minus))
            (%use (%thm natp-of-minus)))

(%autoprove minus-when-not-less
            (%use (build.axiom (axiom-minus-when-subtrahend-as-large))))

(%autoprove minus-of-self)

(%autoprove minus-of-zero-left)

(%autoprove minus-cancels-summand-right
            (%use (build.axiom (axiom-minus-cancels-summand-right))))

(%autoprove minus-of-zero-right
            (%enable default nfix)
            (%disable default minus-cancels-summand-right [outside]minus-cancels-summand-right)
            (%use (%instance (%thm minus-cancels-summand-right) (a a) (b 0))))

(%autoprove minus-cancels-summand-left
            (%disable default commutativity-of-+ nfix)
            (%eqsubst 't (+ a b) (+ b a)))

(%autoprove |(< (- a b) c)| (%use (build.axiom (axiom-less-of-minus-left))))
(%autoprove |(< a (- b c))| (%use (build.axiom (axiom-less-of-minus-right))))
(%disable default |[OUTSIDE](< a (- b c))|) ;; interferes with constant gathering

(%autoprove |(+ a (- b c))| (%use (build.axiom (axiom-plus-of-minus-right))))
(%autoprove |(+ (- a b) c)|)

(%autoprove |(- a (- b c))| (%use (build.axiom (axiom-minus-of-minus-right))))
(%autoprove |(- (- a b) c)| (%use (build.axiom (axiom-minus-of-minus-left))))
(%disable default |[OUTSIDE](- (- a b) c)|) ;; interferes with constant gathering

(%autoprove |(= (- a b) c)| (%use (build.axiom (axiom-equal-of-minus-property))))
(%autoprove |(= c (- a b))|)

(%autoprove |(- (+ a b) (+ a c))|)
(%autoprove |(- (+ a b) (+ c a))|)
(%autoprove |(- (+ b a) (+ c a))|)
(%autoprove |(- (+ b a) (+ a c))|)

(%autoprove |(- (+ a b) (+ c d a))|)

(%autoprove |a < b --> a <= b-1|
            (%enable default nfix))

(%autoprove minus-when-zp-left-cheap)

(%autoprove minus-when-zp-right-cheap)

(%autoprove minus-of-nfix-left)

(%autoprove minus-of-nfix-right)




;; Constant Gathering.  We break our normal forms when we can put two constants
;; next to one another, since they can then be evaluated away to make progress.

(%autoprove gather-constants-from-less-of-plus)

(%autoprove gather-constants-from-less-of-plus-two)

(%autoprove gather-constants-from-less-of-plus-and-plus)

(%autoprove lemma-for-gather-constants-from-equal-of-plus-and-plus)

(%autoprove lemma2-for-gather-constants-from-equal-of-plus-and-plus
            (%enable default nfix)
            (%auto)
            (%use (%instance (%thm trichotomy-of-<) (a c1) (b c2))))

(%autoprove gather-constants-from-equal-of-plus-and-plus
            (%use (%instance (%thm lemma-for-gather-constants-from-equal-of-plus-and-plus)))
            (%use (%instance (%thm lemma2-for-gather-constants-from-equal-of-plus-and-plus)))
            (%split))

(%autoprove gather-constants-from-equal-of-plus
            (%enable default nfix))

(%autoprove gather-constants-from-minus-of-plus)

(%autoprove gather-constants-from-minus-of-plus-two)

(%autoprove gather-constants-from-minus-of-plus-and-plus)

