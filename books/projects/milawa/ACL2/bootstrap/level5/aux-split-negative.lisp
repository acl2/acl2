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
(%interactive)


(%defderiv clause.aux-split-negative-1-bldr-lemma-1 :omit-okp t)

(encapsulate
 ()
 (%autoprove equal-when-logic.functionp-and-logic.functionp
             (%enable default logic.functionp logic.function-name logic.function-args))

 (%autoprove equal-of-one-tuples)

 (%autoprove equal-of-logic.function-args-and-logic.function-args-when-one-tuples
             (%use (%instance (%thm equal-of-one-tuples)
                              (x (logic.function-args x))
                              (y (logic.function-args y)))))

 (local (%enable default
                 equal-when-logic.functionp-and-logic.functionp
                 equal-of-one-tuples
                 equal-of-logic.function-args-and-logic.function-args-when-one-tuples))

 (%defderiv clause.aux-split-negative-1-bldr-lemma-2 :omit-okp t))


(%defderiv clause.aux-split-negative-1-bldr)


(%defderiv clause.aux-split-negative-2-bldr-lemma-1 :omit-okp t)

(encapsulate
 ()
 (local (%enable default
                 equal-when-logic.functionp-and-logic.functionp
                 equal-of-logic.function-args-and-logic.function-args-when-one-tuples))
 (%defderiv clause.aux-split-negative-2-bldr-lemma-2))


(%defderiv clause.aux-split-negative-2-bldr)

