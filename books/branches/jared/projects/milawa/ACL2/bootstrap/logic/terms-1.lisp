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


(%autoadmit logic.variablep)

(%autoprove booleanp-of-logic.variablep
            (%enable default logic.variablep))

(%autoprove symbolp-when-logic.variablep
            (%enable default logic.variablep))

(%autoprove logic.variablep-when-consp
            (%enable default logic.variablep))



(%autoadmit logic.constantp)

(%autoprove booleanp-of-logic.constantp
            (%enable default logic.constantp))

(%autoprove logic.constantp-when-not-consp
            (%enable default logic.constantp))

(%autoprove logic.constantp-of-list-quote
            (%enable default logic.constantp))



(%autoadmit logic.unquote)

(%autoprove logic.unquote-of-list-quote
            (%enable default logic.unquote))

(%autoprove logic.unquote-under-iff-when-logic.constantp
            (%enable default logic.constantp logic.unquote))

(%autoprove equal-of-logic.unquote-and-logic.unquote
            (%enable default logic.constantp logic.unquote)
            (%restrict default tuplep (memberp n '('2 '1))))

(%autoprove logic.variablep-when-logic.constantp
            (%enable default logic.variablep logic.constantp))

(%autoprove logic.constantp-when-logic.variablep)


(%autoadmit logic.function-namep)

(%autoprove booleanp-of-logic.function-namep
            (%enable default logic.function-namep))

(%autoprove symbolp-when-logic.function-namep
            (%enable default logic.function-namep))

(%autoprove logic.function-namep-when-consp
            (%enable default logic.function-namep))

(%autoprove logic.constantp-when-cons-of-logic.function-namep
            (%enable default logic.constantp))

(%autoprove logic.variablep-of-cons-when-logic.function-namep
            (%enable default logic.variablep))

