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
(include-book "terms")
(%interactive)

(%defmap :map (logic.sigmap x)
         :key (logic.variablep x)
         :val (logic.termp x)
         :key-list (logic.variable-listp x)
         :val-list (logic.term-listp x)
         :val-of-nil nil)

(%autoprove forcing-logic.sigmap-of-pair-lists
            (%autoinduct pair-lists))


(%deflist logic.sigma-listp (x)
  (logic.sigmap x))

(%autoprove logic.sigmap-of-second-when-logic.sigma-listp)

(%autoprove forcing-logic.sigma-listp-of-revappend-onto-each
            (%cdr-induction x))



(%deflist logic.sigma-list-listp (x)
  (logic.sigma-listp x))

(%autoprove logic.sigma-listp-of-second-when-logic.sigma-list-listp)

(%autoprove forcing-logic.sigma-listp-of-simple-flatten
            (%cdr-induction x))

