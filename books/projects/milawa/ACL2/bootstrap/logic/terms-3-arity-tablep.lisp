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
(include-book "terms-2")
(%interactive)

(%defmap :map (logic.arity-tablep x)
         :key (logic.function-namep x)
         :val (natp x)
         :key-list (logic.function-symbol-listp x)
         :val-list (nat-listp x)
         :val-of-nil nil)

(%autoprove logic.arity-tablep-of-halve-list
            (%disable default
                      halve-list-correct
                      [outside]halve-list-correct
                      logic.arity-tablep-of-list-fix
                      [outside]logic.arity-tablep-of-list-fix
                      logic.arity-tablep-of-subset-when-logic.arity-tablep)
            (%use (%instance (%thm halve-list-correct)))
            (%use (%instance (%thm logic.arity-tablep-of-list-fix)))
            (%auto :strategy (cleanup split urewrite))
            (%fertilize (list-fix x)
                        (app (rev (car (halve-list x)))
                             (cdr (halve-list x))))
            (%auto)
            (%fertilize (list-fix x)
                        (app (rev (car (halve-list x)))
                             (cdr (halve-list x))))
            (%auto))

(%autoprove logic.arity-tablep-of-halve-list-1
            (%use (%instance (%thm logic.arity-tablep-of-halve-list))))

(%autoprove logic.arity-tablep-of-halve-list-2
            (%use (%instance (%thm logic.arity-tablep-of-halve-list))))

(%autoprove logic.arity-tablep-of-merge-maps
            (%autoinduct merge-maps x y)
            (%restrict default merge-maps (and (equal x 'x) (equal y 'y)))
            (%disable default
                      logic.arity-tablep-of-subset-when-logic.arity-tablep
                      LOGIC.ARITY-TABLEP-WHEN-NOT-CONSP))

(%autoprove logic.arity-tablep-of-mergesort-map
            (%autoinduct mergesort-map)
            (%restrict default mergesort-map (equal x 'x))
            (%disable default
                      logic.arity-tablep-of-subset-when-logic.arity-tablep
                      LOGIC.ARITY-TABLEP-WHEN-NOT-CONSP
                      MERGESORT-MAP-WHEN-NOT-CONSP-OF-CDR
                      MERGESORT-MAP-WHEN-NOT-CONSP
                      ))
