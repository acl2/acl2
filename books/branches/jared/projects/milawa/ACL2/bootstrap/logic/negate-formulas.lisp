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
(include-book "formulas")
(%interactive)


(%deflist logic.all-negationsp (x)
          (equal (logic.fmtype x) 'pnot*)
          :hintsmap ((logic.all-negationsp-of-remove-duplicates
                      (%cdr-induction x)
                      (%auto)
                      (%use (%instance (%thm equal-when-memberp-of-logic.all-negationsp)
                                       (a x1)
                                       (x x2))))
                     (logic.all-negationsp-of-subsetp-when-logic.all-negationsp
                      (%cdr-induction x)
                      (%auto)
                      (%use (%instance (%thm equal-when-memberp-of-logic.all-negationsp)
                                       (a x1)
                                       (x y))))))

(%autoprove logic.fmtype-of-car-when-logic.all-negationsp
            (%enable default equal-of-car-when-logic.all-negationsp))

(%autoprove logic.fmtype-when-memberp-of-logic.all-negationsp
            (%use (%instance (%thm equal-when-memberp-of-logic.all-negationsp))))

(%autoprove logic.fmtype-when-memberp-of-logic.all-negationsp-alt)



(%defprojection :list (logic.~args x)
                :element (logic.~arg x)
                :nil-preservingp t)


(%autoprove forcing-logic.formula-listp-of-logic.~args
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-logic.~args
            (%cdr-induction x))

(%autoprove logic.~arg-of-car-when-all-equalp-of-logic.~args)

(defsection logic.negate-formulas

  (local (%disable default
                   forcing-logic.formulap-of-logic.pnot
                   aggressive-equal-of-logic.pnots
                   forcing-equal-of-logic.pnot-rewrite
                   forcing-equal-of-logic.pnot-rewrite-two))

  (%defprojection :list (logic.negate-formulas x)
                  :element (logic.pnot x)))

(%autoprove memberp-of-logic.pnot-in-logic.negate-formulas
            (%enable default memberp-of-logic.pnot-in-logic.negate-formulas-when-memberp)
            (%cdr-induction x))

(%autoprove logic.formula-listp-of-logic.negate-formulas
            (%cdr-induction x))

(%autoprove logic.formula-list-atblp-of-logic.negate-formulas
            (%cdr-induction x))

(%autoprove equal-of-logic.negate-formulas-and-logic.negate-formulas
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.~args-of-logic.negate-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.~args-of-logic.negate-formulas-free)

(%autoprove forcing-logic.all-negationsp-of-logic.negate-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.all-negationsp-of-logic.negate-formulas-free)





(%autoadmit logic.smart-negate-formulas)

(%autoprove logic.smart-negate-formulas-when-not-consp (%restrict default logic.smart-negate-formulas (equal x 'x)))
(%autoprove logic.smart-negate-formulas-of-cons        (%restrict default logic.smart-negate-formulas (equal x '(cons a x))))

(%autoprove true-listp-of-logic.smart-negate-formulas  (%cdr-induction x))
(%autoprove logic.smart-negate-formulas-of-list-fix    (%cdr-induction x))
(%autoprove logic.smart-negate-formulas-of-app         (%cdr-induction x))
(%autoprove len-of-logic.smart-negate-formulas         (%cdr-induction x))
(%autoprove consp-of-logic.smart-negate-formulas       (%cdr-induction x))
(%autoprove logic.smart-negate-formulas-under-iff      (%cdr-induction x))
(%autoprove forcing-logic.formula-listp-of-logic.smart-negate-formulas      (%cdr-induction x))
(%autoprove forcing-logic.formula-list-atblp-of-logic.smart-negate-formulas (%cdr-induction x))

(%autoprove memberp-of-logic.pnot-in-logic.smart-negate-formulas
            (%cdr-induction x))

(%autoprove memberp-of-logic.pequal-in-logic.smart-negate-formulas
            (%cdr-induction x))

(%autoprove memberp-of-logic.~arg-in-logic.smart-negate-formulas
            (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../logic/negate-formulas")

