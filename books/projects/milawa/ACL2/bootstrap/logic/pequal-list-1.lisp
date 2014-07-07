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

(%autoadmit logic.pequal-list)

(%autoprove logic.pequal-list-when-not-consp-one
            (%restrict default logic.pequal-list (equal x 'x)))

(%autoprove logic.pequal-list-when-not-consp-two
            (%restrict default logic.pequal-list (equal x 'x)))

(%autoprove logic.pequal-list-of-cons-and-cons
            (%restrict default logic.pequal-list (equal x '(cons a x))))

(%autoprove logic.pequal-list-under-iff)

(%autoprove logic.pequal-list-of-list-fix-one
            (%cdr-cdr-induction x y))

(%autoprove logic.pequal-list-of-list-fix-two
            (%cdr-cdr-induction x y))

(%autoprove true-listp-of-logic.pequal-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.formulap-of-logic.pequal-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.formula-atblp-of-logic.pequal-list
            (%cdr-cdr-induction x y))

(%autoprove consp-of-logic.pequal-list)

(%autoprove car-of-logic.pequal-list
            ;; BOZO yuck, new car-cdr-elim code goes berserk here for some reason.
            ;; We just enable the function instead of dealing with it.
            (%restrict default logic.pequal-list (equal x 'x)))

(%autoprove cdr-of-logic.pequal-list)

(%autoprove len-of-logic.pequal-list
            (%cdr-cdr-induction x y))

(%autoprove logic.pequal-list-of-cons-and-repeat-plus-one)




(%deflist logic.all-atomicp (x)
          (equal (logic.fmtype x) 'pequal*)
          :hintsmap
          ;; These nasty hints are needed becuase the "equal" above ruins the
          ;; canonicalization we expect.
          ((logic.all-atomicp-of-remove-duplicates
            (%cdr-induction x)
            (%auto)
            (%use (%instance (%thm equal-when-memberp-of-logic.all-atomicp)
                             (a x1)
                             (x x2))))
           (logic.all-atomicp-of-subsetp-when-logic.all-atomicp
            (%cdr-induction x)
            (%auto)
            (%use (%instance (%thm equal-when-memberp-of-logic.all-atomicp)
                             (a x1)
                             (x y))))))

(%autoprove logic.fmtype-of-car-when-logic.all-atomicp
            (%enable default equal-of-car-when-logic.all-atomicp))

(%autoprove logic.fmtype-when-memberp-of-logic.all-atomicp
            (%use (%instance (%thm equal-when-memberp-of-logic.all-atomicp))))

(%autoprove logic.fmtype-when-memberp-of-logic.all-atomicp-alt)

(%autoprove forcing-logic.all-atomicp-of-logic.pequal-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.all-atomicp-of-logic.pequal-list-free)

(%autoprove logic.fmtype-of-nth-when-logic.all-atomicp)

