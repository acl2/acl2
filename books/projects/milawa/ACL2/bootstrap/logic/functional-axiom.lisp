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
(include-book "proofp")
(%interactive)

(%autoadmit logic.functional-axiom)

(%autoprove forcing-logic.formulap-of-logic.functional-axiom
            (%enable default logic.functional-axiom))

(%autoprove forcing-logic.formula-atblp-of-logic.functional-axiom
            (%enable default logic.functional-axiom))



(%autoadmit logic.functional-axiom-alt1)

(defmacro %logic.functional-axiom-alt1-induction (ti si tacc sacc)
  `(%induct (rank ,ti)
            ((or (not (consp ,ti))
                 (not (consp ,si)))
             nil)
            ((and (consp ,ti)
                  (consp ,si))
             (((,ti (cdr ,ti))
               (,si (cdr ,si))
               (,tacc (cons (car ,ti) ,tacc))
               (,sacc (cons (car ,si) ,sacc)))))))

(%autoprove logic.check-functional-axiom-of-logic.functional-axiom-alt1
            (%logic.functional-axiom-alt1-induction ti si tacc sacc)
            (%restrict default logic.functional-axiom-alt1 (equal ti 'ti))
            (%auto)
            (%restrict default logic.check-functional-axiom (equal ti 'tacc)))


(%autoadmit logic.functional-axiom-alt2)

(%autoprove logic.functional-axiom-alt1/alt2-equivalence
            ;; broken with the alternate rewriter strategy withotu assms
            ;; (%skip) reverting
            (%logic.functional-axiom-alt1-induction ti si tacc sacc)
            (%restrict default logic.functional-axiom-alt1 (equal ti 'ti))
            (%enable default logic.functional-axiom-alt2)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots
                      forcing-logic.formulap-of-logic.por
                      forcing-logic.formulap-of-logic.pequal
                      forcing-logic.formulap-of-logic.pnot
                      forcing-logic.formulap-of-logic.pequal-list
                      forcing-equal-of-logic.por-rewrite-two
                      forcing-equal-of-logic.por-rewrite
                      forcing-logic.fmtype-of-logic.disjoin-formulas
                      [outside]consp-of-logic.pequal-list ;; why ??
                      ))

(%autoprove logic.functional-axiom-alt2/main-equivalence
            (%disable default
                      forcing-logic.formulap-of-logic.pequal-list
                      logic.formula-listp-of-logic.negate-formulas
                      forcing-logic.termp-of-logic.function
                      forcing-equal-of-logic.pequal-list-rewrite
                      forcing-logic.formula-listp-of-app
                      forcing-logic.formulap-of-logic.pequal
                      equal-of-logic.pequal-list-and-logic.pequal-list
                      equal-of-logic.disjoin-formulas-and-logic.disjoin-formulas-when-same-len)
            (%enable default
                     logic.functional-axiom-alt2
                     logic.functional-axiom))

(%autoprove forcing-logic.check-functional-axiom-of-logic.functional-axiom
            (%use (%instance (%thm logic.check-functional-axiom-of-logic.functional-axiom-alt1)
                             (tacc nil)
                             (sacc nil))))

(%ensure-exactly-these-rules-are-missing "../../logic/functional-axiom")

