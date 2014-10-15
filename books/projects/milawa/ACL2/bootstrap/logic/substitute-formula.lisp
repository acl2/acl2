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
(include-book "substitute-formula-2-each")
(include-book "substitute-formula-2-list")
(include-book "disjoin-formulas")
(include-book "negate-formulas")
(include-book "pequal-list")
(include-book "por-list")
(%interactive)

(%autoprove logic.substitute-formula-of-logic.disjoin-formulas
            (%cdr-induction x)
            (%restrict default logic.disjoin-formulas (equal x 'x))
            (%disable default
                      ;; These rules cause some problems with forcing
                      forcing-logic.fmtype-of-logic.substitute-formula
                      forcing-logic.fmtype-of-logic.disjoin-formulas
                      forcing-logic.formula-listp-of-logic.substitute-formula-list
                      forcing-logic.vlhs-of-logic.disjoin-formulas
                      forcing-logic.formulap-of-logic.disjoin-formulas
                      forcing-logic.formulap-of-logic.substitute-formula
                      forcing-logic.formulap-of-logic.por
                      forcing-equal-of-logic.por-rewrite-two
                      equal-of-logic.disjoin-formulas-and-logic.disjoin-formulas-when-same-len
                      aggressive-equal-of-logic.pors))

(%autoprove logic.substitute-formula-list-of-logic.negate-formulas
            (%cdr-induction x))

(%autoprove logic.substitute-formula-list-of-logic.pequal-list
            (%cdr-cdr-induction x y)
            (%disable default
                      forcing-equal-of-logic.pequal-list-rewrite
                      forcing-equal-of-logic.pequal-list-rewrite-alt))

(%autoprove logic.substitute-formula-list-of-logic.por-list
            (%cdr-cdr-induction x y)
            (%disable default
                      forcing-equal-of-logic.por-list-rewrite
                      forcing-equal-of-logic.por-list-rewrite-alt))



(%defprojection :list (logic.substitute-formula-list-list x sigma)
                :element (logic.substitute-formula-list x sigma)
                ;; BOZO this is nil-preserving, but the ACL2 model needs to be updated with that fact.
                ;; :nil-preservingp t
                )

(%autoprove forcing-logic.formula-list-listp-of-logic.substitute-formula-list-list
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-list-atblp-of-logic.substitute-formula-list-list
            (%cdr-induction x))

(%autoprove logic.substitute-formula-list-of-logic.disjoin-each-formula-list
            (%cdr-induction x))

(%autoprove logic.substitute-formula-list-of-logic.disjoin-each-formula-list-free)

(%ensure-exactly-these-rules-are-missing "../../logic/substitute-formula")

