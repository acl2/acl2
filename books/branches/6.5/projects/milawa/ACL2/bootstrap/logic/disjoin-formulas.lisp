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

(%autoadmit logic.disjoin-formulas)

(defmacro %logic.disjoin-formulas-induction (x)
  `(%induct (rank ,x)
            ((or (not (consp ,x))
                 (not (consp (cdr ,x))))
             nil)
            ((and (consp ,x)
                  (consp (cdr ,x)))
             (((,x (cdr ,x)))))))

(defsection logic.disjoin-formulas-when-not-consp
  ;; BOZO add to acl2?  This lets us avoid many expand hints below
  (%prove (%rule logic.disjoin-formulas-when-not-consp
                 :hyps (list (%hyp (not (consp x))))
                 :lhs (logic.disjoin-formulas x)
                 :rhs nil))
  (local (%restrict default logic.disjoin-formulas (equal x 'x)))
  (%auto)
  (%qed)
  (%enable default logic.disjoin-formulas-when-not-consp))

(%autoprove logic.disjoin-formulas-when-singleton-list
            (%restrict default logic.disjoin-formulas (equal x 'x)))

(%autoprove logic.disjoin-formulas-of-cons-onto-consp
            (%restrict default logic.disjoin-formulas (equal x '(cons a x))))

(%autoprove logic.disjoin-formulas-of-list-fix
            (%logic.disjoin-formulas-induction x)
            (%disable default
                      forcing-logic.formulap-of-logic.por
                      aggressive-equal-of-logic.pors
                      forcing-equal-of-logic.por-rewrite
                      forcing-equal-of-logic.por-rewrite-two))

(%autoprove forcing-logic.formulap-of-logic.disjoin-formulas
            (%logic.disjoin-formulas-induction x)
            (%enable default logic.formulap-of-logic.por-expensive))

(%autoprove logic.formula-atblp-of-logic.por-expensive
            (%restrict default logic.formula-atblp (equal x '(logic.por x y))))

(%autoprove forcing-logic.formula-atblp-of-logic.disjoin-formulas
            (%logic.disjoin-formulas-induction x)
            (%enable default logic.formula-atblp-of-logic.por-expensive))

(%autoprove logic.formula-listp-when-logic.formulap-of-logic.disjoin-formulas-free)

(%autoprove logic.formula-list-atblp-when-logic.formula-atblp-of-logic.disjoin-formulas-free)

(%autoprove forcing-logic.fmtype-of-logic.disjoin-formulas
            (%logic.disjoin-formulas-induction x))

(%autoprove forcing-logic.vlhs-of-logic.disjoin-formulas)

(%autoprove forcing-logic.vrhs-of-logic.disjoin-formulas)

(%autoprove forcing-logic.fmtype-of-logic.disjoin-formulas-free)

(%autoprove forcing-logic.vlhs-of-logic.disjoin-formulas-free)

(%autoprove forcing-logic.vrhs-of-logic.disjoin-formulas-free)

(%autoprove forcing-logic.disjoin-formulas-of-two-element-list)

(%autoprove equal-of-logic.disjoin-formulas-and-logic.disjoin-formulas-when-same-len
            (%induct (rank x)
                     ((or (not (consp x))
                          (not (consp y))
                          (not (consp (cdr x)))
                          (not (consp (cdr y))))
                      nil)
                     ((and (consp x)
                           (consp (cdr x))
                           (consp y)
                           (consp (cdr y)))
                      (((x (cdr x))
                        (y (cdr y))))))
            ;; these cause loops after some rewriter changes.  taking them out.
            (%disable default
                      forcing-logic.fmtype-of-logic.disjoin-formulas-free
                      consp-of-cdr-with-len-free))

(encapsulate
 ()
 (local (%disable default EQUAL-OF-LOGIC.DISJOIN-FORMULAS-AND-LOGIC.DISJOIN-FORMULAS-WHEN-SAME-LEN))
 (%defprojection :list (logic.disjoin-each-formula-list x)
                 :element (logic.disjoin-formulas x)
                 :nil-preservingp t))

(%autoprove forcing-logic.formula-listp-of-logic.disjoin-each-formula-list
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-logic.disjoin-each-formula-list
            (%cdr-induction x))

(%autoprove logic.disjoin-each-formula-list-of-listify-each
            (%cdr-induction x))

(%ensure-exactly-these-rules-are-missing "../../logic/disjoin-formulas")

