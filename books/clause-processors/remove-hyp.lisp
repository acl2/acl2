; Copyright (C) 2009 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")


(defun remove-first-hyp-cp (clause)
  (if (consp clause)
      (list (cdr clause))
    (list clause)))

(defevaluator remove-hyp-ev remove-hyp-ev-lst
  ((if a b c)))


(defthm remove-first-hyp-cp-correct
  (implies (and (pseudo-term-listp x)
                (alistp a)
                (remove-hyp-ev (conjoin-clauses (remove-first-hyp-cp x))
                         a))
           (remove-hyp-ev (disjoin x) a))
  :rule-classes :clause-processor)


(defun remove-hyp-cp (clause hyp)
  (list (remove-equal hyp clause)))

(defthm disjoin-of-remove-equal
  (implies (not (remove-hyp-ev (disjoin x) a))
           (not (remove-hyp-ev (disjoin (remove hyp x)) a)))
  :hints(("Goal" :in-theory (enable remove))))

(defthm remove-hyp-cp-correct
  (implies (and (pseudo-term-listp x)
                (alistp a)
                (remove-hyp-ev (conjoin-clauses (remove-hyp-cp x hyp))
                                a))
           (remove-hyp-ev (disjoin x) a))
  :rule-classes :clause-processor)

