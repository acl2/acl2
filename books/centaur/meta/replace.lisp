; Centaur Meta-reasoning Library
; Copyright (C) 2019 Centaur Technology
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

(in-package "CMR")

(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)

(fty::defmap pseudo-term-mapping :key-type pseudo-term :val-type pseudo-term :true-listp t)

(define base-ev-pseudo-term-mapping-correct-p ((map pseudo-term-mapping-p) (env alistp))
  (b* (((when (atom map)) t)
       ((unless (mbt (and (consp (car map))
                          (pseudo-termp (caar map)))))
        (base-ev-pseudo-term-mapping-correct-p (cdr map) env)))
    (and (equal (base-ev (caar map) env)
                (base-ev (cdar map) env))
         (base-ev-pseudo-term-mapping-correct-p (cdr map) env)))
  ///
  (defthm base-ev-pseudo-term-mapping-correct-p-implies
    (implies (and (base-ev-pseudo-term-mapping-correct-p map env)
                  (pseudo-termp x)
                  (hons-assoc-equal x map))
             (equal (base-ev (cdr (hons-assoc-equal x map)) env)
                    (base-ev x env)))))
  

(defines term-replace
  (define term-replace ((x pseudo-termp)
                        (map pseudo-term-mapping-p))
    :returns (new-x pseudo-termp)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (b* ((look (hons-assoc-equal (pseudo-term-fix x) (pseudo-term-mapping-fix map)))
         ((when look) (cdr look)))
      (pseudo-term-case x
        :call (pseudo-term-call x.fn (termlist-replace x.args map))
        :otherwise (pseudo-term-fix x))))
  (define termlist-replace ((x pseudo-term-listp)
                            (map pseudo-term-mapping-p))
    :returns (new-x pseudo-term-listp)
    :measure (pseudo-term-list-count x)
    (if (atom x)
        nil
      (cons (term-replace (car x) map)
            (termlist-replace (cdr x) map))))
  ///
  (defret termlist-replace-len
    (equal (len new-x) (len x))
    :fn termlist-replace)

  (local (Defthm take-of-len
           (implies (and (equal (nfix n) (len x))
                         (true-listp x))
                    (equal (take n x) x))))

  (verify-guards term-replace)

  (defret-mutual term-replace-correct
    (defret term-replace-correct
      (implies (base-ev-pseudo-term-mapping-correct-p map env)
               (equal (base-ev new-x env)
                      (base-ev x env)))
      :hints ('(:expand <call>
                :in-theory (enable acl2::base-ev-of-fncall-args)))
      :fn term-replace)
    (defret termlist-replace-correct
      (implies (base-ev-pseudo-term-mapping-correct-p map env)
               (equal (base-ev-list new-x env)
                      (base-ev-list x env)))
      :hints ('(:expand <call>))
      :fn termlist-replace)))
