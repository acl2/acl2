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

(fty::defmap pseudo-term-subst :key-type pseudo-var :val-type pseudo-term :true-listp t)

(deflist pseudo-var-list :elt-type pseudo-var :true-listp t)

(defthm pseudo-term-subst-p-of-pair-vars
  (implies (pseudo-term-listp vals)
           (pseudo-term-subst-p (pair-vars vars vals)))
  :hints(("Goal" :in-theory (enable pair-vars))))

(defthm pseudo-term-subst-p-of-pairlis$
  (implies (and (pseudo-var-list-p vars)
                (pseudo-term-listp terms))
           (pseudo-term-subst-p (pairlis$ vars terms))))


(defthm pseudo-term-list-p-when-pseudo-var-list-p
  (implies (pseudo-var-list-p x)
           (pseudo-term-listp x))
  :hints(("Goal" :in-theory (enable pseudo-var-list-p))))
           

(defthm pseudo-termp-of-lookup-in-pseudo-term-subst
         (implies (pseudo-term-subst-p x)
                  (pseudo-termp (cdr (assoc k x)))))

(defthm assoc-of-pseudo-term-subst-fix
  (equal (assoc k (pseudo-term-subst-fix x))
         (and (pseudo-var-p k)
              (let ((look (assoc k x)))
                (and look
                     (cons k (pseudo-term-fix (cdr look)))))))
  :hints(("Goal" :in-theory (enable pseudo-term-subst-fix))))


(define base-ev-alist ((x pseudo-term-subst-p) a)
  :verify-guards nil
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (pseudo-var-p (caar x))))
        (cons (cons (caar x) (base-ev (cdar x) a))
              (base-ev-alist (cdr x) a))
      (base-ev-alist (cdr x) a)))
  ///

  (defthm lookup-in-base-ev-alist-split
    (equal (assoc k (base-ev-alist x a))
           (and (pseudo-var-p k)
                (let ((look (assoc k x)))
                  (and look
                       (cons k (base-ev (cdr look) a)))))))

  (local (in-theory (enable pseudo-term-subst-fix))))  
