; Standard Association Lists Library
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "../lists/list-defuns")
(local (include-book "alistp"))
(local (include-book "strip-cars"))
(local (include-book "strip-cdrs"))
(local (include-book "../lists/equiv"))
(local (in-theory (enable pairlis$)))

(defsection std/alists/pairlis$
  :parents (std/alists pairlis$)
  :short "Lemmas about @(see pairlis$) available in the @(see std/alists)
library."

  :long "<p>@('(pairlis$ x y)') is a perfectly reasonable way to create a
proper, @('nil')-terminated @(see alistp) which can be used with either
\"traditional\" or \"modern\" alist functions.</p>"

  (defthm pairlis$-when-atom
    (implies (atom x)
             (equal (pairlis$ x y)
                    nil)))

  (defthm pairlis$-of-cons
    (equal (pairlis$ (cons a x) y)
           (cons (cons a (car y))
                 (pairlis$ x (cdr y)))))

  (defthm len-of-pairlis$
    (equal (len (pairlis$ x y))
           (len x)))

  (encapsulate
    ()
    ;; Some redundant things from alistp, strip-cars, strip-cdrs.
    (set-enforce-redundancy t) ;; Implicitly local

    (defthm alistp-of-pairlis$
      (alistp (pairlis$ x y)))

    (defthm strip-cars-of-pairlis$
      (equal (strip-cars (pairlis$ x y))
             (list-fix x)))

    (defthm strip-cdrs-of-pairlis$
      (equal (strip-cdrs (pairlis$ x y))
             (if (<= (len x) (len y))
                 (take (len x) y)
               (append y (replicate (- (len x) (len y)) nil))))))


  (defthm pairlis$-of-list-fix-left
    (equal (pairlis$ (list-fix x) y)
           (pairlis$ x y)))

  (defthm pairlis$-of-list-fix-right
    (equal (pairlis$ x (list-fix y))
           (pairlis$ x y)))

  (defcong list-equiv equal (pairlis$ x y) 1)
  (defcong list-equiv equal (pairlis$ x y) 2))



