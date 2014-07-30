; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "faig-base")
(include-book "aig-equivs")



(defsection faig-equiv
  (def-universal-equiv faig-equiv
    :qvars env
    :equiv-terms ((equal (faig-eval x env)))
    :defquant t
    :witness-dcls ((declare (xargs :guard t :verify-guards nil)))
    :parents (faig)
    :short "We say the FAIGs @('X') and @('Y') are equivalent when they always
evaluate to the same value, per @(see faig-eval).")

  (verify-guards faig-equiv)

  (defcong faig-equiv equal (faig-eval x env) 1
    :hints(("Goal" :in-theory (e/d (faig-equiv-necc)
                                   (faig-eval)))))

  (defthm faig-equiv-of-faig-fix
    (faig-equiv (faig-fix x) x)
    :hints(("Goal" :in-theory (enable faig-equiv)))))

(defsection faig-alist-equiv
  (def-universal-equiv faig-alist-equiv
    :qvars k
    :equiv-terms ((iff (hons-assoc-equal k x))
                  (faig-equiv (cdr (hons-assoc-equal k x))))
    :defquant t
    :witness-dcls ((declare (xargs :guard t :verify-guards nil)))
    :parents (faig)
    :short "We say the FAIG Alists @('X') and @('Y') are equivalent when they
bind the same keys to equivalent FAIGs, in the sense of @(see faig-equiv).")

  (verify-guards faig-alist-equiv)

  (defrefinement alist-equiv faig-alist-equiv
    :hints ((witness))))


