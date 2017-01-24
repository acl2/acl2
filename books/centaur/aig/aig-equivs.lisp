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
(include-book "aig-base")
(include-book "centaur/misc/witness-cp" :dir :system)
(include-book "centaur/misc/universal-equiv" :dir :system)
(include-book "centaur/misc/fast-alists" :dir :system)
(set-verify-guards-eagerness 0)


(def-universal-equiv aig-equiv
  :qvars env
  :equiv-terms ((equal (aig-eval x env)))
  :defquant t
  :witness-dcls ((declare (xargs :guard t)))
  :parents (aig-semantics)
  :short "We say the AIGs @('X') and @('Y') are equivalent when they always
evaluate to the same value, per @(see aig-eval).")

(verify-guards aig-equiv)


(def-universal-equiv aig-alist-equiv
  :qvars k
  :equiv-terms ((iff (hons-assoc-equal k x))
                (aig-equiv (cdr (hons-assoc-equal k x))))
  :defquant t
  :witness-dcls ((declare (xargs :guard t)))
  :parents (aig-semantics)
  :short "We say the AIG Alists @('X') and @('Y') are equivalent when they bind
the same keys to equivalent AIGs, in the sense of @(see aig-equiv).")

(verify-guards aig-alist-equiv)

(defsection aig-alist-equiv-thms
  :extension aig-alist-equiv

  (defrefinement alist-equiv aig-alist-equiv
    :hints ((witness))))



(def-universal-equiv aig-env-equiv
  :qvars key
  :equiv-terms ((iff (aig-env-lookup key x)))
  :defquant t
  :witness-dcls ((declare (xargs :guard t)))
  :parents (aig-semantics)
  :short "We say the environments @('X') and @('Y') are equivalent when they
give equivalent values to variables looked up with @(see aig-env-lookup).")


(verify-guards aig-env-equiv)

(defsection aig-env-equiv-thms
  :extension aig-env-equiv

  (defcong aig-env-equiv equal (aig-env-lookup key x) 2
    :hints (("goal" :cases ((aig-env-lookup key x))
             :use ((:instance aig-env-equiv-necc (y x-equiv))))))

  (defrefinement alist-equiv aig-env-equiv
    :hints ((witness))))

