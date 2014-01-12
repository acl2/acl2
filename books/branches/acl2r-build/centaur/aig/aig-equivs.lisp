; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
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

  (defrefinement alist-equiv aig-env-equiv
    :hints ((witness))))

