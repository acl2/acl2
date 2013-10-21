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
(include-book "aig-equivs")
(include-book "faig-base")
(set-verify-guards-eagerness 0)


(defsection faig-equiv
  :parents (faig)
  :short "We say the FAIGs @('X') and @('Y') are equivalent when they always
evaluate to the same value, per @(see faig-eval)."

  (def-universal-equiv faig-equiv
    :qvars env
    :equiv-terms ((equal (faig-eval x env)))
    :defquant t
    :witness-dcls ((declare (xargs :guard t))))

  (verify-guards faig-equiv))


(defsection faig-alist-equiv
  :parents (faig)
  :short "We say the FAIG Alists @('X') and @('Y') are equivalent when they
bind the same keys to equivalent FAIGs, in the sense of @(see faig-equiv)."

  (def-universal-equiv faig-alist-equiv
    :qvars k
    :equiv-terms ((iff (hons-assoc-equal k x))
                  (faig-equiv (cdr (hons-assoc-equal k x))))
    :defquant t
    :witness-dcls ((declare (xargs :guard t))))

  (verify-guards faig-alist-equiv)

  (defrefinement alist-equiv faig-alist-equiv
    :hints ((witness))))
