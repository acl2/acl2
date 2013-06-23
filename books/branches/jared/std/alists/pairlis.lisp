; Standard Association Lists Library
; Copyright (C) 2013 Centaur Technology
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
               (append y (repeat nil (- (len x) (len y))))))))


  (defthm pairlis$-of-list-fix-left
    (equal (pairlis$ (list-fix x) y)
           (pairlis$ x y)))

  (defthm pairlis$-of-list-fix-right
    (equal (pairlis$ x (list-fix y))
           (pairlis$ x y)))

  (defcong list-equiv equal (pairlis$ x y) 1)
  (defcong list-equiv equal (pairlis$ x y) 2))



