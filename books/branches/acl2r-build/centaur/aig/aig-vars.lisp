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

;; BOZO should these be local?
(include-book "centaur/misc/equal-sets" :dir :system)
(include-book "centaur/misc/alist-equiv" :dir :system)

(local (in-theory (disable sets::double-containment)))

(defsection aig-vars-thms
  :parents (aig-vars)
  :short "Theorems about @(see aig-vars) from @('centaur/aig/aig-vars')."

  (defthm aig-vars-cons
    (equal (aig-vars (cons x y))
           (sets::union (aig-vars x)
                        (aig-vars y))))

  (defthm member-aig-vars-alist-vals
    (implies (not (sets::in v (aig-vars (alist-vals al))))
             (not (sets::in v (aig-vars (cdr (hons-assoc-equal x al))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm member-aig-vars-aig-and
    (implies (and (not (sets::in v (aig-vars x)))
                  (not (sets::in v (aig-vars y))))
             (not (sets::in v (aig-vars (aig-and x y)))))
    :hints(("Goal" :in-theory (enable aig-and))))

  (defthm aig-vars-aig-not
    (equal (aig-vars (aig-not x))
           (aig-vars x))
    :hints(("Goal" :in-theory (enable aig-not))))

  (defthm member-aig-vars-aig-restrict
    (implies (and (not (and (sets::in v (aig-vars x))
                            (not (member-equal v (alist-keys al)))))
                  (not (sets::in v (aig-vars (alist-vals al)))))
             (not (sets::in v (aig-vars (aig-restrict x al)))))
    :hints(("Goal" :in-theory (enable aig-restrict))))

  (defthm member-aig-vars-aig-partial-eval
    (implies (not (and (sets::in v (aig-vars x))
                       (not (member-equal v (alist-keys al)))))
             (not (sets::in v (aig-vars (aig-partial-eval x al)))))
    :hints(("Goal" :in-theory (enable aig-partial-eval)))))


