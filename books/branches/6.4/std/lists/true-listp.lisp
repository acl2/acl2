; True-Listp Lemmas
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "std/lists/list-defuns" :dir :system)
(in-theory (disable true-listp))

(defsection std/lists/true-listp
  :parents (std/lists true-listp)
  :short "Lemmas about @(see true-listp) available in the @(see std/lists)
library."

  :long "<p>Note: the list of lemmas below is quite incomplete.  For instance,
the @(see true-listp) rule about @(see append) will be found in the
documentation for @(see std/lists/append), instead of here.</p>"

  (local (in-theory (enable true-listp)))

  (defthm true-listp-when-atom
    (implies (atom x)
             (equal (true-listp x)
                    (not x))))

  (defthm true-listp-of-cons
    (equal (true-listp (cons a x))
           (true-listp x)))

  (defthm consp-under-iff-when-true-listp
    ;; BOZO even with the backchain limit, this rule can get too expensive.
    (implies (true-listp x)
             (iff (consp x)
                  x))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


