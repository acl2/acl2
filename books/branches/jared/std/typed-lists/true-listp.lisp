; Built-In Typed Lists
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

(defthm true-listp-when-atom
  (implies (atom x)
           (equal (true-listp x)
                  (not x))))

(defthm true-listp-of-cons
  (equal (true-listp (cons a x))
         (true-listp x)))

(defthm consp-under-iff-when-true-listp
  (implies (true-listp x)
           (iff (consp x)
                x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

