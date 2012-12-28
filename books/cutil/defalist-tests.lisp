; CUTIL - Centaur Basic Utilities
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "CUTIL")
(include-book "defalist")

;; Basic tests to make sure defalist seems to be working.

(local
 (encapsulate
   ()
   (defalist string-int-alistp (x)
     :key (stringp x)
     :val (integerp x))

   (defalist string-int-alist-2p (x)
     :key (stringp x)
     :val (integerp x)
     :keyp-of-nil nil)

   (defalist string-int-alist-3p (x)
     :key (stringp x)
     :val (integerp x)
     :valp-of-nil nil)

   (defalist string-integer-list-alist-p (x)
     :key (stringp x)
     :val (integer-listp x)
     :keyp-of-nil nil
     :valp-of-nil t)

   #!ACL2
   (cutil::defalist string-int-alistp (x)
     :key (stringp x)
     :val (integerp x))

   (defun my-greater-than (x n)
     (declare (xargs :guard (integerp n)))
     (and (integerp x)
          (> x n)))

   (defalist gt-alist (x arg)
     :key (my-greater-than x arg)
     :val (consp x)
     :guard (integerp arg)
     :keyp-of-nil nil
     :valp-of-nil nil)

   (defalist keyword-string-alist-p (x)
     :key (keywordp x)
     :val (stringp x)
     :true-listp t)
   ))


