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
;
; Additional copyright notice:
;
; This file is adapted from Milawa, which is also released under the GPL.

(in-package "CUTIL")
(include-book "deflist")

(local
 (encapsulate
   ()

   (deflist int-listp (x)
     (integerp x))

   (deflist int-listp (x)
     ;; Make sure redundant version works
     (integerp x))

   #!ACL2
   (cutil::deflist int-listp (x)
     ;; Make sure other-package version works
     (integerp x))

   (deflist int-listp-program (x)
     (integerp x)
     :mode :program
     :parents (foo))

   (deflist int-listp-doc (x)
     (integerp x)
     :parents (foo))

   (deflist intfree-listp (x)
     (integerp x)
     :negatedp t)

   (deflist true-list-listp (x)
     (true-listp x)
     :elementp-of-nil t)

   (deflist truelistfree-listp (x)
     (true-listp x)
     :negatedp t
     :elementp-of-nil t)

   (deflist rat-listp (x)
     (rationalp x)
     :elementp-of-nil nil)

   (deflist ratfree-listp (x)
     (rationalp x)
     :elementp-of-nil nil
     :negatedp t)

   (deflist all-greater-than-p (min x)
     (> min x)
     :guard (and (integerp min)
                 (integer-listp x)))))
