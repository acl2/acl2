; Standard Typed Lists Library
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "std/util/deflist" :dir :system)

(in-theory (disable pseudo-term-listp))

(defsection std/typed-lists/pseudo-term-listp
  :parents (pseudo-termp)
  :short "Lemmas about @(see pseudo-term-listp) available in the @(see
std/typed-lists) library."

  :long "<p>Most of these are generated automatically with @(see
std::deflist).</p>"

  (std::deflist pseudo-term-listp (x)
                (pseudo-termp x)
                :true-listp t
                :elementp-of-nil t
                :already-definedp t
                ;; Set :parents to nil to avoid overwriting the built-in ACL2 documentation
                :parents nil)

  (defthm pseudo-term-listp-of-remove-equal
    ;; BOZO probably add to deflist
    (implies (pseudo-term-listp x)
             (pseudo-term-listp (remove-equal a x))))

  (defthm pseudo-term-listp-of-make-list-ac
    ;; BOZO probably silly given REPEAT as the normal form...
    (equal (pseudo-term-listp (make-list-ac n x ac))
           (and (pseudo-term-listp ac)
                (or (pseudo-termp x)
                    (zp n))))))
