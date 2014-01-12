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

(in-theory (disable string-listp))

(defsection std/typed-lists/string-listp
  :parents (std/typed-lists string-listp)
  :short "Lemmas about @(see string-listp) available in the @(see
std/typed-lists) library."
  :long "<p>Most of these are generated automatically with @(see
std::deflist).</p>"

  (std::deflist string-listp (x)
    (stringp x)
    :true-listp t
    :elementp-of-nil nil
    :already-definedp t
    ;; Set :parents to nil to avoid overwriting the built-in ACL2 documentation
    :parents nil)

  (defthm true-listp-when-string-listp-rewrite
    ;; The deflist gives us a compound-recognizer, but in this case having a
    ;; rewrite rule seems worth it.
    (implies (string-listp x)
             (true-listp x))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm string-listp-of-remove-equal
    ;; BOZO probably add to deflist
    (implies (string-listp x)
             (string-listp (remove-equal a x)))))

