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
(include-book "cutil/deflist" :dir :system)

(cutil::deflist character-listp (x)
  (characterp x)
  :true-listp t
  :elementp-of-nil nil
  :already-definedp t)

(defthm true-listp-when-character-listp-rewrite
  ;; The deflist gives us a compound-recognizer, but in this case having a
  ;; rewrite rule seems worth it.
  (implies (character-listp x)
           (true-listp x))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm character-listp-of-remove-equal
  ;; BOZO probably add to deflist
  (implies (character-listp x)
           (character-listp (remove-equal a x))))

(defthm character-listp-of-make-list-ac
  (equal (character-listp (make-list-ac n x ac))
         (and (character-listp ac)
              (or (characterp x)
                  (zp n)))))

(defthm eqlable-listp-when-character-listp
  (implies (character-listp x)
           (eqlable-listp x)))

(defthm character-listp-of-rev
  ;; BOZO consider adding to deflist
  (equal (character-listp (rev x))
         (character-listp (list-fix x)))
  :hints(("Goal" :induct (len x))))

