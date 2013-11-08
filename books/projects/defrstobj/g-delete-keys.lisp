; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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

(in-package "RSTOBJ")
(include-book "misc/records" :dir :system)
(local (include-book "misc/equal-by-g" :dir :system))

; g-delete-keys.lisp
;
; This just deletes a bunch of keys from a record.  It is used in the
; development of fancy-worseguy and to ensure that the MISC fields we add in
; our record stobjs do not overlap with the real stobj fields.

(defund g-delete-keys (keys x)
  (declare (xargs :guard t
                  :measure (len keys)))
  (if (atom keys)
      x
    (g-delete-keys (cdr keys)
                   (s (car keys) nil x))))

(defthm g-of-g-delete-keys
  (equal (g key (g-delete-keys keys x))
         (if (member-equal key keys)
             nil
           (g key x)))
  :hints(("Goal"
          :in-theory (enable g-delete-keys)
          :induct (g-delete-keys keys x))))

(defthm g-delete-keys-of-s-diff
  (implies (not (member-equal name keys))
           (equal (g-delete-keys keys (s name val x))
                  (s name val (g-delete-keys keys x))))
  :hints(("Goal"
          :in-theory (enable acl2::g-of-s-redux)
          :use ((:functional-instance
                 acl2::equal-by-g
                 (acl2::equal-by-g-hyp
                  (lambda () (not (member-equal name keys))))
                 (acl2::equal-by-g-lhs
                  (lambda () (s name val (g-delete-keys keys x))))
                 (acl2::equal-by-g-rhs
                  (lambda () (g-delete-keys keys (s name val x)))))))))