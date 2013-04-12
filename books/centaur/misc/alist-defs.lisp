; Centaur Miscellaneous Books
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

;; for alist-keys, alist-vals:
(include-book "misc/hons-help" :dir :system)
(include-book "hons-extra")
(include-book "std/alists/alist-defuns" :dir :system)

(defund hons-acons-each (keys val al)
  (declare (xargs :guard t))
  (if (atom keys)
      al
    (hons-acons (car keys) val
                (hons-acons-each (Cdr keys) val al))))

;; This is just hshrink-alist with a NIL accumulator.
(defund al-shrink (al)
  (declare (xargs :guard t))
  (hons-shrink-alist al nil))


