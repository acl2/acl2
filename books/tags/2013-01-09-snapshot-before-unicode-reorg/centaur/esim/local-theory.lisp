; ESIM Symbolic Hardware Simulator
; Copyright (C) 2010-2012 Centaur Technology
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


; local-theory.lisp -- general lemmas used in the esim proofs, this book should
; only be locally included!
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "unicode/rev" :dir :system)
(include-book "data-structures/list-defthms" :dir :system)
(include-book "data-structures/no-duplicates" :dir :system)
(include-book "centaur/misc/fast-alists" :dir :system)
(include-book "centaur/misc/equal-sets" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))



(defthm remove-duplicates-equal-of-append
  (equal (remove-duplicates-equal (append a b))
         (append (set-difference-equal (remove-duplicates-equal a) b)
                 (remove-duplicates-equal b)))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-append
  (equal (set-difference-equal (append a b) c)
         (append (set-difference-equal a c)
                 (set-difference-equal b c)))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-remove-inside-set-difference
  (implies (member-equal k keys)
           (equal (set-difference-equal
                   (set-difference-equal a (list k))
                   keys)
                  (set-difference-equal a keys)))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm hons-remove-duplicates1-is-remove-duplicates
  (equal (hons-remove-duplicates1 lst tab)
         (rev (set-difference-equal
               (remove-duplicates-equal (rev lst))
               (alist-keys tab))))
  :hints(("Goal" :in-theory (enable rev set-difference-equal))))

(defthm set-difference-equal-nil
  (equal (set-difference-equal x nil)
         (append x nil))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm hons-remove-duplicates-is-remove-duplicates
  (equal (hons-remove-duplicates lst)
         (rev (remove-duplicates-equal (rev lst)))))

(defthm hons-dups-p1-when-table-member
  (implies (and (member-equal x lst)
                (hons-assoc-equal x tab))
           (hons-dups-p1 lst tab)))

(defthm hons-dups-p1-is-no-duplicatesp
  (iff (hons-dups-p1 lst tab)
       (or (not (no-duplicatesp-equal lst))
           (intersectp-equal lst (alist-keys tab)))))

(defthm hons-dups-p-is-no-duplicatesp
  (iff (hons-dups-p lst)
       (not (no-duplicatesp-equal lst))))

(defthm member-equal-rev
  (iff (member-equal k (rev x))
       (member-equal k x))
  :hints(("Goal" :in-theory (enable rev))))

(defthm set-equivp-rev
  (set-equivp (rev x) x)
  :hints ((witness)))

(defthm alist-keys-append
  (equal (alist-keys (append a b))
         (append (alist-keys a) (alist-keys b))))

(defthm true-listp-append-iff
  (iff (true-listp (append a b))
       (true-listp b)))

