; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
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

(in-package "STR")
(include-book "doc")
(local (include-book "arithmetic"))
(local (include-book "tools/mv-nth" :dir :system))

;; BOZO why do we have this, we have strtok instead?

;; BOZO reimplement strsplit so that it is efficient.

(defund split-list-1 (x del)
  (declare (xargs :guard t))
  (cond ((atom x)
         (mv nil nil))
        ((equal (car x) del)
         (mv nil (cdr x)))
        (t
         (mv-let (part1 part2)
                 (split-list-1 (cdr x) del)
                 (mv (cons (car x) part1) part2)))))

(defthm split-list-1-count
  (implies (consp x)
           (< (acl2-count (mv-nth 1 (split-list-1 x del)))
              (acl2-count x)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable split-list-1))))

(defthm character-listp-of-split-list-1-0
  (implies (character-listp x)
           (character-listp (mv-nth 0 (split-list-1 x del))))
  :hints(("Goal" :in-theory (enable split-list-1))))

(defthm character-listp-of-split-list-1-1
  (implies (character-listp x)
           (character-listp (mv-nth 1 (split-list-1 x del))))
  :hints(("Goal" :in-theory (enable split-list-1))))



(defund split-list* (x del)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (mv-let (first1 x)
            (split-list-1 x del)
            (if first1
                (cons first1 (split-list* x del))
              (split-list* x del)))))

(defund character-list-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (character-listp (car x))
           (character-list-listp (cdr x)))
    t))

(defthm character-list-listp-of-split-list*
  (implies (character-listp x)
           (character-list-listp (split-list* x del)))
  :hints(("Goal" :in-theory (enable split-list* character-list-listp))))



(defund coerce-list-to-strings (x)
  (declare (xargs :guard (character-list-listp x)
                  :guard-hints (("Goal" :in-theory (enable character-list-listp)))))
  (if (consp x)
      (cons (coerce (car x) 'string)
            (coerce-list-to-strings (cdr x)))
    nil))

(defthm string-listp-of-coerce-list-to-strings
  (string-listp (coerce-list-to-strings x))
  :hints(("Goal" :in-theory (enable coerce-list-to-strings))))


(defund strsplit (x del)
  (declare (xargs :guard (and (stringp x)
                              (characterp del))))
  (coerce-list-to-strings
   (split-list* (coerce x 'list) del)))

(defthm string-listp-of-strsplit
  (string-listp (strsplit x del))
  :hints(("Goal" :in-theory (enable strsplit))))




(local (include-book "make-event/assert" :dir :system))

(local
 (encapsulate
  ()
  (ACL2::assert! (equal (strsplit "foo:bar" #\:)
                        (list "foo" "bar")))

  (ACL2::assert! (equal (strsplit "foo:bar:" #\:)
                        (list "foo" "bar")))

  (ACL2::assert! (equal (strsplit ":foo:bar" #\:)
                        (list "foo" "bar")))

  (ACL2::assert! (equal (strsplit "foo::bar" #\:)
                        (list "foo" "bar")))

  (ACL2::assert! (equal (strsplit "foo::bar" #\:)
                        (list "foo" "bar")))

  (ACL2::assert! (not (strsplit "" #\:)))

  (ACL2::assert! (not (strsplit ":::::" #\:)))))


