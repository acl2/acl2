
; no-duplicates.lisp: Reasoning about no-duplicatesp-equal and
; intersectp-equal.  Name-compatible with list-theory.lisp and set-theory.lisp.

; Copyright (C) 2010 Centaur Technology
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

(defthm assoc-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm member-equal-append
  (iff (member-equal x (append a b))
       (or (member-equal x a)
           (member-equal x b))))

(defthm no-duplicatesp-equal-append-iff
  (iff (no-duplicatesp-equal (append a b))
       (and (no-duplicatesp-equal a)
            (no-duplicatesp-equal b)
            (not (intersectp-equal a b)))))

(defthm intersectp-equal-append1
  (equal (intersectp-equal (append a b) c)
         (or (intersectp-equal a c)
             (intersectp-equal b c))))


(defthm intersectp-equal-cons-second
  (iff (intersectp-equal a (cons c b))
       (or (member-equal c a)
           (intersectp-equal a b))))

(defthm intersectp-equal-non-cons-1
  (implies (not (consp a))
           (not (intersectp-equal a b))))

(defthm intersectp-equal-non-cons
  (implies (not (consp b))
           (not (intersectp-equal a b))))

(defthm intersectp-equal-append2
  (equal (intersectp-equal c (append a b))
         (or (intersectp-equal c a)
             (intersectp-equal c b))))


(defthm intersectp-equal-commute
  (iff (intersectp-equal a b)
       (intersectp-equal b a)))




(defthm member-is-member-equal
  (equal (member x y) (member-equal x y)))

(defthm no-duplicatesp-is-no-duplicatesp-equal
  (equal (no-duplicatesp x)
         (no-duplicatesp-equal x)))

(defthm no-duplicatesp-equal-non-cons
  (implies (not (consp x))
           (no-duplicatesp-equal x)))


