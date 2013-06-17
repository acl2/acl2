; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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

(in-package "XDOC")
(program)

; This is the same mergesort from the osets library.  We only copy it here so
; that we can use it without depending on osets.  I modify it somewhat to
; avoid set operations like "empty" and "tail", in lieu of ordinary atom and
; cdr, etc.

(defun << (a b)
  (and (lexorder a b)
       (not (equal a b))))

(defun fast-union (x y acc)
  (cond
   ((atom x) (revappend acc y))
   ((atom y) (revappend acc x))
   ((equal (car x) (car y))
    (fast-union (cdr x) (cdr y) (cons (car x) acc)))
   ((<< (car x) (car y))
    (fast-union (cdr x) y (cons (car x) acc)))
   (t
    (fast-union x (cdr y) (cons (car y) acc)))))

(defund halve-list-aux (mid x acc)
  (if (or (atom x)
          (atom (cdr x)))
      (mv acc mid)
    (halve-list-aux (cdr mid)
                    (cdr (cdr x))
                    (cons (car mid) acc))))

(defund halve-list (x)
  (halve-list-aux x x nil))

(defun mergesort (x)
  (cond ((atom x) nil)
        ((atom (cdr x))
         (list (car x)))
        (t (mv-let (part1 part2)
                   (halve-list x)
                   (fast-union (mergesort part1)
                               (mergesort part2)
                               nil)))))
