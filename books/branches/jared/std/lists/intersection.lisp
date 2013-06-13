; Intersection$ Lemmas
; Copyright (C) 2013 Kookamara LLC
;
; Contact:
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759
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
; Original authors: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "sets")

(in-theory (disable intersection$))
(local (in-theory (enable intersection$)))

(defthm intersection$-when-atom-left
  (implies (atom x)
           (equal (intersection$ x y)
                  nil)))

(defthm intersection$-when-atom-right
  (implies (atom y)
           (equal (intersection$ x y)
                  nil)))

(defthm intersection$-of-cons-left
  (equal (intersection$ (cons a x) y)
         (if (member a y)
             (cons a (intersection$ x y))
           (intersection$ x y))))

(defthm intersection$-of-cons-right-under-set-equiv
  (set-equiv (intersection$ x (cons a y))
             (if (member a x)
                 (cons a (intersection$ x y))
               (intersection$ x y)))
  :hints(("Goal" :in-theory (enable set-equiv))))

(defthm len-of-intersection$-upper-bound
  ;; There is no analogous rule for -right, because, e.g., X could have multiple
  ;; copies of some member in Y, and if so we end up reproducing them.  Consider
  ;; for instance (intersection$ '(a a a) '(a)) ==> '(a a a).
  (<= (len (intersection$ x y))
      (len x))
  :rule-classes ((:rewrite) (:linear)))

(defthm consp-of-intersection$
  (equal (consp (intersection$ x y))
         (intersectp x y))
  :hints(("Goal" :in-theory (enable intersectp))))

(defthm intersection$-under-iff
  (iff (intersection$ x y)
       (intersectp x y))
  :hints(("Goal" :in-theory (enable intersectp))))

