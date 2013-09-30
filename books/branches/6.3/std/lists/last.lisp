; Last Lemmas
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
(include-book "xdoc/top" :dir :system)
(include-book "list-defuns")
(local (include-book "list-fix"))
(local (include-book "append"))
(local (include-book "rev"))

(defsection std/lists/last
  :parents (std/lists last)
  :short "Lemmas about @(see last) available in the @(see std/lists) library."

  (defthm last-when-atom
    (implies (atom x)
             (equal (last x)
                    x)))

  (defthm last-when-atom-of-cdr
    (implies (atom (cdr x))
             (equal (last x)
                    x)))

  (defthm last-of-cons
    (equal (last (cons a x))
           (if (consp x)
               (last x)
             (cons a x))))

  (defthm consp-of-last
    (equal (consp (last l))
           (consp l)))

  (defthm true-listp-of-last
    (equal (true-listp (last l))
           (true-listp l)))

  (defthm last-of-list-fix
    (equal (last (list-fix x))
           (list-fix (last x))))

  (defthm len-of-last 
    (equal (len (last l))
           (if (consp l)
               1
             0)))

  (defthm upper-bound-of-len-of-last
    (< (len (last x)) 2)
    :rule-classes :linear)

  (defthm member-of-car-of-last
    (iff (member (car (last x)) x)
         (if (consp x)
             t
           nil)))
  
  (defsection subsetp-of-last

    (local (defthm l0
             (implies (subsetp-equal a x)
                      (subsetp-equal a (cons b x)))))

    (defthm subsetp-of-last
      ;; possibly good for forward chaining?
      (subsetp (last x) x)))

  (defthm last-of-append
    (equal (last (append x y))
           (if (consp y)
               (last y)
             (append (last x) y))))

  (defthm last-of-rev
    (equal (last (rev x))
           (if (consp x)
               (list (car x))
             nil)))

  (defthm last-of-revappend
    (equal (last (revappend x y))
           (cond ((consp y)
                  (last y))
                 ((consp x)
                  (cons (car x) y))
                 (t
                  y)))))

