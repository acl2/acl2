; Resize List Lemmas
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "list-defuns")
(local (include-book "len"))
(local (include-book "list-fix"))
(local (include-book "repeat"))
(local (include-book "nth"))
(local (include-book "arithmetic/top" :dir :system))

(defthm resize-list-when-zp
  (implies (zp n)
           (equal (resize-list lst n default-value)
                  nil)))

(defthm resize-list-of-nfix
  (equal (resize-list lst (nfix n) default-value)
         (resize-list lst n default-value)))

(defthm resize-list-when-atom
  (implies (atom lst)
           (equal (resize-list lst n default-value)
                  (repeat default-value n)))
  :hints(("Goal" :in-theory (enable repeat))))

(local (defun my-induct (n m lst)
         (if (zp n)
             (list lst)
           (if (zp m)
               nil
             (my-induct (- n 1) (- m 1)
                        (if (atom lst)
                            lst
                          (cdr lst)))))))

(defthm nth-of-resize-list
  (equal (nth n (resize-list lst m default-value))
         (let ((n (nfix n))
               (m (nfix m)))
           (and (< n m)
                (if (< n (len lst))
                    (nth n lst)
                  default-value))))
  :hints(("Goal"
          :expand (resize-list lst m default-value)
          :induct (my-induct n m lst))))

(defthm len-of-resize-list
  (equal (len (resize-list lst n default))
         (nfix n)))

(defthm resize-list-of-len-free
  (implies (equal (nfix n) (len lst))
           (equal (resize-list lst n default-value)
                  (list-fix lst))))

(defthm equal-of-resize-list-and-self
  (equal (equal (resize-list lst n default-value) lst)
         (and (true-listp lst)
              (equal (len lst) (nfix n)))))

