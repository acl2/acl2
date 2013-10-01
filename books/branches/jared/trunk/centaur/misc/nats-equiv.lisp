; Centaur Miscellaneous Books
; Copyright (C) 2013 Centaur Technology
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
(include-book "arith-equivs")
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/lists/equiv" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (in-theory (enable* arith-equiv-forwarding)))


(defund nats-equiv (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (and (atom x)
           (atom y))
      t
    (and (nat-equiv (car x) (car y))
         (nats-equiv (cdr x) (cdr y)))))

(local (in-theory (enable nats-equiv)))

(encapsulate
  ()
  (local (defthm nats-equiv-reflexive
           (nats-equiv x x)
           :hints(("Goal" :induct (len x)))))

  (local (defthm nats-equiv-symmetric
           (implies (nats-equiv x y)
                    (nats-equiv y x))))

  (local (defthm nats-equiv-transitive
           (implies (and (nats-equiv x y)
                         (nats-equiv y z))
                    (nats-equiv x x))))

  (defequiv nats-equiv))

(defrefinement list-equiv nats-equiv)

(defcong nats-equiv nat-equiv (car x) 1)
(defcong nats-equiv nats-equiv (cdr x) 1)
(defcong nats-equiv nats-equiv (cons a x) 2)

(defthm nats-equiv-of-cons
  (equal (nats-equiv (cons a x) z)
         (and (nat-equiv a (car z))
              (nats-equiv x (cdr z)))))

(local (defun my-ind (n x y)
         (if (zp n)
             (list n x y)
           (my-ind (- n 1) (cdr x) (cdr y)))))

(defcong nats-equiv nat-equiv (nth n x) 2
  :hints(("Goal"
          :in-theory (enable nth)
          :induct (my-ind n x x-equiv))))

(defcong nats-equiv nats-equiv (update-nth n v x) 3
  :hints(("Goal"
          :in-theory (enable update-nth)
          :induct (my-ind n x x-equiv))))

(defcong nat-equiv nats-equiv (update-nth n v x) 2
  :hints(("Goal"
          :in-theory (enable update-nth)
          :induct (my-ind n x x-equiv))))

(defcong nats-equiv nats-equiv (append x y) 2)
(defcong nats-equiv nats-equiv (revappend x y) 2)

(defcong nats-equiv nats-equiv (take n x) 2
  :hints(("Goal" :in-theory (enable take-redefinition))))

(defcong nats-equiv nats-equiv (nthcdr n x) 2)

(defcong nats-equiv nats-equiv (make-list-ac n val ac) 3)

(defcong nat-equiv nats-equiv (repeat x n) 1
  :hints(("Goal" :in-theory (enable repeat))))

