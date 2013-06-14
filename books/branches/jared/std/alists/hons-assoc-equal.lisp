; Standard Association Lists Library
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "../lists/list-defuns")
(local (include-book "../lists/list-fix"))
(local (in-theory (enable hons-assoc-equal)))

(defthm hons-assoc-equal-when-atom
  (implies (atom alist)
           (equal (hons-assoc-equal a alist)
                  nil)))

(defthm hons-assoc-equal-of-cons
  (equal (hons-assoc-equal key (cons entry map))
         (if (and (consp entry)
                  (equal key (car entry)))
             entry
           (hons-assoc-equal key map))))

(encapsulate
  ()
  (local (defthmd l0
           (equal (hons-assoc-equal key (list-fix alist))
                  (hons-assoc-equal key alist))))

  (defcong list-equiv equal (hons-assoc-equal key alist) 2
    :hints(("Goal"
            :in-theory (enable list-equiv)
            :use ((:instance l0 (alist alist))
                  (:instance l0 (alist alist-equiv)))))))

(defthm hons-assoc-equal-of-hons-acons
  (equal (hons-assoc-equal key (hons-acons key2 val map))
         (if (equal key key2)
             (cons key val)
           (hons-assoc-equal key map))))

(defthm consp-of-hons-assoc-equal
  (equal (consp (hons-assoc-equal x alist))
         (if (hons-assoc-equal x alist)
             t
           nil)))

(defthm car-hons-assoc-equal
  (implies (hons-assoc-equal k a)
           (equal (car (hons-assoc-equal k a))
                  k)))

(defthm car-hons-assoc-equal-split
  (equal (car (hons-assoc-equal key alist))
         (if (hons-assoc-equal key alist)
             key
           nil)))

(defthm hons-assoc-equal-append
  (equal (hons-assoc-equal x (append a b))
         (or (hons-assoc-equal x a)
             (hons-assoc-equal x b))))

(defthm hons-assoc-equal-of-hons-shrink-alist
  (equal (hons-assoc-equal a (hons-shrink-alist x y))
         (or (hons-assoc-equal a y)
             (hons-assoc-equal a x))))

(defthm cons-key-cdr-hons-assoc-equal
  (implies (hons-assoc-equal k a)
           (equal (cons k (cdr (hons-assoc-equal k a)))
                  (hons-assoc-equal k a))))

