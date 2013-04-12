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
(include-book "alist-keys")
(include-book "alist-vals")
(local (include-book "../lists/list-fix"))

(defund hons-rassoc-equal (val map)
  (declare (xargs :guard t))
  (cond ((atom map)
         nil)
        ((and (consp (car map))
              (equal val (cdar map)))
         (car map))
        (t
         (hons-rassoc-equal val (cdr map)))))

(local (in-theory (enable hons-rassoc-equal)))

(defthm hons-rassoc-equal-when-atom
  (implies (atom map)
           (equal (hons-rassoc-equal val map)
                  nil)))

(defthm hons-rassoc-equal-of-hons-acons
  (equal (hons-rassoc-equal a (cons (cons key b) map))
         (if (equal a b)
             (cons key b)
           (hons-rassoc-equal a map))))

(defthm hons-rassoc-equal-type
  (or (not (hons-rassoc-equal val map))
      (consp (hons-rassoc-equal val map)))
  :rule-classes :type-prescription)

(encapsulate
  ()
  (local (defthmd l0
           (equal (hons-rassoc-equal key (list-fix alist))
                  (hons-rassoc-equal key alist))))

  (defcong list-equiv equal (hons-rassoc-equal key alist) 2
    :hints(("Goal"
            :in-theory (enable list-equiv)
            :use ((:instance l0 (alist alist))
                  (:instance l0 (alist alist-equiv)))))))

(defthm consp-of-hons-rassoc-equal
  (equal (consp (hons-rassoc-equal val map))
         (if (hons-rassoc-equal val map)
             t
           nil)))

(defthm cdr-of-hons-rassoc-equal
  (equal (cdr (hons-rassoc-equal val map))
         (if (hons-rassoc-equal val map)
             val
           nil)))

(defthm member-equal-of-alist-vals-under-iff
  (iff (member-equal val (alist-vals map))
       (hons-rassoc-equal val map))
  :hints(("Goal" :in-theory (enable hons-rassoc-equal
                                    alist-vals))))

(defthm hons-assoc-equal-of-car-when-hons-rassoc-equal
  (implies (hons-rassoc-equal val map)
           (hons-assoc-equal (car (hons-rassoc-equal val map)) map))
  :hints(("Goal" :in-theory (enable hons-assoc-equal
                                    hons-rassoc-equal))))

(defthm hons-assoc-equal-of-car-when-hons-rassoc-equal-and-no-duplicates
  (implies (and (no-duplicatesp-equal (alist-keys map))
                (hons-rassoc-equal val map))
           (equal (hons-assoc-equal (car (hons-rassoc-equal val map)) map)
                  (hons-rassoc-equal val map)))
  :hints(("Goal" :in-theory (enable hons-assoc-equal
                                    hons-rassoc-equal))))

(defthm member-equal-of-car-when-hons-rassoc-equal
  (implies (hons-rassoc-equal val map)
           (member-equal (car (hons-rassoc-equal val map))
                         (alist-keys map))))

(defthm hons-rassoc-equal-of-cdr-when-hons-assoc-equal
  (implies (hons-assoc-equal key map)
           (hons-rassoc-equal (cdr (hons-assoc-equal key map)) map))
  :hints(("Goal" :in-theory (enable hons-assoc-equal
                                    hons-rassoc-equal))))

(defthm hons-rassoc-equal-of-cdr-when-hons-assoc-equal-and-no-duplicates
  (implies (and (no-duplicatesp-equal (alist-vals map))
                (hons-assoc-equal key map))
           (equal (hons-rassoc-equal (cdr (hons-assoc-equal key map)) map)
                  (hons-assoc-equal key map)))
  :hints(("Goal" :in-theory (enable hons-assoc-equal
                                    hons-rassoc-equal))))


