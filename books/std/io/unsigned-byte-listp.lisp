;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(set-verify-guards-eagerness 2)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/lists/take" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)

;; (in-theory (disable unsigned-byte-p))

;; BOZO consider switching this whole book to just be a deflist
;; BOZO probably relocate this book to std/typed-lists

(local (in-theory (disable unsigned-byte-p)))

(defund unsigned-byte-listp (n x)
  (if (atom x)
      (null x)
    (and (unsigned-byte-p n (car x))
         (unsigned-byte-listp n (cdr x)))))

(defthm unsigned-byte-listp-when-not-consp
  (implies (not (consp x))
           (equal (unsigned-byte-listp n x)
                  (not x)))
  :hints(("Goal" :in-theory (enable unsigned-byte-listp))))

(defthm unsigned-byte-listp-of-cons
  (equal (unsigned-byte-listp n (cons a x))
         (and (unsigned-byte-p n a)
              (unsigned-byte-listp n x)))
  :hints(("Goal" :in-theory (enable unsigned-byte-listp))))

(defthm unsigned-byte-p-of-car-when-unsigned-byte-listp
  (implies (unsigned-byte-listp bytes x)
           (equal (unsigned-byte-p bytes (car x))
                  (consp x)))
  :rule-classes (:rewrite :forward-chaining))

(defthm nat-listp-when-unsigned-byte-listp
  (implies (unsigned-byte-listp bytes x)
           (nat-listp x))
  :hints(("Goal" :induct (len x))))

(defthm true-listp-when-unsigned-byte-listp
  (implies (unsigned-byte-listp bytes x)
           (true-listp x))
  :hints(("Goal" :induct (len x))))

(defthm unsigned-byte-listp-of-append
  (equal (unsigned-byte-listp bytes (append x y))
         (and (unsigned-byte-listp bytes (list-fix x))
              (unsigned-byte-listp bytes y)))
  :hints(("Goal" :induct (len x))))

(defthm unsigned-byte-listp-of-list-fix-when-unsigned-byte-listp
  (implies (unsigned-byte-listp bytes x)
           (unsigned-byte-listp bytes (list-fix x))))

(defthm unsigned-byte-listp-of-repeat
  (equal (unsigned-byte-listp bytes (repeat x n))
         (or (zp n)
             (unsigned-byte-p bytes x)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm unsigned-byte-listp-of-take
  (implies (unsigned-byte-listp bytes x)
           (equal (unsigned-byte-listp bytes (take n x))
                  (or (zp n)
                      (<= n (len x))))))

(defthm unsigned-byte-listp-of-take-past-length
  (implies (and (natp k)
                (< (len x) k))
           (not (unsigned-byte-listp bytes (take k x)))))

(defthm unsigned-byte-listp-of-nthcdr
  (implies (unsigned-byte-listp bytes x)
           (unsigned-byte-listp bytes (nthcdr n x))))

(defthm unsigned-byte-listp-when-take-and-nthcdr
  (implies (and (unsigned-byte-listp bytes (take n x))
                (unsigned-byte-listp bytes (nthcdr n x)))
           (unsigned-byte-listp bytes x)))

