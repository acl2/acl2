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
(include-book "base10-digit-charp")
(local (include-book "explode-nonnegative-integer"))

(defthm equal-of-explode-atoms-when-natps
  (implies (and (natp n)
                (natp m))
           (equal (equal (explode-atom n 10)
                         (explode-atom m 10))
                  (equal n m))))

(defthm nonzeroness-of-explode-atom-when-not-zp
  (implies (not (zp n))
           (not (equal (explode-atom n 10) '(#\0)))))
  
(defthm base10-digit-char-listp-of-explode-atom
  (implies (natp n)
           (base10-digit-char-listp (explode-atom n 10))))

(defthm character-listp-of-explode-atom
  (character-listp (explode-atom x 10))
  :hints(("Goal" :in-theory (disable explode-nonnegative-integer))))

(local (defthm true-listp-when-character-listp
         (implies (character-listp x)
                  (true-listp x))))

(defthm true-listp-of-explode-atom
  (true-listp (explode-atom x 10))
  :hints(("Goal" :in-theory (disable explode-atom))))

(defthm consp-of-explode-atom-when-natp
  (implies (and (integerp n)
                (<= 0 n))
           (consp (explode-atom n 10)))
    :rule-classes :type-prescription)
