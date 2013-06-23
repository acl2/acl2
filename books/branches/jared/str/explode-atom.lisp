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
(include-book "digitp")
(local (include-book "std/lists/append" :dir :system))
(local (include-book "explode-nonnegative-integer"))

(defthm true-listp-of-explode-atom
  (true-listp (explode-atom x base))
  :rule-classes :type-prescription)

(defthm consp-of-explode-atom-when-integerp
  (implies (integerp n)
           (consp (explode-atom n base)))
  :rule-classes :type-prescription)

(defthm equal-of-explode-atoms-when-natps
  (implies (and (natp n)
                (natp m)
                (force (print-base-p base)))
           (equal (equal (explode-atom n base)
                         (explode-atom m base))
                  (equal n m))))

(defthm nonzeroness-of-explode-atom-when-not-zp
  (implies (and (not (zp n))
                (force (print-base-p base)))
           (not (equal (explode-atom n base) '(#\0)))))

(defthm digit-listp-of-explode-atom
  (implies (natp n)
           (str::digit-listp (explode-atom n 10))))

(defthm character-listp-of-explode-atom
  (character-listp (explode-atom x base))
  :hints(("Goal" :in-theory (disable explode-nonnegative-integer))))

; Copied from std/io/base.lisp, wherein it was added by Matt K. for princ$
; change 12/7/2012.
(defthm character-listp-explode-atom+
  (character-listp (explode-atom+ x base radix)))
