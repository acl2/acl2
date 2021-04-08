; Mixed rules about lists of rationals
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: See also numeric-lists.lisp

(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "kestrel/typed-lists-light/all-rationalp" :dir :system)
(include-book "kestrel/utilities/polarity" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "kestrel/typed-lists-light/all-less-than-or-equal" :dir :system)

;move
(defthm <-of-maxelem-when-all-<-cheap
  (implies (and (all-< nodenums bound)
                (consp nodenums))
           (< (maxelem nodenums) bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :hints (("Goal" :in-theory (enable all-< maxelem))))

;use polarities
(local
 (defthm tighten
  (implies (and (integerp x)
                (integerp y))
           (equal (< y (+ 1 x))
                  (<= y x)))))

(defthm <-of-maxelem-when-all-<
  (implies (and (all-< items x)
                (consp items))
           (< (maxelem items) x))
  :hints (("Goal" :in-theory (enable maxelem))))

(defthm maxelem-bound-when-all-<
  (implies (and (all-< items x)
                (all-integerp items)
                (integerp x)
                (consp items))
           (NOT (< (+ -1 x)
                   (MAXELEM items))))
  :hints (("Goal" :in-theory (enable maxelem))))

;improve?
(defthm car-bound-when-all-<
  (implies (and (all-< items x)
                (all-integerp items)
                (integerp x)
                (consp items))
           (NOT (< (+ -1 x) (car items)))))

(defthm not-<-of-maxelem-when-all-<
  (implies (and (all-< items bound)
                (consp items))
           (not (< bound (maxelem items))))
  :hints (("Goal" :in-theory (enable maxelem all-<))))

(defthm not-<-of-maxelem-when-all-<-2
  (implies (and (all-< items (+ 1 bound))
                (integerp bound)
                (all-integerp items)
                (consp items))
           (not (< bound (maxelem items))))
  :hints (("Goal" :in-theory (enable maxelem all-<))))

(defthm not-<-of-maxelem-and--1
  (implies (and (all-natp x)
                (consp x))
           (not (< (maxelem x) -1)))
  :hints (("Goal" :in-theory (enable maxelem all-<))))

(defthm <-of-+-of-1-strengthen
  (implies (and (syntaxp (want-to-strengthen (< x (+ 1 y))))
                (integerp x)
                (integerp y))
           (equal (< x (+ 1 y))
                  (<= x y))))

(defthmd <-of-+-of-1-strengthen-2
  (implies (and (integerp x)
                (integerp y))
           (equal (< x (+ 1 y))
                  (<= x y))))

(defthm integer-listp-when-all-natp
  (implies (all-natp x)
           (equal (integer-listp x)
                  (true-listp x)))
  :hints (("Goal" :in-theory (enable all-natp integer-listp))))

(defthm not-<-of-+-1-and-car-when-all-<
  (implies (and (all-< items bound2) ;free var
                (<= bound2 bound)
                (integerp bound)
                (integerp bound2)
                (integerp (car items))
                (consp items))
           (not (< bound (+ 1 (car items)))))
  :hints (("Goal" :in-theory (enable all-<))))

;;;
;;; all-<=
;;;

(defthmd not-negative-when-all-<=-and-all-natp
  (implies (and  (consp indices)
                 (all-natp indices)
                 (all-<= indices top-nodenum-to-check))
           (<= 0 top-nodenum-to-check))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable all-<=))))

(defthm all-<=-of-one-less
  (implies (and (all-< vals n)
                (integerp n)
                (all-integerp vals)
                )
           (all-<= vals (+ -1 n)))
  :hints (("Goal" :in-theory (enable all-< all-<=))))

(defthmd all-rationalp-when-all-natp
  (implies (all-natp acc)
           (all-rationalp acc))
  :hints (("Goal" :in-theory (enable all-natp))))

(defthmd all-rationalp-when-nat-listp
  (implies (nat-listp acc)
           (all-rationalp acc))
  :hints (("Goal" :in-theory (enable all-natp))))

(defthm natp-of-maxelem
  (implies (and (all-natp items)
                (consp items))
           (natp (maxelem items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable all-natp maxelem))))
