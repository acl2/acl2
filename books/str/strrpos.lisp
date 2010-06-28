; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
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

(in-package "STR")
(include-book "strprefixp")
(local (include-book "arithmetic"))

(defund strrpos-fast (x y n xl yl)
  (declare (type string x)
           (type string y)
           (type integer n)
           (type integer xl)
           (type integer yl)
           (xargs :guard (and (stringp x)
                              (stringp y)
                              (natp xl)
                              (natp yl)
                              (natp n)
                              (<= n (length y))
                              (= xl (length x))
                              (= yl (length y)))
                  :measure (nfix n)))
  ;; N goes from YL to 0.
  (cond ((mbe :logic (prefixp (coerce x 'list)
                              (nthcdr n (coerce y 'list)))
              :exec (strprefixp-impl (the string x)
                                     (the string y)
                                     (the integer 0)
                                     (the integer n)
                                     (the integer xl)
                                     (the integer yl)))
         (mbe :logic (nfix n)
              :exec n))
        ((mbe :logic (zp n)
              :exec (= (the integer n) (the integer 0)))
         nil)
        (t
         (strrpos-fast (the string x)
                       (the string y)
                       (mbe :logic (- (nfix n) 1)
                            :exec (the integer (- (the integer n) 1)))
                       (the integer xl)
                       (the integer yl)))))

(defthm strpos-fast-type
  (or (and (integerp (strrpos-fast x y n xl yl))
           (<= 0 (strrpos-fast x y n xl yl)))
      (not (strrpos-fast x y n xl yl)))
  :rule-classes :type-prescription)

(defthm strpos-fast-upper-bound
  (implies (force (natp n))
           (<= (strrpos-fast x y n xl yl) n))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable strrpos-fast))))

(defthm strrpos-fast-when-empty
  (implies (and (not (consp (coerce x 'list)))
                (equal xl (length x))
                (equal yl (length y))
                (natp n))
           (equal (STRRPOS-FAST X Y n xl yl)
                  n))
  :hints(("Goal" :in-theory (enable strrpos-fast))))



(defund strrpos (x y)

  ":Doc-Section Str
  Locate the last occurrence of a substring~/

  ~c[(strrpos x y)] searches through the string y for the last occurrence of the
  substring x.  It returns NIL if x never occurs in y, or returns the index of
  the first character of the last occurrence.

  The function is \"efficient\" in the sense that it does not coerce its arguments
  into lists, but rather traverses both strings with ~c[char].  On the other hand,
  it is a naive string search which operates by repeatedly calling ~il[strprefixp],
  rather than some better algorithm.

  The \"soundness\" and \"completness\" of strpos are established in the theorems
  ~c[prefixp-of-strrpos] and ~c[completeness-of-strrpos].~/~/"

  (declare (type string x)
           (type string y))
  (let ((yl (length (the string y))))
    (declare (type integer yl))
    (strrpos-fast (the string x)
                  (the string y)
                  yl
                  (the integer (length (the string x)))
                  yl)))

(defthm strrpos-type
  (or (and (integerp (strrpos x y))
           (<= 0 (strrpos x y)))
      (not (strrpos x y)))
  :rule-classes :type-prescription)



(encapsulate
 ()
 (local (defthm lemma
          (implies (and (stringp x)
                        (stringp y)
                        (natp xl)
                        (natp yl)
                        (natp n)
                        (<= n (length y))
                        (= xl (length x))
                        (= yl (length y))
                        (strrpos-fast x y n xl yl))
                   (prefixp (coerce x 'list)
                            (nthcdr (strrpos-fast x y n xl yl)
                                    (coerce y 'list))))
          :hints(("Goal"
                  :in-theory (enable strrpos-fast)
                  :induct (strrpos-fast x y n xl yl)))))

 (defthm prefixp-of-strrpos
   (implies (and (strrpos x y)
                 (force (stringp x))
                 (force (stringp y)))
            (prefixp (coerce x 'list)
                     (nthcdr (strrpos x y) (coerce y 'list))))
   :hints(("Goal" :in-theory (enable strrpos)))))


(encapsulate
 ()
 (local (defun my-induction (x y n m xl yl)
          (declare (xargs :measure (nfix n)))
          (cond ((prefixp (coerce x 'list)
                          (nthcdr n (coerce y 'list)))
                 nil)
                ((zp n)
                 (list x y n m xl yl))
                (t
                 (my-induction x y
                               (- (nfix n) 1)
                               (if (= (nfix n) (nfix m))
                                   (- (nfix m) 1)
                                 m)
                               xl yl)))))

 (local (defthm lemma
          (implies (and (stringp x)
                        (stringp y)
                        (natp xl)
                        (natp yl)
                        (natp n)
                        (natp m)
                        (>= n m)
                        (<= n (length y))
                        (= xl (length x))
                        (= yl (length y))
                        (prefixp (coerce x 'list)
                                 (nthcdr m (coerce y 'list))))
                   (and (natp (strrpos-fast x y n xl yl))
                        (>= (strrpos-fast x y n xl yl) m)))
          :hints(("Goal"
                  :in-theory (enable strrpos-fast)
                  :induct (my-induction x y n m xl yl)
                  :do-not '(generalize fertilize)))))

 (defthm completeness-of-strrpos
   (implies (and (prefixp (coerce x 'list)
                          (nthcdr m (coerce y 'list)))
                 (< m (len y))
                 (force (natp m))
                 (force (stringp x))
                 (force (stringp y)))
            (and (natp (strrpos x y))
                 (>= (strrpos x y) m)))
   :hints(("Goal" :in-theory (enable strrpos)))))
