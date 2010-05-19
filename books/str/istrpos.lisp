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
(include-book "iprefixp")
(include-book "istrprefixp")
(local (include-book "arithmetic"))

(defund istrpos-impl (x y n xl yl)
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
                  :measure (nfix (- (nfix yl) (nfix n)))))
  (cond ((mbe :logic (iprefixp (coerce x 'list)
                               (nthcdr n (coerce y 'list)))
              :exec (istrprefixp-impl (the string x)
                                      (the string y)
                                      (the integer 0)
                                      (the integer n)
                                      (the integer xl)
                                      (the integer yl)))
         (mbe :logic (nfix n)
              :exec n))
        ((mbe :logic (zp (- (nfix yl) (nfix n)))
              :exec (= (the integer n)
                       (the integer yl)))
         nil)
        (t
         (istrpos-impl (the string x)
                       (the string y)
                       (mbe :logic (+ (nfix n) 1)
                            :exec (the integer (+ (the integer n) 1)))
                       (the integer xl)
                       (the integer yl)))))

(defund istrpos (x y)

  ":Doc-Section Str
  Case-insensitivly locate the first occurrence of a substring~/

  ~c[(istrpos x y)] is like ~il[strpos], but the comparisons are done in a case
  insensitive manner.  It returns NIL if x never occurs in y, or returns the index
  of the first character of the first occurrence.

  The function is \"efficient\" in the sense that it does not coerce its arguments
  into lists, but rather traverses both strings with ~c[char].  On the other hand,
  it is a naive string search which operates by repeatedly calling ~il[istrprefixp],
  rather than some better algorithm.

  The \"soundness\" and \"completness\" of strpos are established in the theorems
  ~c[iprefixp-of-istrpos] and ~c[completeness-of-istrpos].~/

  ~l[strpos], ~pl[substrp], and ~pl[isubstrp]"

  (declare (type string x)
           (type string y))

  (istrpos-impl (the string x)
                (the string y)
                (the integer 0)
                (the integer (length (the string x)))
                (the integer (length (the string y)))))

(defthm istrpos-type
  (or (and (integerp (istrpos x y))
           (<= 0 (istrpos x y)))
      (not (istrpos x y)))
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
                        (istrpos-impl x y n xl yl))
                   (iprefixp (coerce x 'list)
                                 (nthcdr (istrpos-impl x y n xl yl)
                                         (coerce y 'list))))
          :hints(("Goal"
                  :in-theory (enable istrpos-impl)
                  :induct (istrpos-impl x y n xl yl)))))

 (defthm iprefixp-of-istrpos
   (implies (and (istrpos x y)
                 (force (stringp x))
                 (force (stringp y)))
            (iprefixp (coerce x 'list)
                      (nthcdr (istrpos x y) (coerce y 'list))))
   :hints(("Goal" :in-theory (enable istrpos)))))

(encapsulate
 ()
 (local (defun my-induction (x y n m xl yl)
          (declare (xargs :measure (nfix (- (nfix yl) (nfix n)))))
          (cond ((iprefixp (coerce x 'list)
                           (nthcdr n (coerce y 'list)))
                 nil)
                ((zp (- (nfix yl) (nfix n)))
                 (list x y n m xl yl))
                (t
                 (my-induction x y
                               (+ (nfix n) 1)
                               (if (= (nfix n) (nfix m))
                                   (+ (nfix m) 1)
                                 m)
                               xl yl)))))

 (local (defthm lemma
          (implies (and (stringp x)
                        (stringp y)
                        (natp xl)
                        (natp yl)
                        (natp n)
                        (natp m)
                        (<= n m)
                        (<= n (length y))
                        (= xl (length x))
                        (= yl (length y))
                        (iprefixp (coerce x 'list)
                                  (nthcdr m (coerce y 'list))))
                   (and (natp (istrpos-impl x y n xl yl))
                        (<= (istrpos-impl x y n xl yl) m)))
          :hints(("Goal"
                  :in-theory (enable istrpos-impl)
                  :induct (my-induction x y n m xl yl)
                  :do-not '(generalize fertilize)))))

 (defthm completeness-of-istrpos
   (implies (and (iprefixp (coerce x 'list)
                           (nthcdr m (coerce y 'list)))
                 (force (natp m))
                 (force (stringp x))
                 (force (stringp y)))
            (and (natp (istrpos x y))
                 (<= (istrpos x y) m)))
   :hints(("Goal" :in-theory (enable istrpos)))))

