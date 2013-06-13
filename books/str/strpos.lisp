; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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
(include-book "misc/definline" :dir :system)
(include-book "strprefixp")
(include-book "std/lists/sublistp" :dir :system)
(local (include-book "arithmetic"))

(defsection strpos-fast
  :parents (strpos)
  :short "Fast implementation of @(see strpos)."

  (defund strpos-fast (x y n xl yl)
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
    (cond ((mbe :logic (prefixp (explode x)
                                (nthcdr n (explode y)))
                :exec (strprefixp-impl (the string x)
                                       (the string y)
                                       (the integer 0)
                                       (the integer n)
                                       (the integer xl)
                                       (the integer yl)))
           (lnfix n))
          ((mbe :logic (zp (- (nfix yl) (nfix n)))
                :exec (int= n yl))
           nil)
          (t
           (strpos-fast (the string x)
                        (the string y)
                        (+ 1 (lnfix n))
                        (the integer xl)
                        (the integer yl)))))

  (local (in-theory (enable strpos-fast)))

  (local (defthm l0
           (implies (sublistp x (cdr y))
                    (sublistp x y))
           :hints(("Goal" :in-theory (enable sublistp)))))

  (defthm strpos-fast-removal
    (implies (and (force (stringp x))
                  (force (stringp y))
                  (force (natp n))
                  (force (<= n (length y)))
                  (force (equal xl (length x)))
                  (force (equal yl (length y))))
             (equal (strpos-fast x y n xl yl)
                    (let ((idx (listpos (explode x)
                                        (nthcdr n (explode y)))))
                      (and idx
                           (+ n idx)))))
    :hints(("Goal"
            :induct (strpos-fast x y n xl yl)
            :do-not '(generalize fertilize eliminate-destructors)
            :do-not-induct t
            :in-theory (enable strpos-fast listpos)))))


(defsection strpos
  :parents (substrings)
  :short "Locate the first occurrence of a substring."

  :long "<p>@(call strpos) searches through the string @('y') for the first
occurrence of the substring @('x').  If @('x') occurs somewhere in @('y'), it
returns the starting index of the first occurrence.  Otherwise, it returns
@('nil') to indicate that @('x') never occurs in @('y').</p>

<p>The function is \"efficient\" in the sense that it does not coerce its
arguments into lists, but rather traverses both strings with @(see char).  On
the other hand, it is a naive string search which operates by repeatedly
calling @(see strprefixp), rather than some better algorithm.</p>

<p>Corner case: we say that the empty string <b>is</b> a prefix of any other
string.  That is, @('(strpos \"\" x)') is 0 for all @('x').</p>"

  (definline strpos (x y)
    (declare (type string x y))
    (mbe :logic
         (listpos (explode x)
                  (explode y))
         :exec
         (strpos-fast (the string x)
                      (the string y)
                      (the integer 0)
                      (the integer (length (the string x)))
                      (the integer (length (the string y))))))

  (defcong streqv equal (strpos x y) 1)
  (defcong streqv equal (strpos x y) 2))

