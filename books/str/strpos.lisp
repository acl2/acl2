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
          ((mbe :logic (zp (- (nfix yl) (nfix n)))
                :exec (= (the integer n)
                         (the integer yl)))
           nil)
          (t
           (strpos-fast (the string x)
                        (the string y)
                        (mbe :logic (+ (nfix n) 1)
                             :exec (the integer (+ (the integer n) 1)))
                        (the integer xl)
                        (the integer yl)))))

  (local (in-theory (enable strpos-fast)))

  (defthm strpos-fast-type
    (or (and (integerp (strpos-fast x y n xl yl))
             (<= 0 (strpos-fast x y n xl yl)))
        (not (strpos-fast x y n xl yl)))
    :rule-classes :type-prescription)

  (defthm strpos-fast-upper-bound-weak
    (implies (and (<= n (length y))
                  (= yl (length y)))
             (<= (strpos-fast x y n xl yl)
                 yl))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :induct (strpos-fast x y n xl yl))))

  (defthm strpos-fast-upper-bound-strong
    (implies (and (stringp x)
                  (posp yl)
                  (posp xl)
                  (= xl (length x))
                  (= yl (length y)))
             (< (strpos-fast x y n xl yl)
                yl))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :induct (strpos-fast x y n xl yl)))))


(defsection strpos
  :parents (substrings)
  :short "Locate the first occurrence of a substring."

  :long "<p>@(call strpos) searches through the string <tt>y</tt> for the first
occurrence of the substring <tt>x</tt>.  If <tt>x</tt> occurs somewhere in
<tt>y</tt>, it returns the starting index of the first occurrence.  Otherwise,
it returns <tt>nil</tt> to indicate that <tt>x</tt> never occurs in
<tt>y</tt>.</p>

<p>The function is \"efficient\" in the sense that it does not coerce its
arguments into lists, but rather traverses both strings with @(see char).  On
the other hand, it is a naive string search which operates by repeatedly
calling @(see strprefixp), rather than some better algorithm.</p>

<p>Corner case: we say that the empty string <b>is</b> a prefix of any other
string.  That is, <tt>(strpos \"\" x)</tt> is 0 for all <tt>x</tt>.</p>"

  (defund strpos (x y)
    (declare (type string x)
             (type string y))
    (strpos-fast (the string x)
                 (the string y)
                 (the integer 0)
                 (the integer (length (the string x)))
                 (the integer (length (the string y)))))

  (local (in-theory (enable strpos-fast strpos)))

  (defthm strpos-type
    (or (and (integerp (strpos x y))
             (<= 0 (strpos x y)))
        (not (strpos x y)))
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
                           (strpos-fast x y n xl yl))
                      (prefixp (coerce x 'list)
                               (nthcdr (strpos-fast x y n xl yl)
                                       (coerce y 'list))))
             :hints(("Goal" :induct (strpos-fast x y n xl yl)))))

    (defthm prefixp-of-strpos
      (implies (and (strpos x y)
                    (force (stringp x))
                    (force (stringp y)))
               (prefixp (coerce x 'list)
                        (nthcdr (strpos x y) (coerce y 'list))))))

  (encapsulate
    ()
    (local (defun my-induction (x y n m xl yl)
             (declare (xargs :measure (nfix (- (nfix yl) (nfix n)))))
             (cond ((prefixp (coerce x 'list)
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
                           (prefixp (coerce x 'list)
                                    (nthcdr m (coerce y 'list))))
                      (and (natp (strpos-fast x y n xl yl))
                           (<= (strpos-fast x y n xl yl) m)))
             :hints(("Goal"
                     :induct (my-induction x y n m xl yl)
                     :do-not '(generalize fertilize)))))

    (defthm completeness-of-strpos
      (implies (and (prefixp (coerce x 'list)
                             (nthcdr m (coerce y 'list)))
                    (force (natp m))
                    (force (stringp x))
                    (force (stringp y)))
               (and (natp (strpos x y))
                    (<= (strpos x y) m)))))

  (defthm strpos-upper-bound-weak
    (implies (and (force (stringp x))
                  (force (stringp y)))
             (<= (strpos x y)
                 (len (coerce y 'list))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm strpos-upper-bound-strong
    (implies (and (force (stringp x))
                  (force (stringp y))
                  (not (equal x ""))
                  (not (equal y "")))
             (< (strpos x y)
                (len (coerce y 'list))))
    :rule-classes ((:rewrite) (:linear))))

