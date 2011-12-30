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
(include-book "xdoc/top" :dir :system)
(include-book "unicode/prefixp" :dir :system)
(include-book "unicode/nthcdr" :dir :system)
(local (include-book "arithmetic"))

(local (defthm prefixp-lemma-1
         (implies (and (natp xn)
                       (natp yn)
                       (< xn (len x))
                       (< yn (len y))
                       (not (equal (nth xn x) (nth yn y))))
                  (not (prefixp (nthcdr xn x) (nthcdr yn y))))
         :hints(("Goal" :in-theory (enable nthcdr nth prefixp)))))

(local (defthm prefixp-lemma-2
         (implies (and (natp xn)
                       (natp yn)
                       (< xn (len x))
                       (< yn (len y))
                       (equal (nth xn x) (nth yn y)))
                  (equal (prefixp (nthcdr xn x) (nthcdr yn y))
                         (prefixp (cdr (nthcdr xn x)) (cdr (nthcdr yn y)))))
         :hints(("Goal" :in-theory (enable prefixp nth nthcdr)))))

(defsection strprefixp-impl
  :parents (strprefixp)
  :short "Fast implementation of @(see strprefixp)."

  (defund strprefixp-impl (x y xn yn xl yl)
    (declare (type string x)
             (type string y)
             (type integer xn)
             (type integer yn)
             (type integer xl)
             (type integer yl)
             (xargs :guard (and (stringp x)
                                (stringp y)
                                (natp xn)
                                (natp yn)
                                (natp xl)
                                (natp yl)
                                (= xl (length x))
                                (= yl (length y))
                                (<= xn (length x))
                                (<= yn (length y)))
                    :measure (min (nfix (- (nfix xl) (nfix xn)))
                                  (nfix (- (nfix yl) (nfix yn))))))
    (cond ((mbe :logic (zp (- (nfix xl) (nfix xn)))
                :exec (= (the integer xn)
                         (the integer xl)))
           t)
          ((mbe :logic (zp (- (nfix yl) (nfix yn)))
                :exec (= (the integer yn)
                         (the integer yl)))
           nil)
          ((eql (the character (char x xn))
                (the character (char y yn)))
           (mbe :logic (strprefixp-impl x y
                                        (+ (nfix xn) 1)
                                        (+ (nfix yn) 1)
                                        xl yl)
                :exec  (strprefixp-impl (the string x)
                                        (the string y)
                                        (the integer (+ (the integer xn) 1))
                                        (the integer (+ (the integer yn) 1))
                                        (the integer xl)
                                        (the integer yl))))
          (t
           nil)))

  (local (in-theory (enable strprefixp-impl)))

  (defthm strprefixp-impl-elim
    (implies (and (force (stringp x))
                  (force (stringp y))
                  (force (natp xn))
                  (force (natp yn))
                  (force (= xl (length x)))
                  (force (= yl (length y)))
                  (force (<= xn xl))
                  (force (<= yn yl)))
             (equal (strprefixp-impl x y xn yn xl yl)
                    (prefixp (nthcdr xn (coerce x 'list))
                             (nthcdr yn (coerce y 'list)))))))

(defsection strprefixp
  :parents (substrings)
  :short "Case-sensitive string prefix test."
  :long "<p>@(call strprefixp) determines if the string <tt>x</tt> is a prefix
of the string <tt>y</tt>, in a case-sensitive manner.</p>

<p>Logically, this is identical to</p>

<code>
 (prefixp (coerce x 'list) (coerce y 'list))
</code>

<p>But we use a more efficient implementation which avoids coercing the
strings into character lists.</p>"

  (defun strprefixp (x y)
    (declare (type string x)
             (type string y))
    (mbe :logic (prefixp (coerce x 'list)
                         (coerce y 'list))
         :exec (strprefixp-impl (the string x)
                                (the string y)
                                (the integer 0)
                                (the integer 0)
                                (the integer (length (the string x)))
                                (the integer (length (the string y)))))))
