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
(include-book "ieqv")
(include-book "iprefixp")
(include-book "std/basic/defs" :dir :system)
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "arithmetic"))

(local (defthm iprefixp-lemma-1
         (implies (and (natp xn)
                       (natp yn)
                       (< xn (len x))
                       (< yn (len y))
                       (not (ichareqv (nth xn x) (nth yn y))))
                  (not (iprefixp (nthcdr xn x) (nthcdr yn y))))
         :hints(("Goal" :in-theory (enable nthcdr nth iprefixp)))))

(local (defthm iprefixp-lemma-2
         (implies (and (natp xn)
                       (natp yn)
                       (< xn (len x))
                       (< yn (len y))
                       (ichareqv (nth xn x) (nth yn y)))
                  (equal (iprefixp (nthcdr xn x) (nthcdr yn y))
                         (iprefixp (cdr (nthcdr xn x)) (cdr (nthcdr yn y)))))
         :hints(("Goal" :in-theory (enable iprefixp nth nthcdr)))))

(defsection istrprefixp
  :parents (substrings)
  :short "Case-insensitive string prefix test."

  :long "<p>@(call istrprefixp) determines if the string @('x') is a
case-insensitive prefix of the string @('y').</p>

<p>Logically, this is identical to</p>
@({
  (iprefixp (explode x) (explode y))
})

<p>But we use a more efficient implementation which avoids coercing the strings
to lists.</p>"

  (defund istrprefixp-impl (x y xn yn xl yl)
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
                                  (nfix (- (nfix yl) (nfix yn))))
                    :guard-hints (("Goal" :in-theory (enable ichareqv)))))
    (cond ((mbe :logic (zp (- (nfix xl) (nfix xn)))
                :exec (int= xn xl))
           t)
          ((mbe :logic (zp (- (nfix yl) (nfix yn)))
                :exec (int= yn yl))
           nil)
          ((ichareqv (char x xn) (char y yn))
           (istrprefixp-impl x y
                             (+ 1 (lnfix xn))
                             (+ 1 (lnfix yn))
                             xl yl))
          (t
           nil)))

  (definline istrprefixp (x y)
    (declare (type string x)
             (type string y)
             (xargs :verify-guards nil))
    (mbe :logic (iprefixp (explode x)
                          (explode y))
         :exec (istrprefixp-impl (the string x)
                                 (the string y)
                                 (the integer 0)
                                 (the integer 0)
                                 (the integer (length (the string x)))
                                 (the integer (length (the string y))))))

  (defthm istrprefixp-impl-elim
    (implies (and (force (stringp x))
                  (force (stringp y))
                  (force (natp xn))
                  (force (natp yn))
                  (force (= xl (length x)))
                  (force (= yl (length y)))
                  (force (<= xn xl))
                  (force (<= yn yl)))
             (equal (istrprefixp-impl x y xn yn xl yl)
                    (iprefixp (nthcdr xn (coerce x 'list))
                              (nthcdr yn (coerce y 'list)))))
    :hints(("Goal" :in-theory (enable istrprefixp-impl))))

  (verify-guards istrprefixp$inline)

  (defcong istreqv equal (istrprefixp x y) 1)
  (defcong istreqv equal (istrprefixp x y) 2))


