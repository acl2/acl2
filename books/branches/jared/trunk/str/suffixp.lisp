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
(include-book "strprefixp")
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "misc/assert" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable acl2::prefixp-when-equal-lengths)))

(local (defthm crock
         (implies (and (equal (len x) (len y))
                       (true-listp x)
                       (true-listp y))
                  (equal (prefixp x y)
                         (equal x y)))
         :hints(("Goal" :in-theory (enable prefixp)))))

(defsection strsuffixp
  :parents (substrings)
  :short "Case-sensitive string suffix test."

  :long "<p>@(call strsuffixp) determines if the string @('x') is a suffix of
the string @('y'), in a case-sensitive manner.</p>

<p>Logically, we ask whether @('|x| < |y|'), and whether</p>

@({
  (equal (nthcdr (- |y| |x|) (explode x))
         (explode y))
})

<p>But we use a more efficient implementation that avoids coercing the strings
into lists; basically we ask if the last @('|x|') characters of @('y') are
equal to @('x').</p>

<p>Corner case: we regard the empty string as a suffix of every other string.
That is, @('(strsuffixp \"\" x)') is always true.</p>"

  (definlined strsuffixp (x y)
    (declare (type string x y))
    (mbe :logic
         (let* ((xchars (explode x))
                (ychars (explode y))
                ;; note that using, e.g., (len (explode x)) instead of (length
                ;; x)) gives better congruence behavior
                (xlen   (len xchars))
                (ylen   (len ychars)))
           (and (<= xlen ylen)
                (equal (nthcdr (- ylen xlen) (explode y))
                       (explode x))))
         :exec
         (let* ((xlen (length x))
                (ylen (length y)))
           (and (<= xlen ylen)
                (strprefixp-impl x y 0 (- ylen xlen) xlen ylen)))))

  (local (in-theory (enable strsuffixp)))

  (local (defthm c0
           (implies (and (natp n)
                         (<= (len x) n)
                         (true-listp x))
                    (equal (nthcdr n x) nil))))

  (local (defthm c1
           (implies (true-listp x)
                    (not (nthcdr (len x) x)))))

  (defthm strsuffixp-of-empty
    (strsuffixp "" y))

  (local
   (progn
     (assert! (strsuffixp "" ""))
     (assert! (strsuffixp "" "foo"))
     (assert! (strsuffixp "o" "foo"))
     (assert! (strsuffixp "oo" "foo"))
     (assert! (not (strsuffixp "ooo" "foo")))
     (assert! (not (strsuffixp "fo" "foo")))
     (assert! (strsuffixp "foo" "foo"))))

  (defcong streqv equal (strsuffixp x y) 1)
  (defcong streqv equal (strsuffixp x y) 2))


