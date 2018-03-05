; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "misc/definline" :dir :system)
(include-book "strprefixp")
(include-book "std/lists/sublistp" :dir :system)
(include-book "std/basic/defs" :dir :system)
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

