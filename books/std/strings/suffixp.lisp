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
(include-book "strprefixp")
(local (include-book "std/lists/nthcdr" :dir :system))
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

  (defcong streqv equal (strsuffixp x y) 1)
  (defcong streqv equal (strsuffixp x y) 2))
