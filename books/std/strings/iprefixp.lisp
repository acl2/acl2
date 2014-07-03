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
(include-book "ieqv")
(include-book "std/lists/prefixp" :dir :system)
(local (include-book "arithmetic"))

(defsection iprefixp
  :parents (substrings)
  :short "Case-insensitive character-list prefix test."
  :long "<p>@(call iprefixp) determines whether one character list is a prefix
of another, where each character is tested using @(see ichareqv).</p>"

  (defund iprefixp (x y)
    (declare (xargs :guard (and (character-listp x)
                                (character-listp y))))
    (if (consp x)
        (and (consp y)
             (ichareqv (car x) (car y))
             (iprefixp (cdr x) (cdr y)))
      t))

  (local (in-theory (enable iprefixp)))

  (defthm iprefixp-when-not-consp-left
    (implies (not (consp x))
             (iprefixp x y)))

  (defthm iprefixp-of-cons-left
    (equal (iprefixp (cons a x) y)
           (and (consp y)
                (ichareqv a (car y))
                (iprefixp x (cdr y)))))

  (defthm iprefixp-when-not-consp-right
    (implies (not (consp y))
             (equal (iprefixp x y)
                    (not (consp x))))
    :hints(("Goal" :induct (len x))))

  (defthm iprefixp-of-cons-right
    (equal (iprefixp x (cons a y))
           (if (consp x)
               (and (ichareqv (car x) a)
                    (iprefixp (cdr x) y))
             t)))

  (defthm iprefixp-of-list-fix-left
    (equal (iprefixp (list-fix x) y)
           (iprefixp x y)))

  (defthm iprefixp-of-list-fix-right
    (equal (iprefixp x (list-fix y))
           (iprefixp x y)))

  (defcong icharlisteqv equal (iprefixp x y) 1)
  (defcong icharlisteqv equal (iprefixp x y) 2)

  (defthm iprefixp-when-prefixp
    (implies (prefixp x y) (iprefixp x y))))
