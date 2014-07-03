; Len lemmas
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "ACL2")
(include-book "abstract")
(local (include-book "arithmetic/top" :dir :system))

(defsection std/lists/len
  :parents (std/lists len)
  :short "Lemmas about @(see len) available in the @(see std/lists) library."

  (defthm len-when-atom
    (implies (atom x)
             (equal (len x)
                    0)))

  (defthm len-of-cons
    (equal (len (cons a x))
           (+ 1 (len x))))

  (defthm |(equal 0 (len x))|
    (equal (equal 0 (len x))
           (atom x)))

  (defthm |(< 0 (len x))|
    (equal (< 0 (len x))
           (consp x)))

  (defthm consp-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp x)
                    (< 0 n))))

  (defthm consp-of-cdr-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp (cdr x))
                    (< 1 n)))
    :hints(("Goal" :expand ((len x)
                            (len (cdr x))))))

  (defthm consp-of-cddr-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp (cddr x))
                    (< 2 n)))
    :hints(("Goal" :expand ((len x)
                            (len (cdr x))
                            (len (cddr x))))))

  (defthm consp-of-cdddr-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp (cdddr x))
                    (< 3 n)))
    :hints(("Goal" :expand ((len x)
                            (len (cdr x))
                            (len (cddr x))
                            (len (cdddr x))))))

  (def-projection-rule len-of-elementlist-projection
    (equal (len (elementlist-projection x))
           (len x))))

