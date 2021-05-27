; Standard Association Lists Library
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "../lists/list-defuns")
(local (include-book "../lists/take"))
(local (in-theory (enable alistp)))

(defsection std/alists/alistp
  :parents (std/alists alistp)
  :short "Lemmas about @(see alistp) available in the @(see std/alists)
library."

  :long "<p>Note that \"modern\" alist functions do not have @('alistp') guards
and that theorems about them typically do not need any @('alistp') hypotheses.
Accordingly, you may not really need to reason about @('alistp') at all.</p>"

  (defthm alistp-when-atom
    (implies (atom x)
             (equal (alistp x)
                    (not x))))

  (defthm alistp-of-cons
    (equal (alistp (cons a x))
           (and (consp a)
                (alistp x))))

  (defthm true-listp-when-alistp
    (implies (alistp x)
             (true-listp x))
    :rule-classes :compound-recognizer)

  (defthmd true-listp-when-alistp-rewrite
    (implies (alistp x)
             (true-listp x)))

  (defthm alistp-of-append
    (equal (alistp (append x y))
           (and (alistp (list-fix x))
                (alistp y)))
    :hints(("Goal" :in-theory (enable list-fix))))

  (defthm alistp-of-revappend
    (equal (alistp (revappend x y))
           (and (alistp (list-fix x))
                (alistp y)))
    :hints(("Goal" :in-theory (enable list-fix))))

  (local (defthm list-fix-when-true-listp
           (implies (true-listp x) (equal (list-fix x) x))
           :hints(("Goal" :in-theory (enable list-fix)))))

  (defthm alistp-of-rev
    (equal (alistp (rev x))
           (alistp (list-fix x)))
    :hints(("Goal"
            :in-theory (enable rev list-fix)
            :induct (len x))))

  (defthm alistp-of-reverse
    (equal (alistp (reverse x))
           (and (not (stringp x))
                (alistp (list-fix x))))
    :hints(("Goal"
            :in-theory (enable list-fix)
            :induct (len x))))

  (defthm alistp-of-cdr
    (implies (alistp x)
             (alistp (cdr x))))

  (defthm consp-of-car-when-alistp
    (implies (alistp x)
             (equal (consp (car x))
                    (if x t nil))))

  (defthm alistp-of-member
    (implies (alistp x)
             (alistp (member a x))))

  (defthm alistp-of-repeat
    (equal (alistp (repeat n x))
           (or (zp n)
               (consp x)))
    :hints(("Goal" :in-theory (enable repeat))))

  (defthm alistp-of-take
    (implies (alistp x)
             (equal (alistp (take n x))
                    (<= (nfix n) (len x))))
    :hints(("Goal" :in-theory (enable take))))

  (defthm alistp-of-nthcdr
    (implies (alistp x)
             (alistp (nthcdr n x))))

  (defthm alistp-of-remove1-assoc-equal
    (implies (alistp x)
             (alistp (remove1-assoc-equal key x))))

  (defthm alistp-of-pairlis$
    (alistp (pairlis$ x y))))
