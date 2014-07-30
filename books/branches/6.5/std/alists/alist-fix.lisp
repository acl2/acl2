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
; Original authors: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defsection alist-fix
  :parents (std/alists)
  :short "Basic fixing function for \"modern\" alists that respects the
behavior of @(see hons-assoc-equal)."

  (defund alist-fix (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (if (consp (car x))
          (cons (car x) (alist-fix (cdr x)))
        (alist-fix (cdr x)))))

  (local (in-theory (enable alist-fix)))

  (defthm alistp-of-alist-fix
    (alistp (alist-fix x)))

  (defthm alist-fix-when-alistp
    (implies (alistp x)
             (equal (alist-fix x) x)))

  (defthm hons-assoc-equal-of-alist-fix
    (equal (hons-assoc-equal k (alist-fix x))
           (hons-assoc-equal k x)))

  (defthm alist-fix-of-cons
    (equal (alist-fix (cons a b))
           (if (consp a)
               (cons a (alist-fix b))
             (alist-fix b))))

  (defthm alist-fix-of-atom
    (implies (not (consp x))
             (equal (alist-fix x) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))



