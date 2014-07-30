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
(include-book "alist-fix")

(defsection hons-remove-assoc
  :parents (std/alists)
  :short "Remove a particular key from a \"modern\" alist."
  :long "<p>The @('hons-') here just refers to our observation of the
\"modern\" atom-skipping convention as in @(see hons-assoc-equal), etc.  There
is nothing fast or hons-specific here.</p>"

  (defund hons-remove-assoc (k x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (if (and (consp (car x))
               (not (equal k (caar x))))
          (cons (car x) (hons-remove-assoc k (cdr x)))
        (hons-remove-assoc k (cdr x)))))

  (local (in-theory (enable hons-remove-assoc)))

  (defthm hons-remove-assoc-of-cons
    (equal (hons-remove-assoc k (cons x y))
           (if (and (consp x)
                    (not (equal (car x) k)))
               (cons x (hons-remove-assoc k y))
             (hons-remove-assoc k y))))

  (defthm hons-remove-assoc-of-atom
    (implies (not (consp x))
             (equal (hons-remove-assoc k x) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm hons-remove-assoc-commutes
    (equal (hons-remove-assoc k (hons-remove-assoc j x))
           (hons-remove-assoc j (hons-remove-assoc k x)))
    :hints(("Goal" :in-theory (enable hons-remove-assoc)))
    :rule-classes ((:rewrite :loop-stopper ((j k)))))

  (defthm hons-assoc-equal-remove-assoc
    (equal (hons-assoc-equal k (hons-remove-assoc j x))
           (and (not (equal k j))
                (hons-assoc-equal k x)))
    :hints(("Goal" :in-theory (enable hons-remove-assoc))))

  (defthm hons-remove-assoc-of-fast-alist-fork
    (equal (hons-remove-assoc k (fast-alist-fork x y))
           (fast-alist-fork (hons-remove-assoc k x) (hons-remove-assoc k y)))
    :hints(("Goal" :in-theory (enable hons-remove-assoc)
            :induct (fast-alist-fork x y))))

  (defthm hons-remove-assoc-of-append
    (equal (hons-remove-assoc k (append x y))
           (append (hons-remove-assoc k x)
                   (hons-remove-assoc k y))))

  (defthm hons-remove-assoc-when-not-hons-assoc-equal
    (implies (not (hons-assoc-equal k x))
             (equal (hons-remove-assoc k x)
                    (alist-fix x))))

  (defthm alistp-of-hons-remove-assoc
    (alistp (hons-remove-assoc k x)))

  (defthm hons-remove-assoc-of-alist-fix
    (equal (hons-remove-assoc k (alist-fix x))
           (hons-remove-assoc k x))))
