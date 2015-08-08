; Last Lemmas
; Copyright (C) 2013 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "list-defuns")
(include-book "abstract")
(local (include-book "list-fix"))
(local (include-book "append"))
(local (include-book "rev"))

(defsection std/lists/last
  :parents (std/lists last)
  :short "Lemmas about @(see last) available in the @(see std/lists) library."

  (defthm last-when-atom
    (implies (atom x)
             (equal (last x)
                    x)))

  (defthm last-when-atom-of-cdr
    (implies (atom (cdr x))
             (equal (last x)
                    x)))

  (defthm last-of-cons
    (equal (last (cons a x))
           (if (consp x)
               (last x)
             (cons a x))))

  (defthm consp-of-last
    (equal (consp (last l))
           (consp l)))

  (defthm true-listp-of-last
    (equal (true-listp (last l))
           (true-listp l)))

  (defthm last-of-list-fix
    (equal (last (list-fix x))
           (list-fix (last x))))

  (defthm len-of-last
    (equal (len (last l))
           (if (consp l)
               1
             0)))

  (defthm upper-bound-of-len-of-last
    (< (len (last x)) 2)
    :rule-classes :linear)

  (defthm member-of-car-of-last
    (iff (member (car (last x)) x)
         (if (consp x)
             t
           nil)))

  (defsection subsetp-of-last

    (local (defthm l0
             (implies (subsetp-equal a x)
                      (subsetp-equal a (cons b x)))))

    (defthm subsetp-of-last
      ;; possibly good for forward chaining?
      (subsetp (last x) x)))

  (defthm last-of-append
    (equal (last (append x y))
           (if (consp y)
               (last y)
             (append (last x) y))))

  (defthm last-of-rev
    (equal (last (rev x))
           (if (consp x)
               (list (car x))
             nil)))

  (defthm last-of-revappend
    (equal (last (revappend x y))
           (cond ((consp y)
                  (last y))
                 ((consp x)
                  (cons (car x) y))
                 (t
                  y))))

  (def-listp-rule element-list-p-of-last
    (implies (element-list-p (double-rewrite x))
             (element-list-p (last x)))))

