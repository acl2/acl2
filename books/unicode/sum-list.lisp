; Processing Unicode Files with ACL2
; Copyright (C) 2005-2006 Kookamara LLC
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

(include-book "arithmetic/nat-listp" :dir :system)
(include-book "std/lists/list-fix" :dir :system)

(defund sum-list (x)
  (declare (xargs :guard (nat-listp x)))
  (if (consp x)
      (+ (car x)
         (sum-list (cdr x)))
    0))

(defthm sum-list-when-not-consp
  (implies (not (consp x))
           (equal (sum-list x)
                  0))
  :hints(("Goal" :in-theory (enable sum-list))))

(defthm sum-list-of-cons
  (equal (sum-list (cons a x))
         (+ a (sum-list x)))
  :hints(("Goal" :in-theory (enable sum-list))))

(defthm sum-list-of-list-fix
  (equal (sum-list (list-fix x))
         (sum-list x))
  :hints(("Goal" :induct (len x))))

(defthm sum-list-of-append
  (equal (sum-list (append x y))
         (+ (sum-list x)
            (sum-list y)))
  :hints(("Goal" :induct (len x))))

(defthm natp-of-sum-list-when-nat-listp
  (implies (nat-listp x)
           (and (integerp (sum-list x))
                (<= 0 (sum-list x))))
  :hints(("Goal" :induct (len x))))

(defthm natp-of-sum-list-when-nat-listp-linear
  (implies (nat-listp x)
           (<= 0 (sum-list x)))
  :rule-classes :linear)
