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
(include-book "std/lists/append" :dir :system)

(defund z-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (if (integerp (car x))
               (<= (car x) 0)
             t)
           (z-listp (cdr x)))
    t))

(defthm z-listp-when-not-consp
  (implies (not (consp x))
           (z-listp x))
  :hints(("Goal" :in-theory (enable z-listp))))

(defthm z-listp-of-cons
  (equal (z-listp (cons a x))
         (and (zp a)
              (z-listp x)))
  :hints(("Goal" :in-theory (enable z-listp))))

(defthm z-listp-of-list-fix
  (equal (z-listp (list-fix x))
         (z-listp x))
  :hints(("Goal" :induct (len x))))

(defthm z-listp-of-append
  (equal (z-listp (append x y))
         (and (z-listp (list-fix x))
              (z-listp y)))
  :hints(("Goal" :induct (len x))))

(defthm z-listp-of-cdr-when-z-listp
  (implies (z-listp x)
           (z-listp (cdr x))))

(defthm z-listp-forward-to-zp-of-car
  (implies (z-listp x)
           (zp (car x)))
  :rule-classes :forward-chaining
  :hints(("Goal" :induct (len x))))

