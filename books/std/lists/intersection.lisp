; Intersection$ Lemmas
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
(include-book "sets")

(in-theory (disable intersection$))
(local (in-theory (enable intersection$)))

(defthm intersection$-when-atom-left
  (implies (atom x)
           (equal (intersection$ x y)
                  nil)))

(defthm intersection$-when-atom-right
  (implies (atom y)
           (equal (intersection$ x y)
                  nil)))

(defthm intersection$-of-cons-left
  (equal (intersection$ (cons a x) y)
         (if (member a y)
             (cons a (intersection$ x y))
           (intersection$ x y))))

(defthm intersection$-of-cons-right-under-set-equiv
  (set-equiv (intersection$ x (cons a y))
             (if (member a x)
                 (cons a (intersection$ x y))
               (intersection$ x y)))
  :hints(("Goal" :in-theory (enable set-equiv))))

(defthm len-of-intersection$-upper-bound
  ;; There is no analogous rule for -right, because, e.g., X could have multiple
  ;; copies of some member in Y, and if so we end up reproducing them.  Consider
  ;; for instance (intersection$ '(a a a) '(a)) ==> '(a a a).
  (<= (len (intersection$ x y))
      (len x))
  :rule-classes ((:rewrite) (:linear)))

(defthm consp-of-intersection$
  (equal (consp (intersection$ x y))
         (intersectp x y))
  :hints(("Goal" :in-theory (enable intersectp))))

(defthm intersection$-under-iff
  (iff (intersection$ x y)
       (intersectp x y))
  :hints(("Goal" :in-theory (enable intersectp))))

