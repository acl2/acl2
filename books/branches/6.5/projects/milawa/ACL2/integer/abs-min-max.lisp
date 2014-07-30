; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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

(in-package "MILAWA")
(include-book "base")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defsection iabs

  (defund iabs (a)
    (declare (xargs :guard t))
    (if (i< a 0)
        (ineg a)
      (ifix a)))

  (local (in-theory (enable integerp iabs ifix ineg i<)))

  (defthm natp-of-iabs
    (equal (natp (iabs a))
           t))

  (defthm iabs-of-ifix
    (equal (iabs (ifix a))
           (iabs a)))

  (defund fast-iabs (a)
    (declare (xargs :guard (integerp a)))
    (if (consp a)
        (cdr a)
      a))

  (defthm fast-iabs-removal
    (implies (force (integerp a))
             (equal (fast-iabs a)
                    (iabs a)))
    :hints(("Goal" :in-theory (enable fast-iabs)))))



(defsection imax

  (defund imax (a b)
    (declare (xargs :guard t))
    (if (i< a b)
        (ifix b)
      (ifix a)))

  (local (in-theory (enable imax)))

  (defthm integerp-of-imax
    (equal (integerp (imax a b))
           t))

  (defthm imax-of-ifix-left
    (equal (imax (ifix a) b)
           (imax a b)))

  (defthm imax-of-ifix-right
    (equal (imax a (ifix b))
           (imax a b)))

  (defthm |(i< (imax a b) a)|
    (equal (i< (imax a b) a)
           nil))

  (defthm |(i< (imax a b) b)|
    (equal (i< (imax a b) b)
           nil))

  (defund fast-imax (a b)
    (declare (xargs :guard (and (integerp a)
                                (integerp b))))
    (if (fast-i< a b)
        b
      a))

  (defthm fast-imax-removal
    (implies (force (and (integerp a)
                         (integerp b)))
             (equal (fast-imax a b)
                    (imax a b)))
    :hints(("Goal" :in-theory (enable fast-imax)))))



(defsection imin

  (defund imin (a b)
    (declare (xargs :guard t))
    (if (i< a b)
        (ifix a)
      (ifix b)))

  (local (in-theory (enable imin)))

  (defthm integerp-of-imin
    (equal (integerp (imin a b))
           t))

  (defthm imin-of-ifix-left
    (equal (imin (ifix a) b)
           (imin a b)))

  (defthm imin-of-ifix-right
    (equal (imin a (ifix b))
           (imin a b)))

  (defthm |(i< a (imin a b))|
    (equal (i< a (imin a b))
           nil))

  (defthm |(i< b (imin a b))|
    (equal (i< b (imin a b))
           nil))

  (defund fast-imin (a b)
    (declare (xargs :guard (and (integerp a)
                                (integerp b))))
    (if (fast-i< a b)
        a
      b))

  (defthm fast-imin-removal
    (implies (force (and (integerp a)
                         (integerp b)))
             (equal (fast-imin a b)
                    (imin a b)))
    :hints(("Goal" :in-theory (enable fast-imin)))))

