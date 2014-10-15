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
(include-book "shift")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; We say log2(0) = 0, and for all other n we say log2(n) is the maximum k such
;; that 2^k <= n.  For example:
;;
;;     n           Log2(n)      2^Log2(n)
;;    ------------------------------------------------
;;     0-1         0            1
;;     2-3         1            2
;;     4-7         2            4
;;     8-15        3            8
;;     16-31       4            16
;;     ...
;;    ------------------------------------------------

(defun fast-log2 (n acc)
  (declare (xargs :guard (and (natp n)
                              (natp acc))
                  :measure (nfix n)))
  (if (or (zp n)
          (equal n 1))
      acc
    (fast-log2 (bitwise-shr n 1) (+ 1 acc))))

(definlined log2 (n)
  (declare (xargs :guard (natp n)))
  (fast-log2 n 0))

(encapsulate
 ()
 (local (defthm natp-of-fast-log2
          (implies (force (natp acc))
                   (equal (natp (fast-log2 n acc))
                          t))
          :hints(("Goal" :in-theory (enable fast-log2)))))

 (defthm natp-of-log2
   (equal (natp (log2 n))
          t)
   :hints(("Goal" :in-theory (enable log2)))))

