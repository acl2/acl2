; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(defun f1 (x)
  (cons x x))

(defconst *c*
  (expt 2 3))

(defthm f1-*c*-val
  (equal (f1 *c*) '(8 . 8)))
