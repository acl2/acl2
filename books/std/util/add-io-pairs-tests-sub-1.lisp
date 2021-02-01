; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book supports testing of the use of include-book with add-io-pairs.  See
; add-io-pairs-tests.lisp.

(in-package "ACL2")

(include-book "add-io-pairs")

; From add-io-pairs-tests.lisp:
(defun g (x y)
  (declare (xargs :guard (and (natp x) (natp y))))
  (mv (non-exec (* 10 x)) (* 10 y)))

; Also in add-io-pairs-tests-sub-2.lisp:
(defun g2 (x)
  (declare (xargs :guard (natp x)))
  (non-exec (* 100 x)))

(add-io-pair (g 100 7) (mv 1000 70))
(add-io-pair (g 700 7) (mv 7000 70)) ; same as in *-sub-2.lisp
(add-io-pair (g2 7) 700)
