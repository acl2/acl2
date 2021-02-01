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

(add-io-pair (g 100 200) (mv 1000 2000))
