; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book supports testing as explained in include-include-top.lisp.

(in-package "ACL2")

(include-book "include-include-sub")

(defun f-mid (st)
  (declare (xargs :stobjs st))
  (misc st))
