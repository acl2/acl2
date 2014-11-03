; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defstobj st fld)

(defun top (st)
  (declare (xargs :stobjs st))
  (update-fld 3 st))
