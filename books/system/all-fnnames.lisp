; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(verify-termination all-fnnames1
  (declare (xargs :verify-guards nil)))

(defthm true-listp-all-fnnames
  (implies (true-listp acc)
           (true-listp (all-fnnames1 flg x acc))))

(verify-guards all-fnnames1)
