; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(let ((st (update-fld 3 *the-live-st*)))
  (cond ((equal (fld st) 3)
         (print "SUCCESS"))
        (t (print "FAILURE"))))
