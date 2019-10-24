; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(let* ((live-st (cdr (assoc-eq 'st *user-stobj-alist*)))
       (st (my-update 3 live-st)))
  (cond ((and (equal (fld1 st) 3)
              (equal (fld2 st) 'a-changed))
         (print "SUCCESS"))
        (t (print "FAILURE"))))
