; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(cond ((and (equal (len-test (make-list 1000)) 999)
            (equal (len-test 10) 22))
       (print "SUCCESS"))
      (t (print "FAILURE")))
