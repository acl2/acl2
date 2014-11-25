; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(cond ((eql (fib 10) 55)
       (format t
               "SUCCESS with~a #+acl2-par"
               #+acl2-par ""
               #-acl2-par "OUT"))
      (t (print "FAILURE")))
