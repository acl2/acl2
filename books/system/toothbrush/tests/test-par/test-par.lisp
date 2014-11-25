; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we test ACL2(p).

(in-package "ACL2")

(defun fib (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) 0)
        ((eql n 1) 1)
        (t (#+acl2-par
            plet
            #-acl2-par
            let
            ((a (fib (- n 1)))
             (b (fib (- n 2))))
            (+ a b)))))

(defun top (n)
  (declare (xargs :guard (natp n)))
  (fib n))
