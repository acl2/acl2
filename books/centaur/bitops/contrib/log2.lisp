; Matt Kaufmann
; Copyright (C) 2014, ForrestHunt, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This code was cut from ash-of-a-constant.lisp and put in log2.lisp, thus it
; retains the copyright from ash-of-a-constant.lisp.

(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))

(local (scatter-exponents))

(defun log2 (x)
  (declare (xargs :guard (posp x)))
  (cond ((mbe :logic (or (zp x)
                         (equal x 1))
              :exec (int= x 1))
         0)
        (t (1+ (log2 (floor x 2))))))
