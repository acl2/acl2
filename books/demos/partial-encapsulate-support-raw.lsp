; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun ln (x)
  (if (and (real/rationalp x)
           (< 0 x))
      (rational (log x))
    0))
