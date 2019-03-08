; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun ln (x)
  (if (and (real/rationalp x)
           (< 0 x))

; At one time we returned (rational (log x)) in this case.  However, that gave
; a different answer in GCL than in some other Lisps, presumably because of the
; precision.

      (let ((n (expt 10 7)))
        (/ (round (* (log 3) n))
           n))
    0))
